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
v___x_612_ = lean_st_ref_put(v___y_571_, v___x_611_);
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
lean_ctor_set(v___x_636_, 0, v___y_633_);
lean_ctor_set(v___x_636_, 1, v___y_635_);
lean_inc(v___y_628_);
v___x_637_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v___y_628_, v___x_636_, v___y_634_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_639_; lean_object* v_toGoalState_640_; lean_object* v_clean_641_; lean_object* v_fst_642_; lean_object* v_snd_643_; lean_object* v_mvarId_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_687_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
lean_dec_ref_known(v___x_637_, 1);
v___x_639_ = lean_st_ref_take(v___y_634_);
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
v___x_673_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_next_669_, v___y_628_, v_snd_643_);
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
v___x_680_ = lean_st_ref_put(v___y_634_, v___x_679_);
v_name_570_ = v_fst_642_;
v___y_571_ = v___y_634_;
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
lean_dec(v___y_628_);
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
v___y_623_ = v___y_705_;
v___y_624_ = v___y_708_;
v___y_625_ = v___y_700_;
v___y_626_ = v___y_702_;
v___y_627_ = v___y_704_;
v___y_628_ = v_a_715_;
v___y_629_ = v___y_701_;
v___y_630_ = v___y_707_;
v___y_631_ = v___y_706_;
v___y_632_ = v___y_703_;
v___y_633_ = v_name_698_;
v___y_634_ = v___y_699_;
v___y_635_ = v_val_721_;
goto v___jp_622_;
}
else
{
lean_object* v___x_722_; 
lean_dec(v___x_720_);
v___x_722_ = lean_unsigned_to_nat(1u);
v___y_623_ = v___y_705_;
v___y_624_ = v___y_708_;
v___y_625_ = v___y_700_;
v___y_626_ = v___y_702_;
v___y_627_ = v___y_704_;
v___y_628_ = v_a_715_;
v___y_629_ = v___y_701_;
v___y_630_ = v___y_707_;
v___y_631_ = v___y_706_;
v___y_632_ = v___y_703_;
v___y_633_ = v_name_698_;
v___y_634_ = v___y_699_;
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
v___x_1046_ = lean_st_ref_put(v___y_1018_, v___x_1045_);
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
size_t v_x_195401__boxed_1610_; size_t v_x_195402__boxed_1611_; lean_object* v_res_1612_; 
v_x_195401__boxed_1610_ = lean_unbox_usize(v_x_1606_);
lean_dec(v_x_1606_);
v_x_195402__boxed_1611_ = lean_unbox_usize(v_x_1607_);
lean_dec(v_x_1607_);
v_res_1612_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_1605_, v_x_195401__boxed_1610_, v_x_195402__boxed_1611_, v_x_1608_, v_x_1609_);
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
lean_object* v___x_1624_; lean_object* v_mctx_1625_; lean_object* v_cache_1626_; lean_object* v_zetaDeltaFVarIds_1627_; lean_object* v_postponed_1628_; lean_object* v_diag_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1658_; 
v___x_1624_ = lean_st_ref_take(v___y_1622_);
v_mctx_1625_ = lean_ctor_get(v___x_1624_, 0);
v_cache_1626_ = lean_ctor_get(v___x_1624_, 1);
v_zetaDeltaFVarIds_1627_ = lean_ctor_get(v___x_1624_, 2);
v_postponed_1628_ = lean_ctor_get(v___x_1624_, 3);
v_diag_1629_ = lean_ctor_get(v___x_1624_, 4);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1631_ = v___x_1624_;
v_isShared_1632_ = v_isSharedCheck_1658_;
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
v_isShared_1632_ = v_isSharedCheck_1658_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v_depth_1633_; lean_object* v_levelAssignDepth_1634_; lean_object* v_lmvarCounter_1635_; lean_object* v_mvarCounter_1636_; lean_object* v_lDecls_1637_; lean_object* v_decls_1638_; lean_object* v_userNames_1639_; lean_object* v_lAssignment_1640_; lean_object* v_eAssignment_1641_; lean_object* v_dAssignment_1642_; lean_object* v_instanceTypedMVars_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1657_; 
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
v_instanceTypedMVars_1643_ = lean_ctor_get(v_mctx_1625_, 10);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_mctx_1625_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1645_ = v_mctx_1625_;
v_isShared_1646_ = v_isSharedCheck_1657_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_instanceTypedMVars_1643_);
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
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1657_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1647_; lean_object* v___x_1649_; 
v___x_1647_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_eAssignment_1641_, v_mvarId_1620_, v_val_1621_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 8, v___x_1647_);
v___x_1649_ = v___x_1645_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_depth_1633_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v_levelAssignDepth_1634_);
lean_ctor_set(v_reuseFailAlloc_1656_, 2, v_lmvarCounter_1635_);
lean_ctor_set(v_reuseFailAlloc_1656_, 3, v_mvarCounter_1636_);
lean_ctor_set(v_reuseFailAlloc_1656_, 4, v_lDecls_1637_);
lean_ctor_set(v_reuseFailAlloc_1656_, 5, v_decls_1638_);
lean_ctor_set(v_reuseFailAlloc_1656_, 6, v_userNames_1639_);
lean_ctor_set(v_reuseFailAlloc_1656_, 7, v_lAssignment_1640_);
lean_ctor_set(v_reuseFailAlloc_1656_, 8, v___x_1647_);
lean_ctor_set(v_reuseFailAlloc_1656_, 9, v_dAssignment_1642_);
lean_ctor_set(v_reuseFailAlloc_1656_, 10, v_instanceTypedMVars_1643_);
v___x_1649_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_object* v___x_1651_; 
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1649_);
v___x_1651_ = v___x_1631_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1649_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_cache_1626_);
lean_ctor_set(v_reuseFailAlloc_1655_, 2, v_zetaDeltaFVarIds_1627_);
lean_ctor_set(v_reuseFailAlloc_1655_, 3, v_postponed_1628_);
lean_ctor_set(v_reuseFailAlloc_1655_, 4, v_diag_1629_);
v___x_1651_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1652_ = lean_st_ref_put(v___y_1622_, v___x_1651_);
v___x_1653_ = lean_box(0);
v___x_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
return v___x_1654_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg___boxed(lean_object* v_mvarId_1659_, lean_object* v_val_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1659_, v_val_1660_, v___y_1661_);
lean_dec(v___y_1661_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(lean_object* v___y_1664_){
_start:
{
lean_object* v___x_1666_; lean_object* v_ngen_1667_; lean_object* v_namePrefix_1668_; lean_object* v_idx_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1698_; 
v___x_1666_ = lean_st_ref_get(v___y_1664_);
v_ngen_1667_ = lean_ctor_get(v___x_1666_, 2);
lean_inc_ref(v_ngen_1667_);
lean_dec(v___x_1666_);
v_namePrefix_1668_ = lean_ctor_get(v_ngen_1667_, 0);
v_idx_1669_ = lean_ctor_get(v_ngen_1667_, 1);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_ngen_1667_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1671_ = v_ngen_1667_;
v_isShared_1672_ = v_isSharedCheck_1698_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_idx_1669_);
lean_inc(v_namePrefix_1668_);
lean_dec(v_ngen_1667_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1698_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1673_; lean_object* v_env_1674_; lean_object* v_nextMacroScope_1675_; lean_object* v_auxDeclNGen_1676_; lean_object* v_traceState_1677_; lean_object* v_cache_1678_; lean_object* v_messages_1679_; lean_object* v_infoState_1680_; lean_object* v_snapshotTasks_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1696_; 
v___x_1673_ = lean_st_ref_take(v___y_1664_);
v_env_1674_ = lean_ctor_get(v___x_1673_, 0);
v_nextMacroScope_1675_ = lean_ctor_get(v___x_1673_, 1);
v_auxDeclNGen_1676_ = lean_ctor_get(v___x_1673_, 3);
v_traceState_1677_ = lean_ctor_get(v___x_1673_, 4);
v_cache_1678_ = lean_ctor_get(v___x_1673_, 5);
v_messages_1679_ = lean_ctor_get(v___x_1673_, 6);
v_infoState_1680_ = lean_ctor_get(v___x_1673_, 7);
v_snapshotTasks_1681_ = lean_ctor_get(v___x_1673_, 8);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1696_ == 0)
{
lean_object* v_unused_1697_; 
v_unused_1697_ = lean_ctor_get(v___x_1673_, 2);
lean_dec(v_unused_1697_);
v___x_1683_ = v___x_1673_;
v_isShared_1684_ = v_isSharedCheck_1696_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_snapshotTasks_1681_);
lean_inc(v_infoState_1680_);
lean_inc(v_messages_1679_);
lean_inc(v_cache_1678_);
lean_inc(v_traceState_1677_);
lean_inc(v_auxDeclNGen_1676_);
lean_inc(v_nextMacroScope_1675_);
lean_inc(v_env_1674_);
lean_dec(v___x_1673_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1696_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v_r_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1689_; 
lean_inc(v_idx_1669_);
lean_inc(v_namePrefix_1668_);
v_r_1685_ = l_Lean_Name_num___override(v_namePrefix_1668_, v_idx_1669_);
v___x_1686_ = lean_unsigned_to_nat(1u);
v___x_1687_ = lean_nat_add(v_idx_1669_, v___x_1686_);
lean_dec(v_idx_1669_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 1, v___x_1687_);
v___x_1689_ = v___x_1671_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_namePrefix_1668_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v___x_1691_; 
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 2, v___x_1689_);
v___x_1691_ = v___x_1683_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_env_1674_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v_nextMacroScope_1675_);
lean_ctor_set(v_reuseFailAlloc_1694_, 2, v___x_1689_);
lean_ctor_set(v_reuseFailAlloc_1694_, 3, v_auxDeclNGen_1676_);
lean_ctor_set(v_reuseFailAlloc_1694_, 4, v_traceState_1677_);
lean_ctor_set(v_reuseFailAlloc_1694_, 5, v_cache_1678_);
lean_ctor_set(v_reuseFailAlloc_1694_, 6, v_messages_1679_);
lean_ctor_set(v_reuseFailAlloc_1694_, 7, v_infoState_1680_);
lean_ctor_set(v_reuseFailAlloc_1694_, 8, v_snapshotTasks_1681_);
v___x_1691_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = lean_st_ref_put(v___y_1664_, v___x_1691_);
v___x_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1693_, 0, v_r_1685_);
return v___x_1693_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg___boxed(lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_1699_);
lean_dec(v___y_1699_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
v___x_1713_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_1711_);
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1713_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1713_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2___boxed(lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec(v___y_1722_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(lean_object* v___x_1739_, lean_object* v_a_1740_, uint8_t v___y_1741_, uint8_t v___x_1742_, uint8_t v___x_1743_, lean_object* v_a_1744_, lean_object* v___x_1745_, lean_object* v_expr_1746_, lean_object* v___x_1747_, lean_object* v_val_1748_, lean_object* v_mvarId_1749_, lean_object* v___x_1750_, lean_object* v_a_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Lean_Meta_mkLambdaFVars(v___x_1739_, v_a_1740_, v___y_1741_, v___x_1742_, v___y_1741_, v___x_1742_, v___x_1743_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
v___x_1765_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1));
v___x_1766_ = lean_box(0);
v___x_1767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1767_, 0, v_a_1744_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
v___x_1768_ = l_Lean_mkConst(v___x_1765_, v___x_1767_);
v___x_1769_ = lean_unsigned_to_nat(5u);
v___x_1770_ = lean_mk_empty_array_with_capacity(v___x_1769_);
v___x_1771_ = lean_array_push(v___x_1770_, v___x_1745_);
v___x_1772_ = lean_array_push(v___x_1771_, v_expr_1746_);
v___x_1773_ = lean_array_push(v___x_1772_, v___x_1747_);
v___x_1774_ = lean_array_push(v___x_1773_, v_val_1748_);
v___x_1775_ = lean_array_push(v___x_1774_, v_a_1764_);
v___x_1776_ = l_Lean_mkAppN(v___x_1768_, v___x_1775_);
lean_dec_ref(v___x_1775_);
v___x_1777_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1749_, v___x_1776_, v___y_1759_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1795_; 
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1795_ == 0)
{
lean_object* v_unused_1796_; 
v_unused_1796_ = lean_ctor_get(v___x_1777_, 0);
lean_dec(v_unused_1796_);
v___x_1779_ = v___x_1777_;
v_isShared_1780_ = v_isSharedCheck_1795_;
goto v_resetjp_1778_;
}
else
{
lean_dec(v___x_1777_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1795_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1781_; lean_object* v_toGoalState_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1793_; 
v___x_1781_ = lean_st_ref_get(v___y_1752_);
v_toGoalState_1782_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1793_ == 0)
{
lean_object* v_unused_1794_; 
v_unused_1794_ = lean_ctor_get(v___x_1781_, 1);
lean_dec(v_unused_1794_);
v___x_1784_ = v___x_1781_;
v_isShared_1785_ = v_isSharedCheck_1793_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_toGoalState_1782_);
lean_dec(v___x_1781_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1793_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 1, v___x_1750_);
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_toGoalState_1782_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v___x_1750_);
v___x_1787_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1788_; lean_object* v___x_1790_; 
v___x_1788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1788_, 0, v_a_1751_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1788_);
v___x_1790_ = v___x_1779_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1788_);
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
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_dec(v_a_1751_);
lean_dec(v___x_1750_);
v_a_1797_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1777_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1777_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
lean_dec(v_a_1751_);
lean_dec(v___x_1750_);
lean_dec(v_mvarId_1749_);
lean_dec_ref(v_val_1748_);
lean_dec_ref(v___x_1747_);
lean_dec_ref(v_expr_1746_);
lean_dec_ref(v___x_1745_);
lean_dec(v_a_1744_);
v_a_1805_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1763_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1763_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed(lean_object** _args){
lean_object* v___x_1813_ = _args[0];
lean_object* v_a_1814_ = _args[1];
lean_object* v___y_1815_ = _args[2];
lean_object* v___x_1816_ = _args[3];
lean_object* v___x_1817_ = _args[4];
lean_object* v_a_1818_ = _args[5];
lean_object* v___x_1819_ = _args[6];
lean_object* v_expr_1820_ = _args[7];
lean_object* v___x_1821_ = _args[8];
lean_object* v_val_1822_ = _args[9];
lean_object* v_mvarId_1823_ = _args[10];
lean_object* v___x_1824_ = _args[11];
lean_object* v_a_1825_ = _args[12];
lean_object* v___y_1826_ = _args[13];
lean_object* v___y_1827_ = _args[14];
lean_object* v___y_1828_ = _args[15];
lean_object* v___y_1829_ = _args[16];
lean_object* v___y_1830_ = _args[17];
lean_object* v___y_1831_ = _args[18];
lean_object* v___y_1832_ = _args[19];
lean_object* v___y_1833_ = _args[20];
lean_object* v___y_1834_ = _args[21];
lean_object* v___y_1835_ = _args[22];
lean_object* v___y_1836_ = _args[23];
_start:
{
uint8_t v___y_195727__boxed_1837_; uint8_t v___x_195728__boxed_1838_; uint8_t v___x_195729__boxed_1839_; lean_object* v_res_1840_; 
v___y_195727__boxed_1837_ = lean_unbox(v___y_1815_);
v___x_195728__boxed_1838_ = lean_unbox(v___x_1816_);
v___x_195729__boxed_1839_ = lean_unbox(v___x_1817_);
v_res_1840_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(v___x_1813_, v_a_1814_, v___y_195727__boxed_1837_, v___x_195728__boxed_1838_, v___x_195729__boxed_1839_, v_a_1818_, v___x_1819_, v_expr_1820_, v___x_1821_, v_val_1822_, v_mvarId_1823_, v___x_1824_, v_a_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___x_1813_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(lean_object* v___x_1846_, lean_object* v_a_1847_, uint8_t v___x_1848_, uint8_t v___x_1849_, uint8_t v___x_1850_, lean_object* v_a_1851_, lean_object* v___x_1852_, lean_object* v___x_1853_, lean_object* v_expr_1854_, lean_object* v___x_1855_, lean_object* v_val_1856_, lean_object* v_mvarId_1857_, lean_object* v___x_1858_, lean_object* v_a_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Lean_Meta_mkLambdaFVars(v___x_1846_, v_a_1847_, v___x_1848_, v___x_1849_, v___x_1848_, v___x_1849_, v___x_1850_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_a_1872_);
lean_dec_ref_known(v___x_1871_, 1);
v___x_1873_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1));
v___x_1874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1874_, 0, v_a_1851_);
lean_ctor_set(v___x_1874_, 1, v___x_1852_);
v___x_1875_ = l_Lean_mkConst(v___x_1873_, v___x_1874_);
v___x_1876_ = lean_unsigned_to_nat(5u);
v___x_1877_ = lean_mk_empty_array_with_capacity(v___x_1876_);
v___x_1878_ = lean_array_push(v___x_1877_, v___x_1853_);
v___x_1879_ = lean_array_push(v___x_1878_, v_expr_1854_);
v___x_1880_ = lean_array_push(v___x_1879_, v___x_1855_);
v___x_1881_ = lean_array_push(v___x_1880_, v_val_1856_);
v___x_1882_ = lean_array_push(v___x_1881_, v_a_1872_);
v___x_1883_ = l_Lean_mkAppN(v___x_1875_, v___x_1882_);
lean_dec_ref(v___x_1882_);
v___x_1884_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1857_, v___x_1883_, v___y_1867_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1902_; 
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1902_ == 0)
{
lean_object* v_unused_1903_; 
v_unused_1903_ = lean_ctor_get(v___x_1884_, 0);
lean_dec(v_unused_1903_);
v___x_1886_ = v___x_1884_;
v_isShared_1887_ = v_isSharedCheck_1902_;
goto v_resetjp_1885_;
}
else
{
lean_dec(v___x_1884_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1902_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1888_; lean_object* v_toGoalState_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1900_; 
v___x_1888_ = lean_st_ref_get(v___y_1860_);
v_toGoalState_1889_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1900_ == 0)
{
lean_object* v_unused_1901_; 
v_unused_1901_ = lean_ctor_get(v___x_1888_, 1);
lean_dec(v_unused_1901_);
v___x_1891_ = v___x_1888_;
v_isShared_1892_ = v_isSharedCheck_1900_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_toGoalState_1889_);
lean_dec(v___x_1888_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1900_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 1, v___x_1858_);
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_toGoalState_1889_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v___x_1858_);
v___x_1894_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
lean_object* v___x_1895_; lean_object* v___x_1897_; 
v___x_1895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1895_, 0, v_a_1859_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1895_);
v___x_1897_ = v___x_1886_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v___x_1895_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec(v_a_1859_);
lean_dec(v___x_1858_);
v_a_1904_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1884_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1884_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
lean_dec(v_a_1859_);
lean_dec(v___x_1858_);
lean_dec(v_mvarId_1857_);
lean_dec_ref(v_val_1856_);
lean_dec_ref(v___x_1855_);
lean_dec_ref(v_expr_1854_);
lean_dec_ref(v___x_1853_);
lean_dec(v___x_1852_);
lean_dec(v_a_1851_);
v_a_1912_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1871_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1871_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed(lean_object** _args){
lean_object* v___x_1920_ = _args[0];
lean_object* v_a_1921_ = _args[1];
lean_object* v___x_1922_ = _args[2];
lean_object* v___x_1923_ = _args[3];
lean_object* v___x_1924_ = _args[4];
lean_object* v_a_1925_ = _args[5];
lean_object* v___x_1926_ = _args[6];
lean_object* v___x_1927_ = _args[7];
lean_object* v_expr_1928_ = _args[8];
lean_object* v___x_1929_ = _args[9];
lean_object* v_val_1930_ = _args[10];
lean_object* v_mvarId_1931_ = _args[11];
lean_object* v___x_1932_ = _args[12];
lean_object* v_a_1933_ = _args[13];
lean_object* v___y_1934_ = _args[14];
lean_object* v___y_1935_ = _args[15];
lean_object* v___y_1936_ = _args[16];
lean_object* v___y_1937_ = _args[17];
lean_object* v___y_1938_ = _args[18];
lean_object* v___y_1939_ = _args[19];
lean_object* v___y_1940_ = _args[20];
lean_object* v___y_1941_ = _args[21];
lean_object* v___y_1942_ = _args[22];
lean_object* v___y_1943_ = _args[23];
lean_object* v___y_1944_ = _args[24];
_start:
{
uint8_t v___x_195909__boxed_1945_; uint8_t v___x_195910__boxed_1946_; uint8_t v___x_195911__boxed_1947_; lean_object* v_res_1948_; 
v___x_195909__boxed_1945_ = lean_unbox(v___x_1922_);
v___x_195910__boxed_1946_ = lean_unbox(v___x_1923_);
v___x_195911__boxed_1947_ = lean_unbox(v___x_1924_);
v_res_1948_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(v___x_1920_, v_a_1921_, v___x_195909__boxed_1945_, v___x_195910__boxed_1946_, v___x_195911__boxed_1947_, v_a_1925_, v___x_1926_, v___x_1927_, v_expr_1928_, v___x_1929_, v_val_1930_, v_mvarId_1931_, v___x_1932_, v_a_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___x_1920_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(lean_object* v___x_1949_, lean_object* v_a_1950_, uint8_t v___y_1951_, uint8_t v___x_1952_, uint8_t v___x_1953_, lean_object* v_mvarId_1954_, lean_object* v___x_1955_, lean_object* v_a_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Lean_Meta_mkLambdaFVars(v___x_1949_, v_a_1950_, v___y_1951_, v___x_1952_, v___y_1951_, v___x_1952_, v___x_1953_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1970_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref_known(v___x_1968_, 1);
v___x_1970_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1954_, v_a_1969_, v___y_1964_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1988_; 
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1988_ == 0)
{
lean_object* v_unused_1989_; 
v_unused_1989_ = lean_ctor_get(v___x_1970_, 0);
lean_dec(v_unused_1989_);
v___x_1972_ = v___x_1970_;
v_isShared_1973_ = v_isSharedCheck_1988_;
goto v_resetjp_1971_;
}
else
{
lean_dec(v___x_1970_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1988_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; lean_object* v_toGoalState_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1986_; 
v___x_1974_ = lean_st_ref_get(v___y_1957_);
v_toGoalState_1975_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1986_ == 0)
{
lean_object* v_unused_1987_; 
v_unused_1987_ = lean_ctor_get(v___x_1974_, 1);
lean_dec(v_unused_1987_);
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_1986_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_toGoalState_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1986_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 1, v___x_1955_);
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_toGoalState_1975_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v___x_1955_);
v___x_1980_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
lean_object* v___x_1981_; lean_object* v___x_1983_; 
v___x_1981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1981_, 0, v_a_1956_);
lean_ctor_set(v___x_1981_, 1, v___x_1980_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1981_);
v___x_1983_ = v___x_1972_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1981_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
lean_dec(v_a_1956_);
lean_dec(v___x_1955_);
v_a_1990_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1970_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1970_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
else
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2005_; 
lean_dec(v_a_1956_);
lean_dec(v___x_1955_);
lean_dec(v_mvarId_1954_);
v_a_1998_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_2000_ = v___x_1968_;
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1968_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1998_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed(lean_object** _args){
lean_object* v___x_2006_ = _args[0];
lean_object* v_a_2007_ = _args[1];
lean_object* v___y_2008_ = _args[2];
lean_object* v___x_2009_ = _args[3];
lean_object* v___x_2010_ = _args[4];
lean_object* v_mvarId_2011_ = _args[5];
lean_object* v___x_2012_ = _args[6];
lean_object* v_a_2013_ = _args[7];
lean_object* v___y_2014_ = _args[8];
lean_object* v___y_2015_ = _args[9];
lean_object* v___y_2016_ = _args[10];
lean_object* v___y_2017_ = _args[11];
lean_object* v___y_2018_ = _args[12];
lean_object* v___y_2019_ = _args[13];
lean_object* v___y_2020_ = _args[14];
lean_object* v___y_2021_ = _args[15];
lean_object* v___y_2022_ = _args[16];
lean_object* v___y_2023_ = _args[17];
lean_object* v___y_2024_ = _args[18];
_start:
{
uint8_t v___y_196080__boxed_2025_; uint8_t v___x_196081__boxed_2026_; uint8_t v___x_196082__boxed_2027_; lean_object* v_res_2028_; 
v___y_196080__boxed_2025_ = lean_unbox(v___y_2008_);
v___x_196081__boxed_2026_ = lean_unbox(v___x_2009_);
v___x_196082__boxed_2027_ = lean_unbox(v___x_2010_);
v_res_2028_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(v___x_2006_, v_a_2007_, v___y_196080__boxed_2025_, v___x_196081__boxed_2026_, v___x_196082__boxed_2027_, v_mvarId_2011_, v___x_2012_, v_a_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
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
lean_dec_ref(v___x_2006_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(lean_object* v_mvarId_2031_, lean_object* v___x_2032_, lean_object* v_generation_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v___x_2045_; 
lean_inc(v_mvarId_2031_);
v___x_2045_ = l_Lean_MVarId_getTag(v_mvarId_2031_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2047_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref_known(v___x_2045_, 1);
v___x_2047_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2032_, v_a_2046_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2049_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc_n(v_a_2048_, 2);
lean_dec_ref_known(v___x_2047_, 1);
v___x_2049_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2031_, v_a_2048_, v___y_2041_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v___x_2050_; lean_object* v_toGoalState_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2060_; 
lean_dec_ref_known(v___x_2049_, 1);
v___x_2050_ = lean_st_ref_get(v___y_2034_);
v_toGoalState_2051_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2060_ == 0)
{
lean_object* v_unused_2061_; 
v_unused_2061_ = lean_ctor_get(v___x_2050_, 1);
lean_dec(v_unused_2061_);
v___x_2053_ = v___x_2050_;
v_isShared_2054_ = v_isSharedCheck_2060_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_toGoalState_2051_);
lean_dec(v___x_2050_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2060_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; lean_object* v___x_2057_; 
v___x_2055_ = l_Lean_Expr_mvarId_x21(v_a_2048_);
lean_dec(v_a_2048_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 1, v___x_2055_);
v___x_2057_ = v___x_2053_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_toGoalState_2051_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v___x_2055_);
v___x_2057_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
lean_object* v___x_2058_; 
v___x_2058_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v___x_2057_, v_generation_2033_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
return v___x_2058_;
}
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec(v_a_2048_);
lean_dec(v_generation_2033_);
v_a_2062_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2049_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2049_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
lean_dec(v_generation_2033_);
lean_dec(v_mvarId_2031_);
v_a_2070_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2047_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2047_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec(v_generation_2033_);
lean_dec_ref(v___x_2032_);
lean_dec(v_mvarId_2031_);
v_a_2078_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2045_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2045_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed(lean_object* v_mvarId_2086_, lean_object* v___x_2087_, lean_object* v_generation_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(v_mvarId_2086_, v___x_2087_, v_generation_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec(v___y_2089_);
return v_res_2100_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4(void){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2106_ = lean_box(0);
v___x_2107_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3));
v___x_2108_ = l_Lean_mkConst(v___x_2107_, v___x_2106_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(lean_object* v_goal_2109_, lean_object* v_generation_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v___x_2121_; lean_object* v_a_2123_; lean_object* v___y_2128_; lean_object* v___x_2138_; lean_object* v_mvarId_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2427_; 
lean_inc_ref(v_goal_2109_);
v___x_2121_ = lean_st_mk_ref(v_goal_2109_);
v___x_2138_ = lean_st_ref_get(v___x_2121_);
v_mvarId_2139_ = lean_ctor_get(v___x_2138_, 1);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2427_ == 0)
{
lean_object* v_unused_2428_; 
v_unused_2428_ = lean_ctor_get(v___x_2138_, 0);
lean_dec(v_unused_2428_);
v___x_2141_ = v___x_2138_;
v_isShared_2142_ = v_isSharedCheck_2427_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_mvarId_2139_);
lean_dec(v___x_2138_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2427_;
goto v_resetjp_2140_;
}
v___jp_2122_:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2124_ = lean_st_ref_get(v___x_2121_);
lean_dec(v___x_2121_);
v___x_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2125_, 0, v_a_2123_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
return v___x_2126_;
}
v___jp_2127_:
{
if (lean_obj_tag(v___y_2128_) == 0)
{
lean_object* v_a_2129_; 
v_a_2129_ = lean_ctor_get(v___y_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref_known(v___y_2128_, 1);
v_a_2123_ = v_a_2129_;
goto v___jp_2122_;
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_dec(v___x_2121_);
v_a_2130_ = lean_ctor_get(v___y_2128_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___y_2128_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___y_2128_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___y_2128_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
v_resetjp_2140_:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_MVarId_getType(v_mvarId_2139_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; uint8_t v___x_2145_; uint8_t v___x_2146_; lean_object* v___y_2148_; lean_object* v___y_2149_; uint8_t v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; lean_object* v___y_2165_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2143_, 1);
v___x_2145_ = l_Lean_Expr_isForall(v_a_2144_);
v___x_2146_ = 1;
if (v___x_2145_ == 0)
{
uint8_t v___x_2188_; 
lean_del_object(v___x_2141_);
v___x_2188_ = l_Lean_Expr_isLet(v_a_2144_);
if (v___x_2188_ == 0)
{
lean_object* v___x_2189_; 
lean_dec(v_a_2144_);
lean_dec_ref(v___y_2116_);
lean_dec(v_generation_2110_);
v___x_2189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2189_, 0, v_goal_2109_);
v_a_2123_ = v___x_2189_;
goto v___jp_2122_;
}
else
{
lean_object* v___x_2190_; 
lean_dec_ref(v_goal_2109_);
v___x_2190_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_2112_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; uint8_t v_zetaDelta_2192_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2191_);
lean_dec_ref_known(v___x_2190_, 1);
v_zetaDelta_2192_ = lean_ctor_get_uint8(v_a_2191_, sizeof(void*)*14 + 19);
lean_dec(v_a_2191_);
if (v_zetaDelta_2192_ == 0)
{
lean_object* v___x_2193_; 
lean_dec(v_a_2144_);
v___x_2193_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_2121_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2195_; lean_object* v_mvarId_2196_; lean_object* v___f_2197_; lean_object* v___x_2198_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2194_);
lean_dec_ref_known(v___x_2193_, 1);
v___x_2195_ = lean_st_ref_get(v___x_2121_);
v_mvarId_2196_ = lean_ctor_get(v___x_2195_, 1);
lean_inc(v_mvarId_2196_);
lean_dec(v___x_2195_);
v___f_2197_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed), 13, 2);
lean_closure_set(v___f_2197_, 0, v_a_2194_);
lean_closure_set(v___f_2197_, 1, v_generation_2110_);
v___x_2198_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_2196_, v___f_2197_, v___x_2121_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
lean_dec_ref(v___y_2116_);
v___y_2128_ = v___x_2198_;
goto v___jp_2127_;
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_dec(v___x_2121_);
lean_dec_ref(v___y_2116_);
lean_dec(v_generation_2110_);
v_a_2199_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2193_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2193_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
else
{
lean_object* v___x_2207_; lean_object* v_mvarId_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___f_2211_; lean_object* v___x_2212_; 
v___x_2207_ = lean_st_ref_get(v___x_2121_);
v_mvarId_2208_ = lean_ctor_get(v___x_2207_, 1);
lean_inc_n(v_mvarId_2208_, 2);
lean_dec(v___x_2207_);
v___x_2209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__0));
v___x_2210_ = l_Lean_Meta_expandLet(v_a_2144_, v___x_2209_, v___x_2146_);
lean_dec(v_a_2144_);
v___f_2211_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed), 14, 3);
lean_closure_set(v___f_2211_, 0, v_mvarId_2208_);
lean_closure_set(v___f_2211_, 1, v___x_2210_);
lean_closure_set(v___f_2211_, 2, v_generation_2110_);
v___x_2212_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_2208_, v___f_2211_, v___x_2121_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
lean_dec_ref(v___y_2116_);
v___y_2128_ = v___x_2212_;
goto v___jp_2127_;
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec(v_a_2144_);
lean_dec(v___x_2121_);
lean_dec_ref(v___y_2116_);
lean_dec(v_generation_2110_);
v_a_2213_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2190_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2190_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
}
else
{
lean_object* v___x_2221_; lean_object* v___y_2223_; lean_object* v___y_2224_; uint8_t v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; uint8_t v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v_localInsts_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___x_2319_; 
lean_dec(v_generation_2110_);
lean_dec_ref(v_goal_2109_);
v___x_2221_ = l_Lean_Expr_bindingDomain_x21(v_a_2144_);
lean_inc_ref(v___x_2221_);
v___x_2319_ = l_Lean_Meta_isProp(v___x_2221_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; uint8_t v___y_2322_; uint8_t v___x_2395_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v___x_2319_, 1);
v___x_2395_ = lean_unbox(v_a_2320_);
lean_dec(v_a_2320_);
if (v___x_2395_ == 0)
{
if (v___x_2145_ == 0)
{
lean_del_object(v___x_2141_);
v___y_2322_ = v___x_2145_;
goto v___jp_2321_;
}
else
{
lean_object* v___x_2396_; 
lean_dec_ref(v___x_2221_);
lean_dec(v_a_2144_);
v___x_2396_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_2121_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
lean_dec_ref(v___y_2116_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v___x_2398_; lean_object* v___x_2400_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2397_);
lean_dec_ref_known(v___x_2396_, 1);
v___x_2398_ = lean_st_ref_get(v___x_2121_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set_tag(v___x_2141_, 3);
lean_ctor_set(v___x_2141_, 1, v___x_2398_);
lean_ctor_set(v___x_2141_, 0, v_a_2397_);
v___x_2400_ = v___x_2141_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2397_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
v_a_2123_ = v___x_2400_;
goto v___jp_2122_;
}
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
lean_del_object(v___x_2141_);
lean_dec(v___x_2121_);
v_a_2402_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2396_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2396_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
}
else
{
uint8_t v___x_2410_; 
lean_del_object(v___x_2141_);
v___x_2410_ = 0;
v___y_2322_ = v___x_2410_;
goto v___jp_2321_;
}
v___jp_2321_:
{
lean_object* v___x_2323_; lean_object* v_mvarId_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2393_; 
v___x_2323_ = lean_st_ref_get(v___x_2121_);
v_mvarId_2324_ = lean_ctor_get(v___x_2323_, 1);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2393_ == 0)
{
lean_object* v_unused_2394_; 
v_unused_2394_ = lean_ctor_get(v___x_2323_, 0);
lean_dec(v_unused_2394_);
v___x_2326_ = v___x_2323_;
v_isShared_2327_ = v_isSharedCheck_2393_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_mvarId_2324_);
lean_dec(v___x_2323_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2393_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2328_; 
lean_inc(v_mvarId_2324_);
v___x_2328_ = l_Lean_MVarId_getTag(v_mvarId_2324_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2330_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2329_);
lean_dec_ref_known(v___x_2328_, 1);
v___x_2330_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___x_2121_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v___x_2332_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2331_);
lean_dec_ref_known(v___x_2330_, 1);
lean_inc_ref(v___x_2221_);
v___x_2332_ = l_Lean_Meta_Grind_preprocessHypothesis(v___x_2221_, v___x_2121_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v_expr_2334_; lean_object* v_proof_x3f_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2332_, 1);
v_expr_2334_ = lean_ctor_get(v_a_2333_, 0);
lean_inc_ref_n(v_expr_2334_, 2);
v_proof_x3f_2335_ = lean_ctor_get(v_a_2333_, 1);
lean_inc(v_proof_x3f_2335_);
lean_dec(v_a_2333_);
v___x_2336_ = l_Lean_Expr_bindingName_x21(v_a_2144_);
lean_inc(v___x_2336_);
v___x_2337_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v___x_2336_, v_expr_2334_, v___x_2121_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v_lctx_2339_; lean_object* v_localInstances_2340_; lean_object* v___x_2341_; uint8_t v___x_2342_; uint8_t v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v_lctx_2339_ = lean_ctor_get(v___y_2116_, 2);
v_localInstances_2340_ = lean_ctor_get(v___y_2116_, 3);
lean_inc_n(v_a_2331_, 2);
v___x_2341_ = l_Lean_mkFVar(v_a_2331_);
v___x_2342_ = l_Lean_Expr_bindingInfo_x21(v_a_2144_);
v___x_2343_ = 0;
lean_inc_ref_n(v_expr_2334_, 2);
lean_inc_ref(v_lctx_2339_);
v___x_2344_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_2339_, v_a_2331_, v_a_2338_, v_expr_2334_, v___x_2342_, v___x_2343_);
v___x_2345_ = l_Lean_Meta_isClass_x3f(v_expr_2334_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2347_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2346_);
lean_dec_ref_known(v___x_2345_, 1);
v___x_2347_ = l_Lean_Expr_bindingBody_x21(v_a_2144_);
if (lean_obj_tag(v_a_2346_) == 1)
{
lean_object* v_val_2348_; lean_object* v___x_2350_; 
v_val_2348_ = lean_ctor_get(v_a_2346_, 0);
lean_inc(v_val_2348_);
lean_dec_ref_known(v_a_2346_, 1);
lean_inc_ref(v___x_2341_);
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 1, v___x_2341_);
lean_ctor_set(v___x_2326_, 0, v_val_2348_);
v___x_2350_ = v___x_2326_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_val_2348_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v___x_2341_);
v___x_2350_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
lean_object* v___x_2351_; 
lean_inc_ref(v_localInstances_2340_);
v___x_2351_ = lean_array_push(v_localInstances_2340_, v___x_2350_);
lean_inc(v___x_2121_);
lean_inc_ref(v_expr_2334_);
v___y_2223_ = v_mvarId_2324_;
v___y_2224_ = v_a_2331_;
v___y_2225_ = v___y_2322_;
v___y_2226_ = v_expr_2334_;
v___y_2227_ = v___x_2347_;
v___y_2228_ = v_a_2329_;
v___y_2229_ = v___x_2342_;
v___y_2230_ = v___x_2344_;
v___y_2231_ = v_proof_x3f_2335_;
v___y_2232_ = v___x_2341_;
v___y_2233_ = v___x_2336_;
v___y_2234_ = v_expr_2334_;
v_localInsts_2235_ = v___x_2351_;
v___y_2236_ = v___x_2121_;
v___y_2237_ = v___y_2111_;
v___y_2238_ = v___y_2112_;
v___y_2239_ = v___y_2113_;
v___y_2240_ = v___y_2114_;
v___y_2241_ = v___y_2115_;
v___y_2242_ = v___y_2116_;
v___y_2243_ = v___y_2117_;
v___y_2244_ = v___y_2118_;
v___y_2245_ = v___y_2119_;
goto v___jp_2222_;
}
}
else
{
lean_inc_ref(v_localInstances_2340_);
lean_dec(v_a_2346_);
lean_del_object(v___x_2326_);
lean_inc(v___x_2121_);
lean_inc_ref(v_expr_2334_);
v___y_2223_ = v_mvarId_2324_;
v___y_2224_ = v_a_2331_;
v___y_2225_ = v___y_2322_;
v___y_2226_ = v_expr_2334_;
v___y_2227_ = v___x_2347_;
v___y_2228_ = v_a_2329_;
v___y_2229_ = v___x_2342_;
v___y_2230_ = v___x_2344_;
v___y_2231_ = v_proof_x3f_2335_;
v___y_2232_ = v___x_2341_;
v___y_2233_ = v___x_2336_;
v___y_2234_ = v_expr_2334_;
v_localInsts_2235_ = v_localInstances_2340_;
v___y_2236_ = v___x_2121_;
v___y_2237_ = v___y_2111_;
v___y_2238_ = v___y_2112_;
v___y_2239_ = v___y_2113_;
v___y_2240_ = v___y_2114_;
v___y_2241_ = v___y_2115_;
v___y_2242_ = v___y_2116_;
v___y_2243_ = v___y_2117_;
v___y_2244_ = v___y_2118_;
v___y_2245_ = v___y_2119_;
goto v___jp_2222_;
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_dec_ref(v___x_2344_);
lean_dec_ref(v___x_2341_);
lean_dec(v___x_2336_);
lean_dec(v_proof_x3f_2335_);
lean_dec_ref(v_expr_2334_);
lean_dec(v_a_2331_);
lean_dec(v_a_2329_);
lean_del_object(v___x_2326_);
lean_dec(v_mvarId_2324_);
lean_dec_ref(v___x_2221_);
lean_dec(v_a_2144_);
lean_dec(v___x_2121_);
lean_dec_ref(v___y_2116_);
v_a_2353_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2345_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2345_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
else
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
lean_dec(v___x_2336_);
lean_dec(v_proof_x3f_2335_);
lean_dec_ref(v_expr_2334_);
lean_dec(v_a_2331_);
lean_dec(v_a_2329_);
lean_del_object(v___x_2326_);
lean_dec(v_mvarId_2324_);
lean_dec_ref(v___x_2221_);
lean_dec(v_a_2144_);
lean_dec(v___x_2121_);
lean_dec_ref(v___y_2116_);
v_a_2361_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v___x_2337_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2337_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
lean_dec(v_a_2331_);
lean_dec(v_a_2329_);
lean_del_object(v___x_2326_);
lean_dec(v_mvarId_2324_);
lean_dec_ref(v___x_2221_);
lean_dec(v_a_2144_);
lean_dec(v___x_2121_);
lean_dec_ref(v___y_2116_);
v_a_2369_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2332_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2332_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
lean_dec(v_a_2329_);
lean_del_object(v___x_2326_);
lean_dec(v_mvarId_2324_);
lean_dec_ref(v___x_2221_);
lean_dec(v_a_2144_);
lean_dec(v___x_2121_);
lean_dec_ref(v___y_2116_);
v_a_2377_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2330_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2330_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
lean_del_object(v___x_2326_);
lean_dec(v_mvarId_2324_);
lean_dec_ref(v___x_2221_);
lean_dec(v_a_2144_);
lean_dec(v___x_2121_);
lean_dec_ref(v___y_2116_);
v_a_2385_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2387_ = v___x_2328_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2328_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
}
}
else
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
lean_dec_ref(v___x_2221_);
lean_dec(v_a_2144_);
lean_del_object(v___x_2141_);
lean_dec(v___x_2121_);
lean_dec_ref(v___y_2116_);
v_a_2411_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2413_ = v___x_2319_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2319_);
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
v___jp_2222_:
{
if (lean_obj_tag(v___y_2231_) == 0)
{
uint8_t v___x_2246_; 
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2226_);
lean_dec_ref(v___x_2221_);
v___x_2246_ = l_Lean_Expr_isArrow(v_a_2144_);
lean_dec(v_a_2144_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2247_; 
v___x_2247_ = lean_expr_instantiate1(v___y_2227_, v___y_2232_);
lean_dec_ref(v___y_2227_);
v___y_2148_ = v___y_2223_;
v___y_2149_ = v___y_2224_;
v___y_2150_ = v___y_2225_;
v___y_2151_ = v___y_2243_;
v___y_2152_ = v___y_2245_;
v___y_2153_ = v_localInsts_2235_;
v___y_2154_ = v___y_2239_;
v___y_2155_ = v___y_2237_;
v___y_2156_ = v___y_2228_;
v___y_2157_ = v___y_2236_;
v___y_2158_ = v___y_2230_;
v___y_2159_ = v___y_2242_;
v___y_2160_ = v___y_2241_;
v___y_2161_ = v___y_2232_;
v___y_2162_ = v___y_2240_;
v___y_2163_ = v___y_2244_;
v___y_2164_ = v___y_2238_;
v___y_2165_ = v___x_2247_;
goto v___jp_2147_;
}
else
{
v___y_2148_ = v___y_2223_;
v___y_2149_ = v___y_2224_;
v___y_2150_ = v___y_2225_;
v___y_2151_ = v___y_2243_;
v___y_2152_ = v___y_2245_;
v___y_2153_ = v_localInsts_2235_;
v___y_2154_ = v___y_2239_;
v___y_2155_ = v___y_2237_;
v___y_2156_ = v___y_2228_;
v___y_2157_ = v___y_2236_;
v___y_2158_ = v___y_2230_;
v___y_2159_ = v___y_2242_;
v___y_2160_ = v___y_2241_;
v___y_2161_ = v___y_2232_;
v___y_2162_ = v___y_2240_;
v___y_2163_ = v___y_2244_;
v___y_2164_ = v___y_2238_;
v___y_2165_ = v___y_2227_;
goto v___jp_2147_;
}
}
else
{
lean_object* v_val_2248_; uint8_t v___x_2249_; 
v_val_2248_ = lean_ctor_get(v___y_2231_, 0);
lean_inc(v_val_2248_);
lean_dec_ref_known(v___y_2231_, 1);
v___x_2249_ = l_Lean_Expr_isArrow(v_a_2144_);
lean_dec(v_a_2144_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
lean_inc_ref(v___y_2227_);
lean_inc_ref_n(v___x_2221_, 2);
v___x_2250_ = l_Lean_mkLambda(v___y_2233_, v___y_2229_, v___x_2221_, v___y_2227_);
v___x_2251_ = lean_box(0);
v___x_2252_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4);
lean_inc_ref(v___y_2232_);
lean_inc(v_val_2248_);
v___x_2253_ = l_Lean_mkApp4(v___x_2252_, v___x_2221_, v___y_2234_, v_val_2248_, v___y_2232_);
v___x_2254_ = lean_expr_instantiate1(v___y_2227_, v___x_2253_);
lean_dec_ref(v___x_2253_);
lean_dec_ref(v___y_2227_);
lean_inc_ref(v___x_2254_);
v___x_2255_ = l_Lean_Meta_getLevel(v___x_2254_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; uint8_t v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
lean_inc(v_a_2256_);
lean_dec_ref_known(v___x_2255_, 1);
v___x_2257_ = 2;
v___x_2258_ = lean_unsigned_to_nat(0u);
v___x_2259_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_2230_, v_localInsts_2235_, v___x_2254_, v___x_2257_, v___y_2228_, v___x_2258_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; uint8_t v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___f_2269_; lean_object* v___x_2270_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_a_2260_);
lean_dec_ref_known(v___x_2259_, 1);
v___x_2261_ = l_Lean_Expr_mvarId_x21(v_a_2260_);
v___x_2262_ = lean_unsigned_to_nat(1u);
v___x_2263_ = lean_mk_empty_array_with_capacity(v___x_2262_);
v___x_2264_ = lean_array_push(v___x_2263_, v___y_2232_);
v___x_2265_ = 1;
v___x_2266_ = lean_box(v___x_2249_);
v___x_2267_ = lean_box(v___x_2146_);
v___x_2268_ = lean_box(v___x_2265_);
lean_inc(v___x_2261_);
v___f_2269_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed), 25, 14);
lean_closure_set(v___f_2269_, 0, v___x_2264_);
lean_closure_set(v___f_2269_, 1, v_a_2260_);
lean_closure_set(v___f_2269_, 2, v___x_2266_);
lean_closure_set(v___f_2269_, 3, v___x_2267_);
lean_closure_set(v___f_2269_, 4, v___x_2268_);
lean_closure_set(v___f_2269_, 5, v_a_2256_);
lean_closure_set(v___f_2269_, 6, v___x_2251_);
lean_closure_set(v___f_2269_, 7, v___x_2221_);
lean_closure_set(v___f_2269_, 8, v___y_2226_);
lean_closure_set(v___f_2269_, 9, v___x_2250_);
lean_closure_set(v___f_2269_, 10, v_val_2248_);
lean_closure_set(v___f_2269_, 11, v___y_2223_);
lean_closure_set(v___f_2269_, 12, v___x_2261_);
lean_closure_set(v___f_2269_, 13, v___y_2224_);
v___x_2270_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2261_, v___f_2269_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2236_);
v___y_2128_ = v___x_2270_;
goto v___jp_2127_;
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
lean_dec(v_a_2256_);
lean_dec_ref(v___x_2250_);
lean_dec(v_val_2248_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2232_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___x_2221_);
lean_dec(v___x_2121_);
v_a_2271_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2259_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2259_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2276_; 
if (v_isShared_2274_ == 0)
{
v___x_2276_ = v___x_2273_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_dec_ref(v___x_2254_);
lean_dec_ref(v___x_2250_);
lean_dec(v_val_2248_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2236_);
lean_dec_ref(v_localInsts_2235_);
lean_dec_ref(v___y_2232_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___x_2221_);
lean_dec(v___x_2121_);
v_a_2279_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2255_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2255_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
else
{
lean_object* v___x_2287_; 
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_inc_ref(v___y_2227_);
v___x_2287_ = l_Lean_Meta_getLevel(v___y_2227_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; uint8_t v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref_known(v___x_2287_, 1);
v___x_2289_ = 2;
v___x_2290_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___y_2227_);
v___x_2291_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_2230_, v_localInsts_2235_, v___y_2227_, v___x_2289_, v___y_2228_, v___x_2290_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v_a_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; uint8_t v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___f_2301_; lean_object* v___x_2302_; 
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_a_2292_);
lean_dec_ref_known(v___x_2291_, 1);
v___x_2293_ = l_Lean_Expr_mvarId_x21(v_a_2292_);
v___x_2294_ = lean_unsigned_to_nat(1u);
v___x_2295_ = lean_mk_empty_array_with_capacity(v___x_2294_);
v___x_2296_ = lean_array_push(v___x_2295_, v___y_2232_);
v___x_2297_ = 1;
v___x_2298_ = lean_box(v___y_2225_);
v___x_2299_ = lean_box(v___x_2146_);
v___x_2300_ = lean_box(v___x_2297_);
lean_inc(v___x_2293_);
v___f_2301_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed), 24, 13);
lean_closure_set(v___f_2301_, 0, v___x_2296_);
lean_closure_set(v___f_2301_, 1, v_a_2292_);
lean_closure_set(v___f_2301_, 2, v___x_2298_);
lean_closure_set(v___f_2301_, 3, v___x_2299_);
lean_closure_set(v___f_2301_, 4, v___x_2300_);
lean_closure_set(v___f_2301_, 5, v_a_2288_);
lean_closure_set(v___f_2301_, 6, v___x_2221_);
lean_closure_set(v___f_2301_, 7, v___y_2226_);
lean_closure_set(v___f_2301_, 8, v___y_2227_);
lean_closure_set(v___f_2301_, 9, v_val_2248_);
lean_closure_set(v___f_2301_, 10, v___y_2223_);
lean_closure_set(v___f_2301_, 11, v___x_2293_);
lean_closure_set(v___f_2301_, 12, v___y_2224_);
v___x_2302_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2293_, v___f_2301_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2236_);
v___y_2128_ = v___x_2302_;
goto v___jp_2127_;
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_dec(v_a_2288_);
lean_dec(v_val_2248_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2232_);
lean_dec_ref(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___x_2221_);
lean_dec(v___x_2121_);
v_a_2303_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2291_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2291_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
lean_dec(v_val_2248_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2236_);
lean_dec_ref(v_localInsts_2235_);
lean_dec_ref(v___y_2232_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___x_2221_);
lean_dec(v___x_2121_);
v_a_2311_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2287_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2287_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
}
}
}
v___jp_2147_:
{
uint8_t v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2166_ = 2;
v___x_2167_ = lean_unsigned_to_nat(0u);
v___x_2168_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_2158_, v___y_2153_, v___y_2165_, v___x_2166_, v___y_2156_, v___x_2167_, v___y_2159_, v___y_2151_, v___y_2163_, v___y_2152_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; uint8_t v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___f_2178_; lean_object* v___x_2179_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2169_);
lean_dec_ref_known(v___x_2168_, 1);
v___x_2170_ = l_Lean_Expr_mvarId_x21(v_a_2169_);
v___x_2171_ = lean_unsigned_to_nat(1u);
v___x_2172_ = lean_mk_empty_array_with_capacity(v___x_2171_);
v___x_2173_ = lean_array_push(v___x_2172_, v___y_2161_);
v___x_2174_ = 1;
v___x_2175_ = lean_box(v___y_2150_);
v___x_2176_ = lean_box(v___x_2146_);
v___x_2177_ = lean_box(v___x_2174_);
lean_inc(v___x_2170_);
v___f_2178_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed), 19, 8);
lean_closure_set(v___f_2178_, 0, v___x_2173_);
lean_closure_set(v___f_2178_, 1, v_a_2169_);
lean_closure_set(v___f_2178_, 2, v___x_2175_);
lean_closure_set(v___f_2178_, 3, v___x_2176_);
lean_closure_set(v___f_2178_, 4, v___x_2177_);
lean_closure_set(v___f_2178_, 5, v___y_2148_);
lean_closure_set(v___f_2178_, 6, v___x_2170_);
lean_closure_set(v___f_2178_, 7, v___y_2149_);
v___x_2179_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2170_, v___f_2178_, v___y_2157_, v___y_2155_, v___y_2164_, v___y_2154_, v___y_2162_, v___y_2160_, v___y_2159_, v___y_2151_, v___y_2163_, v___y_2152_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2157_);
v___y_2128_ = v___x_2179_;
goto v___jp_2127_;
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec_ref(v___y_2161_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2157_);
lean_dec(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec(v___x_2121_);
v_a_2180_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2168_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2168_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
lean_del_object(v___x_2141_);
lean_dec(v___x_2121_);
lean_dec_ref(v___y_2116_);
lean_dec(v_generation_2110_);
lean_dec_ref(v_goal_2109_);
v_a_2419_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2143_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2143_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed(lean_object* v_goal_2429_, lean_object* v_generation_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(v_goal_2429_, v_generation_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v___y_2431_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(lean_object* v_goal_2442_, lean_object* v_generation_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_){
_start:
{
lean_object* v_mvarId_2454_; lean_object* v___f_2455_; lean_object* v___x_2456_; 
v_mvarId_2454_ = lean_ctor_get(v_goal_2442_, 1);
lean_inc(v_mvarId_2454_);
v___f_2455_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed), 12, 2);
lean_closure_set(v___f_2455_, 0, v_goal_2442_);
lean_closure_set(v___f_2455_, 1, v_generation_2443_);
v___x_2456_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_2454_, v___f_2455_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2465_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2459_ = v___x_2456_;
v_isShared_2460_ = v_isSharedCheck_2465_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2456_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2465_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v_fst_2461_; lean_object* v___x_2463_; 
v_fst_2461_ = lean_ctor_get(v_a_2457_, 0);
lean_inc(v_fst_2461_);
lean_dec(v_a_2457_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v_fst_2461_);
v___x_2463_ = v___x_2459_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_fst_2461_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
v_a_2466_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2456_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2456_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___boxed(lean_object* v_goal_2474_, lean_object* v_generation_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_2474_, v_generation_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
lean_dec(v_a_2484_);
lean_dec_ref(v_a_2483_);
lean_dec(v_a_2482_);
lean_dec_ref(v_a_2481_);
lean_dec(v_a_2480_);
lean_dec_ref(v_a_2479_);
lean_dec(v_a_2478_);
lean_dec_ref(v_a_2477_);
lean_dec(v_a_2476_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(lean_object* v_mvarId_2487_, lean_object* v_val_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v___x_2500_; 
v___x_2500_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2487_, v_val_2488_, v___y_2496_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___boxed(lean_object* v_mvarId_2501_, lean_object* v_val_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(v_mvarId_2501_, v_val_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec(v___y_2503_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_2524_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___boxed(lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec(v___y_2527_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1(lean_object* v_00_u03b2_2539_, lean_object* v_x_2540_, lean_object* v_x_2541_, lean_object* v_x_2542_){
_start:
{
lean_object* v___x_2543_; 
v___x_2543_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_x_2540_, v_x_2541_, v_x_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2544_, lean_object* v_x_2545_, size_t v_x_2546_, size_t v_x_2547_, lean_object* v_x_2548_, lean_object* v_x_2549_){
_start:
{
lean_object* v___x_2550_; 
v___x_2550_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_2545_, v_x_2546_, v_x_2547_, v_x_2548_, v_x_2549_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2551_, lean_object* v_x_2552_, lean_object* v_x_2553_, lean_object* v_x_2554_, lean_object* v_x_2555_, lean_object* v_x_2556_){
_start:
{
size_t v_x_197107__boxed_2557_; size_t v_x_197108__boxed_2558_; lean_object* v_res_2559_; 
v_x_197107__boxed_2557_ = lean_unbox_usize(v_x_2553_);
lean_dec(v_x_2553_);
v_x_197108__boxed_2558_ = lean_unbox_usize(v_x_2554_);
lean_dec(v_x_2554_);
v_res_2559_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(v_00_u03b2_2551_, v_x_2552_, v_x_197107__boxed_2557_, v_x_197108__boxed_2558_, v_x_2555_, v_x_2556_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_2560_, lean_object* v_n_2561_, lean_object* v_k_2562_, lean_object* v_v_2563_){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(v_n_2561_, v_k_2562_, v_v_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2565_, size_t v_depth_2566_, lean_object* v_keys_2567_, lean_object* v_vals_2568_, lean_object* v_heq_2569_, lean_object* v_i_2570_, lean_object* v_entries_2571_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_2566_, v_keys_2567_, v_vals_2568_, v_i_2570_, v_entries_2571_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2573_, lean_object* v_depth_2574_, lean_object* v_keys_2575_, lean_object* v_vals_2576_, lean_object* v_heq_2577_, lean_object* v_i_2578_, lean_object* v_entries_2579_){
_start:
{
size_t v_depth_boxed_2580_; lean_object* v_res_2581_; 
v_depth_boxed_2580_ = lean_unbox_usize(v_depth_2574_);
lean_dec(v_depth_2574_);
v_res_2581_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(v_00_u03b2_2573_, v_depth_boxed_2580_, v_keys_2575_, v_vals_2576_, v_heq_2577_, v_i_2578_, v_entries_2579_);
lean_dec_ref(v_vals_2576_);
lean_dec_ref(v_keys_2575_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_2582_, lean_object* v_x_2583_, lean_object* v_x_2584_, lean_object* v_x_2585_, lean_object* v_x_2586_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_x_2583_, v_x_2584_, v_x_2585_, v_x_2586_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(lean_object* v_type_2588_, lean_object* v_a_2589_){
_start:
{
lean_object* v___x_2591_; 
v___x_2591_ = l_Lean_Expr_getAppFn(v_type_2588_);
if (lean_obj_tag(v___x_2591_) == 4)
{
lean_object* v_declName_2592_; lean_object* v___x_2593_; 
v_declName_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_declName_2592_);
lean_dec_ref_known(v___x_2591_, 2);
v___x_2593_ = l_Lean_Meta_Grind_isEagerSplit___redArg(v_declName_2592_, v_a_2589_);
lean_dec(v_declName_2592_);
return v___x_2593_;
}
else
{
uint8_t v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
lean_dec_ref(v___x_2591_);
v___x_2594_ = 0;
v___x_2595_ = lean_box(v___x_2594_);
v___x_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
return v___x_2596_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg___boxed(lean_object* v_type_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_2597_, v_a_2598_);
lean_dec_ref(v_a_2598_);
lean_dec_ref(v_type_2597_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(lean_object* v_type_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_){
_start:
{
lean_object* v___x_2612_; 
v___x_2612_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_2601_, v_a_2603_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___boxed(lean_object* v_type_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(v_type_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_);
lean_dec(v_a_2622_);
lean_dec_ref(v_a_2621_);
lean_dec(v_a_2620_);
lean_dec_ref(v_a_2619_);
lean_dec(v_a_2618_);
lean_dec_ref(v_a_2617_);
lean_dec(v_a_2616_);
lean_dec_ref(v_a_2615_);
lean_dec(v_a_2614_);
lean_dec_ref(v_type_2613_);
return v_res_2624_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2625_; 
v___x_2625_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2625_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2626_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
return v___x_2627_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2628_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_2629_ = lean_unsigned_to_nat(0u);
v___x_2630_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2629_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
lean_ctor_set(v___x_2630_, 2, v___x_2629_);
lean_ctor_set(v___x_2630_, 3, v___x_2629_);
lean_ctor_set(v___x_2630_, 4, v___x_2628_);
lean_ctor_set(v___x_2630_, 5, v___x_2628_);
lean_ctor_set(v___x_2630_, 6, v___x_2628_);
lean_ctor_set(v___x_2630_, 7, v___x_2628_);
lean_ctor_set(v___x_2630_, 8, v___x_2628_);
lean_ctor_set(v___x_2630_, 9, v___x_2628_);
lean_ctor_set(v___x_2630_, 10, v___x_2628_);
return v___x_2630_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2631_ = lean_unsigned_to_nat(32u);
v___x_2632_ = lean_mk_empty_array_with_capacity(v___x_2631_);
v___x_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2632_);
return v___x_2633_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2634_ = ((size_t)5ULL);
v___x_2635_ = lean_unsigned_to_nat(0u);
v___x_2636_ = lean_unsigned_to_nat(32u);
v___x_2637_ = lean_mk_empty_array_with_capacity(v___x_2636_);
v___x_2638_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_2639_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2639_, 0, v___x_2638_);
lean_ctor_set(v___x_2639_, 1, v___x_2637_);
lean_ctor_set(v___x_2639_, 2, v___x_2635_);
lean_ctor_set(v___x_2639_, 3, v___x_2635_);
lean_ctor_set_usize(v___x_2639_, 4, v___x_2634_);
return v___x_2639_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2640_ = lean_box(1);
v___x_2641_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_2642_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_2643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2642_);
lean_ctor_set(v___x_2643_, 1, v___x_2641_);
lean_ctor_set(v___x_2643_, 2, v___x_2640_);
return v___x_2643_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2645_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_2646_ = l_Lean_stringToMessageData(v___x_2645_);
return v___x_2646_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2648_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_2649_ = l_Lean_stringToMessageData(v___x_2648_);
return v___x_2649_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_2652_ = l_Lean_stringToMessageData(v___x_2651_);
return v___x_2652_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_2655_ = l_Lean_stringToMessageData(v___x_2654_);
return v___x_2655_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_2658_ = l_Lean_stringToMessageData(v___x_2657_);
return v___x_2658_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_2661_ = l_Lean_stringToMessageData(v___x_2660_);
return v___x_2661_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2663_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_2664_ = l_Lean_stringToMessageData(v___x_2663_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_2665_, lean_object* v_declHint_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v___x_2669_; lean_object* v_env_2670_; uint8_t v___x_2671_; 
v___x_2669_ = lean_st_ref_get(v___y_2667_);
v_env_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc_ref(v_env_2670_);
lean_dec(v___x_2669_);
v___x_2671_ = l_Lean_Name_isAnonymous(v_declHint_2666_);
if (v___x_2671_ == 0)
{
uint8_t v_isExporting_2672_; 
v_isExporting_2672_ = lean_ctor_get_uint8(v_env_2670_, sizeof(void*)*8);
if (v_isExporting_2672_ == 0)
{
lean_object* v___x_2673_; 
lean_dec_ref(v_env_2670_);
lean_dec(v_declHint_2666_);
v___x_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2673_, 0, v_msg_2665_);
return v___x_2673_;
}
else
{
lean_object* v___x_2674_; uint8_t v___x_2675_; 
lean_inc_ref(v_env_2670_);
v___x_2674_ = l_Lean_Environment_setExporting(v_env_2670_, v___x_2671_);
lean_inc(v_declHint_2666_);
lean_inc_ref(v___x_2674_);
v___x_2675_ = l_Lean_Environment_contains(v___x_2674_, v_declHint_2666_, v_isExporting_2672_);
if (v___x_2675_ == 0)
{
lean_object* v___x_2676_; 
lean_dec_ref(v___x_2674_);
lean_dec_ref(v_env_2670_);
lean_dec(v_declHint_2666_);
v___x_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2676_, 0, v_msg_2665_);
return v___x_2676_;
}
else
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v_c_2682_; lean_object* v___x_2683_; 
v___x_2677_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_2678_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_2679_ = l_Lean_Options_empty;
v___x_2680_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2674_);
lean_ctor_set(v___x_2680_, 1, v___x_2677_);
lean_ctor_set(v___x_2680_, 2, v___x_2678_);
lean_ctor_set(v___x_2680_, 3, v___x_2679_);
lean_inc(v_declHint_2666_);
v___x_2681_ = l_Lean_MessageData_ofConstName(v_declHint_2666_, v___x_2671_);
v_c_2682_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2682_, 0, v___x_2680_);
lean_ctor_set(v_c_2682_, 1, v___x_2681_);
v___x_2683_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2670_, v_declHint_2666_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
lean_dec_ref(v_env_2670_);
lean_dec(v_declHint_2666_);
v___x_2684_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_2685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
lean_ctor_set(v___x_2685_, 1, v_c_2682_);
v___x_2686_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_2687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2685_);
lean_ctor_set(v___x_2687_, 1, v___x_2686_);
v___x_2688_ = l_Lean_MessageData_note(v___x_2687_);
v___x_2689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2689_, 0, v_msg_2665_);
lean_ctor_set(v___x_2689_, 1, v___x_2688_);
v___x_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
return v___x_2690_;
}
else
{
lean_object* v_val_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2726_; 
v_val_2691_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2693_ = v___x_2683_;
v_isShared_2694_ = v_isSharedCheck_2726_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_val_2691_);
lean_dec(v___x_2683_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2726_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v_mod_2698_; uint8_t v___x_2699_; 
v___x_2695_ = lean_box(0);
v___x_2696_ = l_Lean_Environment_header(v_env_2670_);
lean_dec_ref(v_env_2670_);
v___x_2697_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2696_);
v_mod_2698_ = lean_array_get(v___x_2695_, v___x_2697_, v_val_2691_);
lean_dec(v_val_2691_);
lean_dec_ref(v___x_2697_);
v___x_2699_ = l_Lean_isPrivateName(v_declHint_2666_);
lean_dec(v_declHint_2666_);
if (v___x_2699_ == 0)
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2711_; 
v___x_2700_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_2701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
lean_ctor_set(v___x_2701_, 1, v_c_2682_);
v___x_2702_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_2703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2701_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = l_Lean_MessageData_ofName(v_mod_2698_);
v___x_2705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2703_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
v___x_2706_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_2707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2705_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
v___x_2708_ = l_Lean_MessageData_note(v___x_2707_);
v___x_2709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2709_, 0, v_msg_2665_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set_tag(v___x_2693_, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2709_);
v___x_2711_ = v___x_2693_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2709_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
else
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2713_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_2714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
lean_ctor_set(v___x_2714_, 1, v_c_2682_);
v___x_2715_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_2716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2714_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
v___x_2717_ = l_Lean_MessageData_ofName(v_mod_2698_);
v___x_2718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2716_);
lean_ctor_set(v___x_2718_, 1, v___x_2717_);
v___x_2719_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_2720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2718_);
lean_ctor_set(v___x_2720_, 1, v___x_2719_);
v___x_2721_ = l_Lean_MessageData_note(v___x_2720_);
v___x_2722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2722_, 0, v_msg_2665_);
lean_ctor_set(v___x_2722_, 1, v___x_2721_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set_tag(v___x_2693_, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2722_);
v___x_2724_ = v___x_2693_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2727_; 
lean_dec_ref(v_env_2670_);
lean_dec(v_declHint_2666_);
v___x_2727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2727_, 0, v_msg_2665_);
return v___x_2727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_2728_, lean_object* v_declHint_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2728_, v_declHint_2729_, v___y_2730_);
lean_dec(v___y_2730_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_2733_, lean_object* v_declHint_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v___x_2738_; lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2748_; 
v___x_2738_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2733_, v_declHint_2734_, v___y_2736_);
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2741_ = v___x_2738_;
v_isShared_2742_ = v_isSharedCheck_2748_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2738_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2748_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2746_; 
v___x_2743_ = l_Lean_unknownIdentifierMessageTag;
v___x_2744_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
lean_ctor_set(v___x_2744_, 1, v_a_2739_);
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 0, v___x_2744_);
v___x_2746_ = v___x_2741_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v___x_2744_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_2749_, lean_object* v_declHint_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2749_, v_declHint_2750_, v___y_2751_, v___y_2752_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msgData_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v___x_2759_; lean_object* v_env_2760_; lean_object* v_options_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2759_ = lean_st_ref_get(v___y_2757_);
v_env_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc_ref(v_env_2760_);
lean_dec(v___x_2759_);
v_options_2761_ = lean_ctor_get(v___y_2756_, 2);
v___x_2762_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_2763_ = lean_unsigned_to_nat(32u);
v___x_2764_ = lean_mk_empty_array_with_capacity(v___x_2763_);
lean_dec_ref(v___x_2764_);
v___x_2765_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
lean_inc_ref(v_options_2761_);
v___x_2766_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2766_, 0, v_env_2760_);
lean_ctor_set(v___x_2766_, 1, v___x_2762_);
lean_ctor_set(v___x_2766_, 2, v___x_2765_);
lean_ctor_set(v___x_2766_, 3, v_options_2761_);
v___x_2767_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
lean_ctor_set(v___x_2767_, 1, v_msgData_2755_);
v___x_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msgData_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_2769_, v___y_2770_, v___y_2771_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_msg_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_ref_2778_; lean_object* v___x_2779_; lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2788_; 
v_ref_2778_ = lean_ctor_get(v___y_2775_, 5);
v___x_2779_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_2774_, v___y_2775_, v___y_2776_);
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2782_ = v___x_2779_;
v_isShared_2783_ = v_isSharedCheck_2788_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2779_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2788_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2784_; lean_object* v___x_2786_; 
lean_inc(v_ref_2778_);
v___x_2784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2784_, 0, v_ref_2778_);
lean_ctor_set(v___x_2784_, 1, v_a_2780_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set_tag(v___x_2782_, 1);
lean_ctor_set(v___x_2782_, 0, v___x_2784_);
v___x_2786_ = v___x_2782_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2784_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_msg_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2789_, v___y_2790_, v___y_2791_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_2794_, lean_object* v_msg_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v_fileName_2799_; lean_object* v_fileMap_2800_; lean_object* v_options_2801_; lean_object* v_currRecDepth_2802_; lean_object* v_maxRecDepth_2803_; lean_object* v_ref_2804_; lean_object* v_currNamespace_2805_; lean_object* v_openDecls_2806_; lean_object* v_initHeartbeats_2807_; lean_object* v_maxHeartbeats_2808_; lean_object* v_quotContext_2809_; lean_object* v_currMacroScope_2810_; uint8_t v_diag_2811_; lean_object* v_cancelTk_x3f_2812_; uint8_t v_suppressElabErrors_2813_; lean_object* v_inheritedTraceOptions_2814_; lean_object* v_ref_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v_fileName_2799_ = lean_ctor_get(v___y_2796_, 0);
v_fileMap_2800_ = lean_ctor_get(v___y_2796_, 1);
v_options_2801_ = lean_ctor_get(v___y_2796_, 2);
v_currRecDepth_2802_ = lean_ctor_get(v___y_2796_, 3);
v_maxRecDepth_2803_ = lean_ctor_get(v___y_2796_, 4);
v_ref_2804_ = lean_ctor_get(v___y_2796_, 5);
v_currNamespace_2805_ = lean_ctor_get(v___y_2796_, 6);
v_openDecls_2806_ = lean_ctor_get(v___y_2796_, 7);
v_initHeartbeats_2807_ = lean_ctor_get(v___y_2796_, 8);
v_maxHeartbeats_2808_ = lean_ctor_get(v___y_2796_, 9);
v_quotContext_2809_ = lean_ctor_get(v___y_2796_, 10);
v_currMacroScope_2810_ = lean_ctor_get(v___y_2796_, 11);
v_diag_2811_ = lean_ctor_get_uint8(v___y_2796_, sizeof(void*)*14);
v_cancelTk_x3f_2812_ = lean_ctor_get(v___y_2796_, 12);
v_suppressElabErrors_2813_ = lean_ctor_get_uint8(v___y_2796_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2814_ = lean_ctor_get(v___y_2796_, 13);
v_ref_2815_ = l_Lean_replaceRef(v_ref_2794_, v_ref_2804_);
lean_inc_ref(v_inheritedTraceOptions_2814_);
lean_inc(v_cancelTk_x3f_2812_);
lean_inc(v_currMacroScope_2810_);
lean_inc(v_quotContext_2809_);
lean_inc(v_maxHeartbeats_2808_);
lean_inc(v_initHeartbeats_2807_);
lean_inc(v_openDecls_2806_);
lean_inc(v_currNamespace_2805_);
lean_inc(v_maxRecDepth_2803_);
lean_inc(v_currRecDepth_2802_);
lean_inc_ref(v_options_2801_);
lean_inc_ref(v_fileMap_2800_);
lean_inc_ref(v_fileName_2799_);
v___x_2816_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2816_, 0, v_fileName_2799_);
lean_ctor_set(v___x_2816_, 1, v_fileMap_2800_);
lean_ctor_set(v___x_2816_, 2, v_options_2801_);
lean_ctor_set(v___x_2816_, 3, v_currRecDepth_2802_);
lean_ctor_set(v___x_2816_, 4, v_maxRecDepth_2803_);
lean_ctor_set(v___x_2816_, 5, v_ref_2815_);
lean_ctor_set(v___x_2816_, 6, v_currNamespace_2805_);
lean_ctor_set(v___x_2816_, 7, v_openDecls_2806_);
lean_ctor_set(v___x_2816_, 8, v_initHeartbeats_2807_);
lean_ctor_set(v___x_2816_, 9, v_maxHeartbeats_2808_);
lean_ctor_set(v___x_2816_, 10, v_quotContext_2809_);
lean_ctor_set(v___x_2816_, 11, v_currMacroScope_2810_);
lean_ctor_set(v___x_2816_, 12, v_cancelTk_x3f_2812_);
lean_ctor_set(v___x_2816_, 13, v_inheritedTraceOptions_2814_);
lean_ctor_set_uint8(v___x_2816_, sizeof(void*)*14, v_diag_2811_);
lean_ctor_set_uint8(v___x_2816_, sizeof(void*)*14 + 1, v_suppressElabErrors_2813_);
v___x_2817_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2795_, v___x_2816_, v___y_2797_);
lean_dec_ref_known(v___x_2816_, 14);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_2818_, lean_object* v_msg_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2818_, v_msg_2819_, v___y_2820_, v___y_2821_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v_ref_2818_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_2824_, lean_object* v_msg_2825_, lean_object* v_declHint_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v___x_2830_; lean_object* v_a_2831_; lean_object* v___x_2832_; 
v___x_2830_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2825_, v_declHint_2826_, v___y_2827_, v___y_2828_);
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref(v___x_2830_);
v___x_2832_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2824_, v_a_2831_, v___y_2827_, v___y_2828_);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_2833_, lean_object* v_msg_2834_, lean_object* v_declHint_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2833_, v_msg_2834_, v_declHint_2835_, v___y_2836_, v___y_2837_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v_ref_2833_);
return v_res_2839_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2841_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2842_ = l_Lean_stringToMessageData(v___x_2841_);
return v___x_2842_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2844_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_2845_ = l_Lean_stringToMessageData(v___x_2844_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2846_, lean_object* v_constName_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
lean_object* v___x_2851_; uint8_t v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2851_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2852_ = 0;
lean_inc(v_constName_2847_);
v___x_2853_ = l_Lean_MessageData_ofConstName(v_constName_2847_, v___x_2852_);
v___x_2854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2851_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
v___x_2855_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_2856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2854_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
v___x_2857_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2846_, v___x_2856_, v_constName_2847_, v___y_2848_, v___y_2849_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2858_, lean_object* v_constName_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_2858_, v_constName_2859_, v___y_2860_, v___y_2861_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec(v_ref_2858_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(lean_object* v_constName_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
lean_object* v_ref_2868_; lean_object* v___x_2869_; 
v_ref_2868_ = lean_ctor_get(v___y_2865_, 5);
v___x_2869_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_2868_, v_constName_2864_, v___y_2865_, v___y_2866_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_2870_, v___y_2871_, v___y_2872_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(lean_object* v_constName_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v___x_2879_; lean_object* v_env_2880_; uint8_t v___x_2881_; lean_object* v___x_2882_; 
v___x_2879_ = lean_st_ref_get(v___y_2877_);
v_env_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc_ref(v_env_2880_);
lean_dec(v___x_2879_);
v___x_2881_ = 0;
lean_inc(v_constName_2875_);
v___x_2882_ = l_Lean_Environment_find_x3f(v_env_2880_, v_constName_2875_, v___x_2881_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_2875_, v___y_2876_, v___y_2877_);
return v___x_2883_;
}
else
{
lean_object* v_val_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
lean_dec(v_constName_2875_);
v_val_2884_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2882_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_val_2884_);
lean_dec(v___x_2882_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
lean_ctor_set_tag(v___x_2886_, 0);
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_val_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0___boxed(lean_object* v_constName_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_constName_2892_, v___y_2893_, v___y_2894_);
lean_dec(v___y_2894_);
lean_dec_ref(v___y_2893_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(lean_object* v_type_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_){
_start:
{
lean_object* v___x_2901_; 
v___x_2901_ = l_Lean_Expr_getAppFn(v_type_2897_);
if (lean_obj_tag(v___x_2901_) == 4)
{
lean_object* v_declName_2902_; lean_object* v___x_2903_; 
v_declName_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_declName_2902_);
lean_dec_ref_known(v___x_2901_, 2);
v___x_2903_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_declName_2902_, v_a_2898_, v_a_2899_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2921_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2906_ = v___x_2903_;
v_isShared_2907_ = v_isSharedCheck_2921_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2903_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2921_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
if (lean_obj_tag(v_a_2904_) == 5)
{
lean_object* v_val_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; uint8_t v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2914_; 
v_val_2908_ = lean_ctor_get(v_a_2904_, 0);
lean_inc_ref(v_val_2908_);
lean_dec_ref_known(v_a_2904_, 1);
v___x_2909_ = l_Lean_InductiveVal_numCtors(v_val_2908_);
lean_dec_ref(v_val_2908_);
v___x_2910_ = lean_unsigned_to_nat(1u);
v___x_2911_ = lean_nat_dec_le(v___x_2909_, v___x_2910_);
lean_dec(v___x_2909_);
v___x_2912_ = lean_box(v___x_2911_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v___x_2912_);
v___x_2914_ = v___x_2906_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2912_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
else
{
uint8_t v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2919_; 
lean_dec(v_a_2904_);
v___x_2916_ = 0;
v___x_2917_ = lean_box(v___x_2916_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v___x_2917_);
v___x_2919_ = v___x_2906_;
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
}
}
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
v_a_2922_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2903_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2903_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
else
{
uint8_t v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
lean_dec_ref(v___x_2901_);
v___x_2930_ = 0;
v___x_2931_ = lean_box(v___x_2930_);
v___x_2932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2931_);
return v___x_2932_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive___boxed(lean_object* v_type_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_type_2933_, v_a_2934_, v_a_2935_);
lean_dec(v_a_2935_);
lean_dec_ref(v_a_2934_);
lean_dec_ref(v_type_2933_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(lean_object* v_00_u03b1_2938_, lean_object* v_constName_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v___x_2943_; 
v___x_2943_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_2939_, v___y_2940_, v___y_2941_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2944_, lean_object* v_constName_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(v_00_u03b1_2944_, v_constName_2945_, v___y_2946_, v___y_2947_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2950_, lean_object* v_ref_2951_, lean_object* v_constName_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_2951_, v_constName_2952_, v___y_2953_, v___y_2954_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2957_, lean_object* v_ref_2958_, lean_object* v_constName_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(v_00_u03b1_2957_, v_ref_2958_, v_constName_2959_, v___y_2960_, v___y_2961_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v_ref_2958_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2964_, lean_object* v_ref_2965_, lean_object* v_msg_2966_, lean_object* v_declHint_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2965_, v_msg_2966_, v_declHint_2967_, v___y_2968_, v___y_2969_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2972_, lean_object* v_ref_2973_, lean_object* v_msg_2974_, lean_object* v_declHint_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2972_, v_ref_2973_, v_msg_2974_, v_declHint_2975_, v___y_2976_, v___y_2977_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v_ref_2973_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_2980_, lean_object* v_declHint_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v___x_2985_; 
v___x_2985_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2980_, v_declHint_2981_, v___y_2983_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_2986_, lean_object* v_declHint_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2986_, v_declHint_2987_, v___y_2988_, v___y_2989_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_2992_, lean_object* v_ref_2993_, lean_object* v_msg_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2993_, v_msg_2994_, v___y_2995_, v___y_2996_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2999_, lean_object* v_ref_3000_, lean_object* v_msg_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_2999_, v_ref_3000_, v_msg_3001_, v___y_3002_, v___y_3003_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec(v_ref_3000_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_3006_, lean_object* v_msg_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_3007_, v___y_3008_, v___y_3009_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_3012_, lean_object* v_msg_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_3012_, v_msg_3013_, v___y_3014_, v___y_3015_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(lean_object* v_goal_3018_, lean_object* v_fvarId_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_){
_start:
{
lean_object* v_toGoalState_3025_; lean_object* v_mvarId_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3062_; 
v_toGoalState_3025_ = lean_ctor_get(v_goal_3018_, 0);
v_mvarId_3026_ = lean_ctor_get(v_goal_3018_, 1);
v_isSharedCheck_3062_ = !lean_is_exclusive(v_goal_3018_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3028_ = v_goal_3018_;
v_isShared_3029_ = v_isSharedCheck_3062_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_mvarId_3026_);
lean_inc(v_toGoalState_3025_);
lean_dec(v_goal_3018_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3062_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3030_; 
v___x_3030_ = l_Lean_Meta_Grind_injection_x3f(v_mvarId_3026_, v_fvarId_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3053_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3033_ = v___x_3030_;
v_isShared_3034_ = v_isSharedCheck_3053_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3030_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3053_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
if (lean_obj_tag(v_a_3031_) == 1)
{
lean_object* v_val_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3048_; 
v_val_3035_ = lean_ctor_get(v_a_3031_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v_a_3031_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3037_ = v_a_3031_;
v_isShared_3038_ = v_isSharedCheck_3048_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_val_3035_);
lean_dec(v_a_3031_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3048_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 1, v_val_3035_);
v___x_3040_ = v___x_3028_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_toGoalState_3025_);
lean_ctor_set(v_reuseFailAlloc_3047_, 1, v_val_3035_);
v___x_3040_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3042_; 
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 0, v___x_3040_);
v___x_3042_ = v___x_3037_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3040_);
v___x_3042_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3044_; 
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 0, v___x_3042_);
v___x_3044_ = v___x_3033_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3042_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
}
}
else
{
lean_object* v___x_3049_; lean_object* v___x_3051_; 
lean_dec(v_a_3031_);
lean_del_object(v___x_3028_);
lean_dec_ref(v_toGoalState_3025_);
v___x_3049_ = lean_box(0);
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 0, v___x_3049_);
v___x_3051_ = v___x_3033_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3049_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
lean_del_object(v___x_3028_);
lean_dec_ref(v_toGoalState_3025_);
v_a_3054_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_3030_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3030_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f___boxed(lean_object* v_goal_3063_, lean_object* v_fvarId_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_3063_, v_fvarId_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(lean_object* v_mvarId_3071_, lean_object* v_x_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v___x_3078_; 
v___x_3078_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3071_, v_x_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_3078_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3078_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
v_a_3087_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_3078_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3078_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg___boxed(lean_object* v_mvarId_3095_, lean_object* v_x_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3095_, v_x_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(lean_object* v_00_u03b1_3103_, lean_object* v_mvarId_3104_, lean_object* v_x_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
lean_object* v___x_3111_; 
v___x_3111_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3104_, v_x_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___boxed(lean_object* v_00_u03b1_3112_, lean_object* v_mvarId_3113_, lean_object* v_x_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(v_00_u03b1_3112_, v_mvarId_3113_, v_x_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(lean_object* v_mvarId_3121_, lean_object* v_toGoalState_3122_, lean_object* v_goal_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
lean_object* v___x_3129_; 
lean_inc(v_mvarId_3121_);
v___x_3129_ = l_Lean_MVarId_getType(v_mvarId_3121_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
if (lean_obj_tag(v___x_3129_) == 0)
{
lean_object* v_a_3130_; lean_object* v___x_3131_; 
v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
lean_inc(v_a_3130_);
lean_dec_ref_known(v___x_3129_, 1);
v___x_3131_ = l_Lean_Meta_isProp(v_a_3130_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3158_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3134_ = v___x_3131_;
v_isShared_3135_ = v_isSharedCheck_3158_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3131_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3158_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
uint8_t v___x_3136_; 
v___x_3136_ = lean_unbox(v_a_3132_);
lean_dec(v_a_3132_);
if (v___x_3136_ == 0)
{
lean_object* v___x_3137_; 
lean_del_object(v___x_3134_);
lean_dec_ref(v_goal_3123_);
v___x_3137_ = l_Lean_MVarId_exfalso(v_mvarId_3121_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3146_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3140_ = v___x_3137_;
v_isShared_3141_ = v_isSharedCheck_3146_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3137_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3146_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3142_; lean_object* v___x_3144_; 
v___x_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3142_, 0, v_toGoalState_3122_);
lean_ctor_set(v___x_3142_, 1, v_a_3138_);
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 0, v___x_3142_);
v___x_3144_ = v___x_3140_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3142_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
lean_dec_ref(v_toGoalState_3122_);
v_a_3147_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3137_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3137_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
else
{
lean_object* v___x_3156_; 
lean_dec_ref(v_toGoalState_3122_);
lean_dec(v_mvarId_3121_);
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 0, v_goal_3123_);
v___x_3156_ = v___x_3134_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_goal_3123_);
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
else
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
lean_dec_ref(v_goal_3123_);
lean_dec_ref(v_toGoalState_3122_);
lean_dec(v_mvarId_3121_);
v_a_3159_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v___x_3131_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3131_);
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
else
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
lean_dec_ref(v_goal_3123_);
lean_dec_ref(v_toGoalState_3122_);
lean_dec(v_mvarId_3121_);
v_a_3167_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3169_ = v___x_3129_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3129_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed(lean_object* v_mvarId_3175_, lean_object* v_toGoalState_3176_, lean_object* v_goal_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(v_mvarId_3175_, v_toGoalState_3176_, v_goal_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(lean_object* v_goal_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_){
_start:
{
lean_object* v_toGoalState_3190_; lean_object* v_mvarId_3191_; lean_object* v___f_3192_; lean_object* v___x_3193_; 
v_toGoalState_3190_ = lean_ctor_get(v_goal_3184_, 0);
lean_inc_ref(v_toGoalState_3190_);
v_mvarId_3191_ = lean_ctor_get(v_goal_3184_, 1);
lean_inc_n(v_mvarId_3191_, 2);
v___f_3192_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3192_, 0, v_mvarId_3191_);
lean_closure_set(v___f_3192_, 1, v_toGoalState_3190_);
lean_closure_set(v___f_3192_, 2, v_goal_3184_);
v___x_3193_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3191_, v___f_3192_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_);
return v___x_3193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___boxed(lean_object* v_goal_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_){
_start:
{
lean_object* v_res_3200_; 
v_res_3200_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_);
lean_dec(v_a_3198_);
lean_dec_ref(v_a_3197_);
lean_dec(v_a_3196_);
lean_dec_ref(v_a_3195_);
return v_res_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f(lean_object* v_goal_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_){
_start:
{
lean_object* v_mvarId_3207_; lean_object* v___x_3208_; 
v_mvarId_3207_ = lean_ctor_get(v_goal_3201_, 1);
lean_inc(v_mvarId_3207_);
lean_dec_ref(v_goal_3201_);
v___x_3208_ = l_Lean_MVarId_getDecl(v_mvarId_3207_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3218_; 
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3211_ = v___x_3208_;
v_isShared_3212_ = v_isSharedCheck_3218_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3208_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3218_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v_lctx_3213_; lean_object* v___x_3214_; lean_object* v___x_3216_; 
v_lctx_3213_ = lean_ctor_get(v_a_3209_, 1);
lean_inc_ref(v_lctx_3213_);
lean_dec(v_a_3209_);
v___x_3214_ = l_Lean_LocalContext_lastDecl(v_lctx_3213_);
lean_dec_ref(v_lctx_3213_);
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 0, v___x_3214_);
v___x_3216_ = v___x_3211_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v___x_3214_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
v_a_3219_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3208_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3208_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f___boxed(lean_object* v_goal_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l_Lean_Meta_Grind_Goal_lastDecl_x3f(v_goal_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_);
lean_dec(v_a_3231_);
lean_dec_ref(v_a_3230_);
lean_dec(v_a_3229_);
lean_dec_ref(v_a_3228_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(lean_object* v_goal_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_){
_start:
{
if (lean_obj_tag(v_a_3235_) == 0)
{
lean_object* v___x_3237_; 
v___x_3237_ = l_List_reverse___redArg(v_a_3236_);
return v___x_3237_;
}
else
{
lean_object* v_head_3238_; lean_object* v_tail_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3249_; 
v_head_3238_ = lean_ctor_get(v_a_3235_, 0);
v_tail_3239_ = lean_ctor_get(v_a_3235_, 1);
v_isSharedCheck_3249_ = !lean_is_exclusive(v_a_3235_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3241_ = v_a_3235_;
v_isShared_3242_ = v_isSharedCheck_3249_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_tail_3239_);
lean_inc(v_head_3238_);
lean_dec(v_a_3235_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3249_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v_toGoalState_3243_; lean_object* v___x_3244_; lean_object* v___x_3246_; 
v_toGoalState_3243_ = lean_ctor_get(v_goal_3234_, 0);
lean_inc_ref(v_toGoalState_3243_);
v___x_3244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3244_, 0, v_toGoalState_3243_);
lean_ctor_set(v___x_3244_, 1, v_head_3238_);
if (v_isShared_3242_ == 0)
{
lean_ctor_set(v___x_3241_, 1, v_a_3236_);
lean_ctor_set(v___x_3241_, 0, v___x_3244_);
v___x_3246_ = v___x_3241_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3244_);
lean_ctor_set(v_reuseFailAlloc_3248_, 1, v_a_3236_);
v___x_3246_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
v_a_3235_ = v_tail_3239_;
v_a_3236_ = v___x_3246_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0___boxed(lean_object* v_goal_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_){
_start:
{
lean_object* v_res_3253_; 
v_res_3253_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v_goal_3250_, v_a_3251_, v_a_3252_);
lean_dec_ref(v_goal_3250_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(lean_object* v_kp_3254_, lean_object* v_as_x27_3255_, lean_object* v_b_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
if (lean_obj_tag(v_as_x27_3255_) == 0)
{
lean_object* v___x_3267_; 
lean_dec_ref(v_kp_3254_);
v___x_3267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3267_, 0, v_b_3256_);
return v___x_3267_;
}
else
{
lean_object* v_head_3268_; lean_object* v_tail_3269_; lean_object* v___x_3270_; 
v_head_3268_ = lean_ctor_get(v_as_x27_3255_, 0);
v_tail_3269_ = lean_ctor_get(v_as_x27_3255_, 1);
lean_inc_ref(v_kp_3254_);
lean_inc(v___y_3265_);
lean_inc_ref(v___y_3264_);
lean_inc(v___y_3263_);
lean_inc_ref(v___y_3262_);
lean_inc(v___y_3261_);
lean_inc_ref(v___y_3260_);
lean_inc(v___y_3259_);
lean_inc_ref(v___y_3258_);
lean_inc(v___y_3257_);
lean_inc(v_head_3268_);
v___x_3270_ = lean_apply_11(v_kp_3254_, v_head_3268_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, lean_box(0));
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3271_);
lean_dec_ref_known(v___x_3270_, 1);
if (lean_obj_tag(v_a_3271_) == 0)
{
lean_object* v_fst_3272_; lean_object* v_snd_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3283_; 
v_fst_3272_ = lean_ctor_get(v_b_3256_, 0);
v_snd_3273_ = lean_ctor_get(v_b_3256_, 1);
v_isSharedCheck_3283_ = !lean_is_exclusive(v_b_3256_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3275_ = v_b_3256_;
v_isShared_3276_ = v_isSharedCheck_3283_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_snd_3273_);
lean_inc(v_fst_3272_);
lean_dec(v_b_3256_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3283_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v_seq_3277_; lean_object* v___x_3278_; lean_object* v___x_3280_; 
v_seq_3277_ = lean_ctor_get(v_a_3271_, 0);
lean_inc(v_seq_3277_);
lean_dec_ref_known(v_a_3271_, 1);
v___x_3278_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_fst_3272_, v_seq_3277_);
if (v_isShared_3276_ == 0)
{
lean_ctor_set(v___x_3275_, 0, v___x_3278_);
v___x_3280_ = v___x_3275_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v___x_3278_);
lean_ctor_set(v_reuseFailAlloc_3282_, 1, v_snd_3273_);
v___x_3280_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
v_as_x27_3255_ = v_tail_3269_;
v_b_3256_ = v___x_3280_;
goto _start;
}
}
}
else
{
lean_object* v_fst_3284_; lean_object* v_snd_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3295_; 
v_fst_3284_ = lean_ctor_get(v_b_3256_, 0);
v_snd_3285_ = lean_ctor_get(v_b_3256_, 1);
v_isSharedCheck_3295_ = !lean_is_exclusive(v_b_3256_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3287_ = v_b_3256_;
v_isShared_3288_ = v_isSharedCheck_3295_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_snd_3285_);
lean_inc(v_fst_3284_);
lean_dec(v_b_3256_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3295_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v_gs_3289_; lean_object* v___x_3290_; lean_object* v___x_3292_; 
v_gs_3289_ = lean_ctor_get(v_a_3271_, 0);
lean_inc(v_gs_3289_);
lean_dec_ref_known(v_a_3271_, 1);
v___x_3290_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_snd_3285_, v_gs_3289_);
if (v_isShared_3288_ == 0)
{
lean_ctor_set(v___x_3287_, 1, v___x_3290_);
v___x_3292_ = v___x_3287_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_fst_3284_);
lean_ctor_set(v_reuseFailAlloc_3294_, 1, v___x_3290_);
v___x_3292_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
v_as_x27_3255_ = v_tail_3269_;
v_b_3256_ = v___x_3292_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3303_; 
lean_dec_ref(v_b_3256_);
lean_dec_ref(v_kp_3254_);
v_a_3296_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3298_ = v___x_3270_;
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3270_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3301_; 
if (v_isShared_3299_ == 0)
{
v___x_3301_ = v___x_3298_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3296_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg___boxed(lean_object* v_kp_3304_, lean_object* v_as_x27_3305_, lean_object* v_b_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3304_, v_as_x27_3305_, v_b_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec(v_as_x27_3305_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(lean_object* v_fvarId_3322_, lean_object* v_mvarId_3323_, lean_object* v_goal_3324_, lean_object* v_kp_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___x_3391_; 
lean_inc(v_fvarId_3322_);
v___x_3391_ = l_Lean_FVarId_getType___redArg(v_fvarId_3322_, v___y_3331_, v___y_3333_, v___y_3334_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; lean_object* v___x_3393_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_a_3392_);
lean_dec_ref_known(v___x_3391_, 1);
lean_inc(v___y_3334_);
lean_inc_ref(v___y_3333_);
lean_inc(v___y_3332_);
lean_inc_ref(v___y_3331_);
v___x_3393_ = lean_whnf(v_a_3392_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___x_3416_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
lean_inc(v_a_3394_);
lean_dec_ref_known(v___x_3393_, 1);
v___x_3416_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_a_3394_, v___y_3327_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3456_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3419_ = v___x_3416_;
v_isShared_3420_ = v_isSharedCheck_3456_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3416_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3456_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
uint8_t v___x_3421_; 
v___x_3421_ = lean_unbox(v_a_3417_);
lean_dec(v_a_3417_);
if (v___x_3421_ == 0)
{
lean_object* v___x_3422_; lean_object* v___x_3424_; 
lean_dec(v_a_3394_);
lean_dec_ref(v_kp_3325_);
lean_dec(v_mvarId_3323_);
lean_dec(v_fvarId_3322_);
v___x_3422_ = lean_box(0);
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v___x_3422_);
v___x_3424_ = v___x_3419_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3422_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
else
{
lean_object* v___x_3426_; 
lean_del_object(v___x_3419_);
v___x_3426_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3327_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v_a_3427_; uint8_t v___x_3428_; 
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
lean_inc(v_a_3427_);
lean_dec_ref_known(v___x_3426_, 1);
v___x_3428_ = lean_unbox(v_a_3427_);
lean_dec(v_a_3427_);
if (v___x_3428_ == 0)
{
v___y_3396_ = v___y_3326_;
v___y_3397_ = v___y_3327_;
v___y_3398_ = v___y_3328_;
v___y_3399_ = v___y_3329_;
v___y_3400_ = v___y_3330_;
v___y_3401_ = v___y_3331_;
v___y_3402_ = v___y_3332_;
v___y_3403_ = v___y_3333_;
v___y_3404_ = v___y_3334_;
goto v___jp_3395_;
}
else
{
lean_object* v___x_3429_; 
v___x_3429_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_a_3394_, v___y_3333_, v___y_3334_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3439_; 
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3432_ = v___x_3429_;
v_isShared_3433_ = v_isSharedCheck_3439_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3429_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3439_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
uint8_t v___x_3434_; 
v___x_3434_ = lean_unbox(v_a_3430_);
lean_dec(v_a_3430_);
if (v___x_3434_ == 0)
{
lean_object* v___x_3435_; lean_object* v___x_3437_; 
lean_dec(v_a_3394_);
lean_dec_ref(v_kp_3325_);
lean_dec(v_mvarId_3323_);
lean_dec(v_fvarId_3322_);
v___x_3435_ = lean_box(0);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 0, v___x_3435_);
v___x_3437_ = v___x_3432_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v___x_3435_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
else
{
lean_del_object(v___x_3432_);
v___y_3396_ = v___y_3326_;
v___y_3397_ = v___y_3327_;
v___y_3398_ = v___y_3328_;
v___y_3399_ = v___y_3329_;
v___y_3400_ = v___y_3330_;
v___y_3401_ = v___y_3331_;
v___y_3402_ = v___y_3332_;
v___y_3403_ = v___y_3333_;
v___y_3404_ = v___y_3334_;
goto v___jp_3395_;
}
}
}
else
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3447_; 
lean_dec(v_a_3394_);
lean_dec_ref(v_kp_3325_);
lean_dec(v_mvarId_3323_);
lean_dec(v_fvarId_3322_);
v_a_3440_ = lean_ctor_get(v___x_3429_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3442_ = v___x_3429_;
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3429_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3440_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
}
else
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3455_; 
lean_dec(v_a_3394_);
lean_dec_ref(v_kp_3325_);
lean_dec(v_mvarId_3323_);
lean_dec(v_fvarId_3322_);
v_a_3448_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3450_ = v___x_3426_;
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3426_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
}
}
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
lean_dec(v_a_3394_);
lean_dec_ref(v_kp_3325_);
lean_dec(v_mvarId_3323_);
lean_dec(v_fvarId_3322_);
v_a_3457_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3416_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3416_);
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
v___jp_3395_:
{
lean_object* v___x_3405_; 
v___x_3405_ = l_Lean_Expr_getAppFn(v_a_3394_);
lean_dec(v_a_3394_);
if (lean_obj_tag(v___x_3405_) == 4)
{
lean_object* v_declName_3406_; lean_object* v___x_3407_; 
v_declName_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_declName_3406_);
lean_dec_ref_known(v___x_3405_, 2);
v___x_3407_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3406_, v___y_3398_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_dec_ref_known(v___x_3407_, 1);
v___y_3337_ = v___y_3396_;
v___y_3338_ = v___y_3397_;
v___y_3339_ = v___y_3398_;
v___y_3340_ = v___y_3399_;
v___y_3341_ = v___y_3400_;
v___y_3342_ = v___y_3401_;
v___y_3343_ = v___y_3402_;
v___y_3344_ = v___y_3403_;
v___y_3345_ = v___y_3404_;
goto v___jp_3336_;
}
else
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
lean_dec_ref(v_kp_3325_);
lean_dec(v_mvarId_3323_);
lean_dec(v_fvarId_3322_);
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___x_3407_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3407_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
else
{
lean_dec_ref(v___x_3405_);
v___y_3337_ = v___y_3396_;
v___y_3338_ = v___y_3397_;
v___y_3339_ = v___y_3398_;
v___y_3340_ = v___y_3399_;
v___y_3341_ = v___y_3400_;
v___y_3342_ = v___y_3401_;
v___y_3343_ = v___y_3402_;
v___y_3344_ = v___y_3403_;
v___y_3345_ = v___y_3404_;
goto v___jp_3336_;
}
}
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
lean_dec_ref(v_kp_3325_);
lean_dec(v_mvarId_3323_);
lean_dec(v_fvarId_3322_);
v_a_3465_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3393_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3393_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
lean_dec_ref(v_kp_3325_);
lean_dec(v_mvarId_3323_);
lean_dec(v_fvarId_3322_);
v_a_3473_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3391_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3391_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
v___jp_3336_:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = l_Lean_mkFVar(v_fvarId_3322_);
v___x_3347_ = l_Lean_Meta_Grind_cases(v_mvarId_3323_, v___x_3346_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3348_);
lean_dec_ref_known(v___x_3347_, 1);
v___x_3349_ = lean_box(0);
v___x_3350_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v_goal_3324_, v_a_3348_, v___x_3349_);
v___x_3351_ = lean_unsigned_to_nat(0u);
v___x_3352_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__1));
v___x_3353_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3325_, v___x_3350_, v___x_3352_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
lean_dec(v___x_3350_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3374_; 
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3356_ = v___x_3353_;
v_isShared_3357_ = v_isSharedCheck_3374_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3353_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3374_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v_fst_3358_; lean_object* v_snd_3359_; lean_object* v___x_3360_; uint8_t v___x_3361_; 
v_fst_3358_ = lean_ctor_get(v_a_3354_, 0);
lean_inc(v_fst_3358_);
v_snd_3359_ = lean_ctor_get(v_a_3354_, 1);
lean_inc(v_snd_3359_);
lean_dec(v_a_3354_);
v___x_3360_ = lean_array_get_size(v_snd_3359_);
v___x_3361_ = lean_nat_dec_eq(v___x_3360_, v___x_3351_);
if (v___x_3361_ == 0)
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3366_; 
lean_dec(v_fst_3358_);
v___x_3362_ = lean_array_to_list(v_snd_3359_);
v___x_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3362_);
v___x_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 0, v___x_3364_);
v___x_3366_ = v___x_3356_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v___x_3364_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
else
{
lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3372_; 
lean_dec(v_snd_3359_);
v___x_3368_ = lean_array_to_list(v_fst_3358_);
v___x_3369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
v___x_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3369_);
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 0, v___x_3370_);
v___x_3372_ = v___x_3356_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3370_);
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
else
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
v_a_3375_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3353_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3353_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
else
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3390_; 
lean_dec_ref(v_kp_3325_);
v_a_3383_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3385_ = v___x_3347_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3347_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3388_; 
if (v_isShared_3386_ == 0)
{
v___x_3388_ = v___x_3385_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3383_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed(lean_object* v_fvarId_3481_, lean_object* v_mvarId_3482_, lean_object* v_goal_3483_, lean_object* v_kp_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(v_fvarId_3481_, v_mvarId_3482_, v_goal_3483_, v_kp_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec(v___y_3485_);
lean_dec_ref(v_goal_3483_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(lean_object* v_goal_3496_, lean_object* v_fvarId_3497_, lean_object* v_kp_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_){
_start:
{
lean_object* v_mvarId_3509_; lean_object* v___f_3510_; lean_object* v___x_3511_; 
v_mvarId_3509_ = lean_ctor_get(v_goal_3496_, 1);
lean_inc_n(v_mvarId_3509_, 2);
v___f_3510_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed), 14, 4);
lean_closure_set(v___f_3510_, 0, v_fvarId_3497_);
lean_closure_set(v___f_3510_, 1, v_mvarId_3509_);
lean_closure_set(v___f_3510_, 2, v_goal_3496_);
lean_closure_set(v___f_3510_, 3, v_kp_3498_);
v___x_3511_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3509_, v___f_3510_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___boxed(lean_object* v_goal_3512_, lean_object* v_fvarId_3513_, lean_object* v_kp_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_){
_start:
{
lean_object* v_res_3525_; 
v_res_3525_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3512_, v_fvarId_3513_, v_kp_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_, v_a_3523_);
lean_dec(v_a_3523_);
lean_dec_ref(v_a_3522_);
lean_dec(v_a_3521_);
lean_dec_ref(v_a_3520_);
lean_dec(v_a_3519_);
lean_dec_ref(v_a_3518_);
lean_dec(v_a_3517_);
lean_dec_ref(v_a_3516_);
lean_dec(v_a_3515_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(lean_object* v_kp_3526_, lean_object* v_as_3527_, lean_object* v_as_x27_3528_, lean_object* v_b_3529_, lean_object* v_a_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v___x_3541_; 
v___x_3541_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3526_, v_as_x27_3528_, v_b_3529_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___boxed(lean_object* v_kp_3542_, lean_object* v_as_3543_, lean_object* v_as_x27_3544_, lean_object* v_b_3545_, lean_object* v_a_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(v_kp_3542_, v_as_3543_, v_as_x27_3544_, v_b_3545_, v_a_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec(v___y_3547_);
lean_dec(v_as_x27_3544_);
lean_dec(v_as_3543_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0(lean_object* v_goal_3558_, lean_object* v_fvarId_3559_, lean_object* v_generation_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_){
_start:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3571_ = lean_st_mk_ref(v_goal_3558_);
v___x_3572_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_3559_, v_generation_3560_, v___x_3571_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3581_; 
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3581_ == 0)
{
lean_object* v_unused_3582_; 
v_unused_3582_ = lean_ctor_get(v___x_3572_, 0);
lean_dec(v_unused_3582_);
v___x_3574_ = v___x_3572_;
v_isShared_3575_ = v_isSharedCheck_3581_;
goto v_resetjp_3573_;
}
else
{
lean_dec(v___x_3572_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3581_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3579_; 
v___x_3576_ = lean_st_ref_get(v___x_3571_);
v___x_3577_ = lean_st_ref_get(v___x_3571_);
lean_dec(v___x_3571_);
lean_dec(v___x_3577_);
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v___x_3576_);
v___x_3579_ = v___x_3574_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3576_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
lean_dec(v___x_3571_);
v_a_3583_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3572_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3572_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3583_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0___boxed(lean_object* v_goal_3591_, lean_object* v_fvarId_3592_, lean_object* v_generation_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Lean_Meta_Grind_Action_intro___lam__0(v_goal_3591_, v_fvarId_3592_, v_generation_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro(lean_object* v_generation_3607_, lean_object* v_goal_3608_, lean_object* v_kna_3609_, lean_object* v_kp_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_){
_start:
{
lean_object* v_toGoalState_3621_; uint8_t v_inconsistent_3622_; 
v_toGoalState_3621_ = lean_ctor_get(v_goal_3608_, 0);
v_inconsistent_3622_ = lean_ctor_get_uint8(v_toGoalState_3621_, sizeof(void*)*17);
if (v_inconsistent_3622_ == 0)
{
lean_object* v_mvarId_3623_; lean_object* v___x_3624_; 
v_mvarId_3623_ = lean_ctor_get(v_goal_3608_, 1);
lean_inc(v_mvarId_3623_);
v___x_3624_ = l_Lean_MVarId_getType(v_mvarId_3623_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; uint8_t v___x_3626_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
lean_inc(v_a_3625_);
lean_dec_ref_known(v___x_3624_, 1);
v___x_3626_ = l_Lean_Expr_isFalse(v_a_3625_);
if (v___x_3626_ == 0)
{
lean_object* v___x_3627_; 
lean_dec_ref(v_kna_3609_);
lean_inc(v_generation_3607_);
v___x_3627_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_3608_, v_generation_3607_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v_a_3628_; 
v_a_3628_ = lean_ctor_get(v___x_3627_, 0);
lean_inc(v_a_3628_);
lean_dec_ref_known(v___x_3627_, 1);
switch(lean_obj_tag(v_a_3628_))
{
case 0:
{
lean_object* v_goal_3629_; lean_object* v___x_3630_; 
lean_dec(v_generation_3607_);
v_goal_3629_ = lean_ctor_get(v_a_3628_, 0);
lean_inc_ref(v_goal_3629_);
lean_dec_ref_known(v_a_3628_, 1);
v___x_3630_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_3629_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_object* v_a_3631_; lean_object* v_toGoalState_3632_; lean_object* v_mvarId_3633_; lean_object* v___x_3634_; 
v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
lean_inc(v_a_3631_);
lean_dec_ref_known(v___x_3630_, 1);
v_toGoalState_3632_ = lean_ctor_get(v_a_3631_, 0);
v_mvarId_3633_ = lean_ctor_get(v_a_3631_, 1);
lean_inc(v_mvarId_3633_);
v___x_3634_ = l_Lean_MVarId_byContra_x3f(v_mvarId_3633_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v_a_3635_; 
v_a_3635_ = lean_ctor_get(v___x_3634_, 0);
lean_inc(v_a_3635_);
lean_dec_ref_known(v___x_3634_, 1);
if (lean_obj_tag(v_a_3635_) == 1)
{
lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3644_; 
lean_inc_ref(v_toGoalState_3632_);
v_isSharedCheck_3644_ = !lean_is_exclusive(v_a_3631_);
if (v_isSharedCheck_3644_ == 0)
{
lean_object* v_unused_3645_; lean_object* v_unused_3646_; 
v_unused_3645_ = lean_ctor_get(v_a_3631_, 1);
lean_dec(v_unused_3645_);
v_unused_3646_ = lean_ctor_get(v_a_3631_, 0);
lean_dec(v_unused_3646_);
v___x_3637_ = v_a_3631_;
v_isShared_3638_ = v_isSharedCheck_3644_;
goto v_resetjp_3636_;
}
else
{
lean_dec(v_a_3631_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3644_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v_val_3639_; lean_object* v___x_3641_; 
v_val_3639_ = lean_ctor_get(v_a_3635_, 0);
lean_inc(v_val_3639_);
lean_dec_ref_known(v_a_3635_, 1);
if (v_isShared_3638_ == 0)
{
lean_ctor_set(v___x_3637_, 1, v_val_3639_);
v___x_3641_ = v___x_3637_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_toGoalState_3632_);
lean_ctor_set(v_reuseFailAlloc_3643_, 1, v_val_3639_);
v___x_3641_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
lean_object* v___x_3642_; 
lean_inc(v_a_3619_);
lean_inc_ref(v_a_3618_);
lean_inc(v_a_3617_);
lean_inc_ref(v_a_3616_);
lean_inc(v_a_3615_);
lean_inc_ref(v_a_3614_);
lean_inc(v_a_3613_);
lean_inc_ref(v_a_3612_);
lean_inc(v_a_3611_);
v___x_3642_ = lean_apply_11(v_kp_3610_, v___x_3641_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, lean_box(0));
return v___x_3642_;
}
}
}
else
{
lean_object* v___x_3647_; 
lean_dec(v_a_3635_);
lean_inc(v_a_3619_);
lean_inc_ref(v_a_3618_);
lean_inc(v_a_3617_);
lean_inc_ref(v_a_3616_);
lean_inc(v_a_3615_);
lean_inc_ref(v_a_3614_);
lean_inc(v_a_3613_);
lean_inc_ref(v_a_3612_);
lean_inc(v_a_3611_);
v___x_3647_ = lean_apply_11(v_kp_3610_, v_a_3631_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, lean_box(0));
return v___x_3647_;
}
}
else
{
lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3655_; 
lean_dec(v_a_3631_);
lean_dec_ref(v_kp_3610_);
v_a_3648_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3650_ = v___x_3634_;
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v___x_3634_);
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
}
else
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
lean_dec_ref(v_kp_3610_);
v_a_3656_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3658_ = v___x_3630_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3630_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3661_; 
if (v_isShared_3659_ == 0)
{
v___x_3661_ = v___x_3658_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_a_3656_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3664_; lean_object* v_goal_3665_; lean_object* v___x_3666_; 
v_fvarId_3664_ = lean_ctor_get(v_a_3628_, 0);
lean_inc_n(v_fvarId_3664_, 2);
v_goal_3665_ = lean_ctor_get(v_a_3628_, 1);
lean_inc_ref_n(v_goal_3665_, 2);
lean_dec_ref_known(v_a_3628_, 2);
v___x_3666_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_3665_, v_fvarId_3664_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_a_3667_);
lean_dec_ref_known(v___x_3666_, 1);
if (lean_obj_tag(v_a_3667_) == 1)
{
lean_object* v_val_3668_; lean_object* v___x_3669_; 
lean_dec_ref(v_goal_3665_);
lean_dec(v_fvarId_3664_);
lean_dec(v_generation_3607_);
v_val_3668_ = lean_ctor_get(v_a_3667_, 0);
lean_inc(v_val_3668_);
lean_dec_ref_known(v_a_3667_, 1);
lean_inc(v_a_3619_);
lean_inc_ref(v_a_3618_);
lean_inc(v_a_3617_);
lean_inc_ref(v_a_3616_);
lean_inc(v_a_3615_);
lean_inc_ref(v_a_3614_);
lean_inc(v_a_3613_);
lean_inc_ref(v_a_3612_);
lean_inc(v_a_3611_);
v___x_3669_ = lean_apply_11(v_kp_3610_, v_val_3668_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, lean_box(0));
return v___x_3669_;
}
else
{
lean_object* v___x_3670_; 
lean_dec(v_a_3667_);
lean_inc_ref(v_kp_3610_);
lean_inc(v_fvarId_3664_);
lean_inc_ref(v_goal_3665_);
v___x_3670_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3665_, v_fvarId_3664_, v_kp_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3692_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3673_ = v___x_3670_;
v_isShared_3674_ = v_isSharedCheck_3692_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3670_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3692_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
if (lean_obj_tag(v_a_3671_) == 1)
{
lean_object* v_val_3675_; lean_object* v___x_3677_; 
lean_dec_ref(v_goal_3665_);
lean_dec(v_fvarId_3664_);
lean_dec_ref(v_kp_3610_);
lean_dec(v_generation_3607_);
v_val_3675_ = lean_ctor_get(v_a_3671_, 0);
lean_inc(v_val_3675_);
lean_dec_ref_known(v_a_3671_, 1);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 0, v_val_3675_);
v___x_3677_ = v___x_3673_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_val_3675_);
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
lean_object* v_mvarId_3679_; lean_object* v___f_3680_; lean_object* v___x_3681_; 
lean_del_object(v___x_3673_);
lean_dec(v_a_3671_);
v_mvarId_3679_ = lean_ctor_get(v_goal_3665_, 1);
lean_inc(v_mvarId_3679_);
v___f_3680_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intro___lam__0___boxed), 13, 3);
lean_closure_set(v___f_3680_, 0, v_goal_3665_);
lean_closure_set(v___f_3680_, 1, v_fvarId_3664_);
lean_closure_set(v___f_3680_, 2, v_generation_3607_);
v___x_3681_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3679_, v___f_3680_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_);
if (lean_obj_tag(v___x_3681_) == 0)
{
lean_object* v_a_3682_; lean_object* v___x_3683_; 
v_a_3682_ = lean_ctor_get(v___x_3681_, 0);
lean_inc(v_a_3682_);
lean_dec_ref_known(v___x_3681_, 1);
lean_inc(v_a_3619_);
lean_inc_ref(v_a_3618_);
lean_inc(v_a_3617_);
lean_inc_ref(v_a_3616_);
lean_inc(v_a_3615_);
lean_inc_ref(v_a_3614_);
lean_inc(v_a_3613_);
lean_inc_ref(v_a_3612_);
lean_inc(v_a_3611_);
v___x_3683_ = lean_apply_11(v_kp_3610_, v_a_3682_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, lean_box(0));
return v___x_3683_;
}
else
{
lean_object* v_a_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3691_; 
lean_dec_ref(v_kp_3610_);
v_a_3684_ = lean_ctor_get(v___x_3681_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3686_ = v___x_3681_;
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_a_3684_);
lean_dec(v___x_3681_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3689_; 
if (v_isShared_3687_ == 0)
{
v___x_3689_ = v___x_3686_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3684_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
}
}
}
}
else
{
lean_object* v_a_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3700_; 
lean_dec_ref(v_goal_3665_);
lean_dec(v_fvarId_3664_);
lean_dec_ref(v_kp_3610_);
lean_dec(v_generation_3607_);
v_a_3693_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3695_ = v___x_3670_;
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_a_3693_);
lean_dec(v___x_3670_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3698_; 
if (v_isShared_3696_ == 0)
{
v___x_3698_ = v___x_3695_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3693_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
}
}
else
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3708_; 
lean_dec_ref(v_goal_3665_);
lean_dec(v_fvarId_3664_);
lean_dec_ref(v_kp_3610_);
lean_dec(v_generation_3607_);
v_a_3701_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3703_ = v___x_3666_;
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3666_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3706_; 
if (v_isShared_3704_ == 0)
{
v___x_3706_ = v___x_3703_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3701_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
case 2:
{
lean_object* v_goal_3709_; lean_object* v___x_3710_; 
lean_dec(v_generation_3607_);
v_goal_3709_ = lean_ctor_get(v_a_3628_, 0);
lean_inc_ref(v_goal_3709_);
lean_dec_ref_known(v_a_3628_, 1);
lean_inc(v_a_3619_);
lean_inc_ref(v_a_3618_);
lean_inc(v_a_3617_);
lean_inc_ref(v_a_3616_);
lean_inc(v_a_3615_);
lean_inc_ref(v_a_3614_);
lean_inc(v_a_3613_);
lean_inc_ref(v_a_3612_);
lean_inc(v_a_3611_);
v___x_3710_ = lean_apply_11(v_kp_3610_, v_goal_3709_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, lean_box(0));
return v___x_3710_;
}
default: 
{
lean_object* v_fvarId_3711_; lean_object* v_goal_3712_; lean_object* v___x_3713_; 
lean_dec(v_generation_3607_);
v_fvarId_3711_ = lean_ctor_get(v_a_3628_, 0);
lean_inc(v_fvarId_3711_);
v_goal_3712_ = lean_ctor_get(v_a_3628_, 1);
lean_inc_ref_n(v_goal_3712_, 2);
lean_dec_ref_known(v_a_3628_, 2);
lean_inc_ref(v_kp_3610_);
v___x_3713_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3712_, v_fvarId_3711_, v_kp_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3723_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3716_ = v___x_3713_;
v_isShared_3717_ = v_isSharedCheck_3723_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_a_3714_);
lean_dec(v___x_3713_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3723_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
if (lean_obj_tag(v_a_3714_) == 1)
{
lean_object* v_val_3718_; lean_object* v___x_3720_; 
lean_dec_ref(v_goal_3712_);
lean_dec_ref(v_kp_3610_);
v_val_3718_ = lean_ctor_get(v_a_3714_, 0);
lean_inc(v_val_3718_);
lean_dec_ref_known(v_a_3714_, 1);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 0, v_val_3718_);
v___x_3720_ = v___x_3716_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_val_3718_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
else
{
lean_object* v___x_3722_; 
lean_del_object(v___x_3716_);
lean_dec(v_a_3714_);
lean_inc(v_a_3619_);
lean_inc_ref(v_a_3618_);
lean_inc(v_a_3617_);
lean_inc_ref(v_a_3616_);
lean_inc(v_a_3615_);
lean_inc_ref(v_a_3614_);
lean_inc(v_a_3613_);
lean_inc_ref(v_a_3612_);
lean_inc(v_a_3611_);
v___x_3722_ = lean_apply_11(v_kp_3610_, v_goal_3712_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, lean_box(0));
return v___x_3722_;
}
}
}
else
{
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
lean_dec_ref(v_goal_3712_);
lean_dec_ref(v_kp_3610_);
v_a_3724_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3726_ = v___x_3713_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3713_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_a_3724_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
}
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_dec_ref(v_kp_3610_);
lean_dec(v_generation_3607_);
v_a_3732_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3627_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3627_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
else
{
lean_object* v___x_3740_; 
lean_dec_ref(v_kp_3610_);
lean_dec(v_generation_3607_);
lean_inc(v_a_3619_);
lean_inc_ref(v_a_3618_);
lean_inc(v_a_3617_);
lean_inc_ref(v_a_3616_);
lean_inc(v_a_3615_);
lean_inc_ref(v_a_3614_);
lean_inc(v_a_3613_);
lean_inc_ref(v_a_3612_);
lean_inc(v_a_3611_);
v___x_3740_ = lean_apply_11(v_kna_3609_, v_goal_3608_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, lean_box(0));
return v___x_3740_;
}
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
lean_dec_ref(v_kp_3610_);
lean_dec_ref(v_kna_3609_);
lean_dec_ref(v_goal_3608_);
lean_dec(v_generation_3607_);
v_a_3741_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3624_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3624_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
else
{
lean_object* v___x_3749_; lean_object* v___x_3750_; 
lean_dec_ref(v_kp_3610_);
lean_dec_ref(v_kna_3609_);
lean_dec_ref(v_goal_3608_);
lean_dec(v_generation_3607_);
v___x_3749_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intro___closed__0));
v___x_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3749_);
return v___x_3750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___boxed(lean_object* v_generation_3751_, lean_object* v_goal_3752_, lean_object* v_kna_3753_, lean_object* v_kp_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l_Lean_Meta_Grind_Action_intro(v_generation_3751_, v_goal_3752_, v_kna_3753_, v_kp_3754_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_);
lean_dec(v_a_3763_);
lean_dec_ref(v_a_3762_);
lean_dec(v_a_3761_);
lean_dec_ref(v_a_3760_);
lean_dec(v_a_3759_);
lean_dec_ref(v_a_3758_);
lean_dec(v_a_3757_);
lean_dec_ref(v_a_3756_);
lean_dec(v_a_3755_);
return v_res_3765_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_hugeNumber(void){
_start:
{
lean_object* v___x_3766_; 
v___x_3766_ = lean_unsigned_to_nat(1000000u);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0(lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_){
_start:
{
lean_object* v___x_3780_; 
v___x_3780_ = l_Lean_Meta_Grind_Action_group___redArg(v___y_3767_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0___boxed(lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_){
_start:
{
lean_object* v_res_3794_; 
v_res_3794_ = l_Lean_Meta_Grind_Action_intros___lam__0(v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3782_);
return v_res_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1(lean_object* v_generation_3795_, lean_object* v___f_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3810_ = lean_unsigned_to_nat(1000000u);
v___x_3811_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intro___boxed), 14, 1);
lean_closure_set(v___x_3811_, 0, v_generation_3795_);
v___x_3812_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_loop___boxed), 15, 2);
lean_closure_set(v___x_3812_, 0, v___x_3810_);
lean_closure_set(v___x_3812_, 1, v___x_3811_);
v___x_3813_ = l_Lean_Meta_Grind_Action_andThen(v___x_3812_, v___f_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
return v___x_3813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1___boxed(lean_object* v_generation_3814_, lean_object* v___f_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
lean_object* v_res_3829_; 
v_res_3829_ = l_Lean_Meta_Grind_Action_intros___lam__1(v_generation_3814_, v___f_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
lean_dec(v___y_3819_);
return v_res_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros(lean_object* v_generation_3832_, lean_object* v_a_3833_, lean_object* v_kna_3834_, lean_object* v_kp_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_){
_start:
{
lean_object* v___f_3846_; lean_object* v___f_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___f_3846_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intros___closed__0));
v___f_3847_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___lam__1___boxed), 15, 2);
lean_closure_set(v___f_3847_, 0, v_generation_3832_);
lean_closure_set(v___f_3847_, 1, v___f_3846_);
v___x_3848_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intros___closed__1));
v___x_3849_ = l_Lean_Meta_Grind_Action_andThen(v___x_3848_, v___f_3847_, v_a_3833_, v_kna_3834_, v_kp_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___boxed(lean_object* v_generation_3850_, lean_object* v_a_3851_, lean_object* v_kna_3852_, lean_object* v_kp_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l_Lean_Meta_Grind_Action_intros(v_generation_3850_, v_a_3851_, v_kna_3852_, v_kp_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_);
lean_dec(v_a_3862_);
lean_dec_ref(v_a_3861_);
lean_dec(v_a_3860_);
lean_dec_ref(v_a_3859_);
lean_dec(v_a_3858_);
lean_dec_ref(v_a_3857_);
lean_dec(v_a_3856_);
lean_dec_ref(v_a_3855_);
lean_dec(v_a_3854_);
return v_res_3864_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3872_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__2));
v___x_3873_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1));
v___x_3874_ = l_Lean_mkConst(v___x_3873_, v___x_3872_);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(lean_object* v_goal_3875_, lean_object* v_prop_3876_, lean_object* v_proof_3877_, lean_object* v_generation_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3889_ = lean_st_mk_ref(v_goal_3875_);
lean_inc(v___y_3887_);
lean_inc_ref(v___y_3886_);
lean_inc(v___y_3885_);
lean_inc_ref(v___y_3884_);
lean_inc(v___y_3883_);
lean_inc_ref(v___y_3882_);
lean_inc(v___y_3881_);
lean_inc_ref(v___y_3880_);
lean_inc(v___y_3879_);
lean_inc(v___x_3889_);
lean_inc_ref(v_prop_3876_);
v___x_3890_ = lean_grind_preprocess(v_prop_3876_, v___x_3889_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; lean_object* v_expr_3892_; lean_object* v___x_3893_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_a_3891_);
lean_dec_ref_known(v___x_3890_, 1);
v_expr_3892_ = lean_ctor_get(v_a_3891_, 0);
lean_inc_ref(v_expr_3892_);
v___x_3893_ = l_Lean_Meta_Simp_Result_getProof(v_a_3891_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_a_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
lean_inc(v_a_3894_);
lean_dec_ref_known(v___x_3893_, 1);
v___x_3895_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3);
lean_inc_ref(v_expr_3892_);
v___x_3896_ = l_Lean_mkApp4(v___x_3895_, v_prop_3876_, v_expr_3892_, v_a_3894_, v_proof_3877_);
v___x_3897_ = l_Lean_Meta_Grind_add(v_expr_3892_, v___x_3896_, v_generation_3878_, v___x_3889_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3906_; 
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3906_ == 0)
{
lean_object* v_unused_3907_; 
v_unused_3907_ = lean_ctor_get(v___x_3897_, 0);
lean_dec(v_unused_3907_);
v___x_3899_ = v___x_3897_;
v_isShared_3900_ = v_isSharedCheck_3906_;
goto v_resetjp_3898_;
}
else
{
lean_dec(v___x_3897_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3906_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3904_; 
v___x_3901_ = lean_st_ref_get(v___x_3889_);
v___x_3902_ = lean_st_ref_get(v___x_3889_);
lean_dec(v___x_3889_);
lean_dec(v___x_3902_);
if (v_isShared_3900_ == 0)
{
lean_ctor_set(v___x_3899_, 0, v___x_3901_);
v___x_3904_ = v___x_3899_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v___x_3901_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
else
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3915_; 
lean_dec(v___x_3889_);
v_a_3908_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3910_ = v___x_3897_;
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3897_);
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
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3923_; 
lean_dec_ref(v_expr_3892_);
lean_dec(v___x_3889_);
lean_dec(v_generation_3878_);
lean_dec_ref(v_proof_3877_);
lean_dec_ref(v_prop_3876_);
v_a_3916_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3918_ = v___x_3893_;
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3893_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3919_ == 0)
{
v___x_3921_ = v___x_3918_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_a_3916_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
}
else
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3931_; 
lean_dec(v___x_3889_);
lean_dec(v_generation_3878_);
lean_dec_ref(v_proof_3877_);
lean_dec_ref(v_prop_3876_);
v_a_3924_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3926_ = v___x_3890_;
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3890_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3929_; 
if (v_isShared_3927_ == 0)
{
v___x_3929_ = v___x_3926_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3924_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed(lean_object* v_goal_3932_, lean_object* v_prop_3933_, lean_object* v_proof_3934_, lean_object* v_generation_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(v_goal_3932_, v_prop_3933_, v_proof_3934_, v_generation_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec_ref(v___y_3941_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3936_);
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(lean_object* v_mvarId_3947_, lean_object* v___f_3948_, lean_object* v_kp_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_){
_start:
{
lean_object* v___x_3960_; 
v___x_3960_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3947_, v___f_3948_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v_a_3961_; lean_object* v___x_3962_; 
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_a_3961_);
lean_dec_ref_known(v___x_3960_, 1);
lean_inc(v___y_3958_);
lean_inc_ref(v___y_3957_);
lean_inc(v___y_3956_);
lean_inc_ref(v___y_3955_);
lean_inc(v___y_3954_);
lean_inc_ref(v___y_3953_);
lean_inc(v___y_3952_);
lean_inc_ref(v___y_3951_);
lean_inc(v___y_3950_);
v___x_3962_ = lean_apply_11(v_kp_3949_, v_a_3961_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, lean_box(0));
return v___x_3962_;
}
else
{
lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
lean_dec_ref(v_kp_3949_);
v_a_3963_ = lean_ctor_get(v___x_3960_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3965_ = v___x_3960_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v___x_3960_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed(lean_object* v_mvarId_3971_, lean_object* v___f_3972_, lean_object* v_kp_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
lean_object* v_res_3984_; 
v_res_3984_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(v_mvarId_3971_, v___f_3972_, v_kp_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
lean_dec(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec(v___y_3974_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(lean_object* v_proof_3985_, lean_object* v_prop_3986_, lean_object* v_generation_3987_, lean_object* v_goal_3988_, lean_object* v_kna_3989_, lean_object* v_kp_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_){
_start:
{
lean_object* v___x_4001_; 
v___x_4001_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_prop_3986_, v_a_3992_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_object* v_a_4002_; uint8_t v___x_4003_; 
v_a_4002_ = lean_ctor_get(v___x_4001_, 0);
lean_inc(v_a_4002_);
lean_dec_ref_known(v___x_4001_, 1);
v___x_4003_ = lean_unbox(v_a_4002_);
lean_dec(v_a_4002_);
if (v___x_4003_ == 0)
{
lean_object* v_mvarId_4004_; lean_object* v___f_4005_; lean_object* v___f_4006_; lean_object* v___x_4007_; 
lean_dec_ref(v_kna_3989_);
v_mvarId_4004_ = lean_ctor_get(v_goal_3988_, 1);
lean_inc_n(v_mvarId_4004_, 2);
v___f_4005_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed), 14, 4);
lean_closure_set(v___f_4005_, 0, v_goal_3988_);
lean_closure_set(v___f_4005_, 1, v_prop_3986_);
lean_closure_set(v___f_4005_, 2, v_proof_3985_);
lean_closure_set(v___f_4005_, 3, v_generation_3987_);
v___f_4006_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed), 13, 3);
lean_closure_set(v___f_4006_, 0, v_mvarId_4004_);
lean_closure_set(v___f_4006_, 1, v___f_4005_);
lean_closure_set(v___f_4006_, 2, v_kp_3990_);
v___x_4007_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_4004_, v___f_4006_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
return v___x_4007_;
}
else
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4008_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v___x_4009_ = l_Lean_Core_mkFreshUserName(v___x_4008_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v_a_4010_; lean_object* v_toGoalState_4011_; lean_object* v_mvarId_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4030_; 
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
lean_inc(v_a_4010_);
lean_dec_ref_known(v___x_4009_, 1);
v_toGoalState_4011_ = lean_ctor_get(v_goal_3988_, 0);
v_mvarId_4012_ = lean_ctor_get(v_goal_3988_, 1);
v_isSharedCheck_4030_ = !lean_is_exclusive(v_goal_3988_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4014_ = v_goal_3988_;
v_isShared_4015_ = v_isSharedCheck_4030_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_mvarId_4012_);
lean_inc(v_toGoalState_4011_);
lean_dec(v_goal_3988_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4030_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4016_; 
v___x_4016_ = l_Lean_MVarId_assert(v_mvarId_4012_, v_a_4010_, v_prop_3986_, v_proof_3985_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_object* v_a_4017_; lean_object* v___x_4019_; 
v_a_4017_ = lean_ctor_get(v___x_4016_, 0);
lean_inc(v_a_4017_);
lean_dec_ref_known(v___x_4016_, 1);
if (v_isShared_4015_ == 0)
{
lean_ctor_set(v___x_4014_, 1, v_a_4017_);
v___x_4019_ = v___x_4014_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_toGoalState_4011_);
lean_ctor_set(v_reuseFailAlloc_4021_, 1, v_a_4017_);
v___x_4019_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
lean_object* v___x_4020_; 
v___x_4020_ = l_Lean_Meta_Grind_Action_intros(v_generation_3987_, v___x_4019_, v_kna_3989_, v_kp_3990_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
return v___x_4020_;
}
}
else
{
lean_object* v_a_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4029_; 
lean_del_object(v___x_4014_);
lean_dec_ref(v_toGoalState_4011_);
lean_dec_ref(v_kp_3990_);
lean_dec_ref(v_kna_3989_);
lean_dec(v_generation_3987_);
v_a_4022_ = lean_ctor_get(v___x_4016_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4024_ = v___x_4016_;
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_a_4022_);
lean_dec(v___x_4016_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4027_; 
if (v_isShared_4025_ == 0)
{
v___x_4027_ = v___x_4024_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_a_4022_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
}
}
}
else
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4038_; 
lean_dec_ref(v_kp_3990_);
lean_dec_ref(v_kna_3989_);
lean_dec_ref(v_goal_3988_);
lean_dec(v_generation_3987_);
lean_dec_ref(v_prop_3986_);
lean_dec_ref(v_proof_3985_);
v_a_4031_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4038_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4033_ = v___x_4009_;
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v___x_4009_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4036_; 
if (v_isShared_4034_ == 0)
{
v___x_4036_ = v___x_4033_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4031_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
return v___x_4036_;
}
}
}
}
}
else
{
lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4046_; 
lean_dec_ref(v_kp_3990_);
lean_dec_ref(v_kna_3989_);
lean_dec_ref(v_goal_3988_);
lean_dec(v_generation_3987_);
lean_dec_ref(v_prop_3986_);
lean_dec_ref(v_proof_3985_);
v_a_4039_ = lean_ctor_get(v___x_4001_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4041_ = v___x_4001_;
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_dec(v___x_4001_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4044_; 
if (v_isShared_4042_ == 0)
{
v___x_4044_ = v___x_4041_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_a_4039_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___boxed(lean_object* v_proof_4047_, lean_object* v_prop_4048_, lean_object* v_generation_4049_, lean_object* v_goal_4050_, lean_object* v_kna_4051_, lean_object* v_kp_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(v_proof_4047_, v_prop_4048_, v_generation_4049_, v_goal_4050_, v_kna_4051_, v_kp_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_);
lean_dec(v_a_4061_);
lean_dec_ref(v_a_4060_);
lean_dec(v_a_4059_);
lean_dec_ref(v_a_4058_);
lean_dec(v_a_4057_);
lean_dec_ref(v_a_4056_);
lean_dec(v_a_4055_);
lean_dec_ref(v_a_4054_);
lean_dec(v_a_4053_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext(lean_object* v_goal_4064_, lean_object* v_kna_4065_, lean_object* v_kp_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_){
_start:
{
lean_object* v_toGoalState_4077_; uint8_t v_inconsistent_4078_; 
v_toGoalState_4077_ = lean_ctor_get(v_goal_4064_, 0);
lean_inc_ref(v_toGoalState_4077_);
v_inconsistent_4078_ = lean_ctor_get_uint8(v_toGoalState_4077_, sizeof(void*)*17);
if (v_inconsistent_4078_ == 0)
{
lean_object* v_mvarId_4079_; lean_object* v_nextDeclIdx_4080_; lean_object* v_enodeMap_4081_; lean_object* v_exprs_4082_; lean_object* v_parents_4083_; lean_object* v_congrTable_4084_; lean_object* v_appMap_4085_; lean_object* v_indicesFound_4086_; lean_object* v_newFacts_4087_; lean_object* v_nextIdx_4088_; lean_object* v_newRawFacts_4089_; lean_object* v_facts_4090_; lean_object* v_extThms_4091_; lean_object* v_ematch_4092_; lean_object* v_inj_4093_; lean_object* v_split_4094_; lean_object* v_clean_4095_; lean_object* v_sstates_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4134_; 
v_mvarId_4079_ = lean_ctor_get(v_goal_4064_, 1);
v_nextDeclIdx_4080_ = lean_ctor_get(v_toGoalState_4077_, 0);
v_enodeMap_4081_ = lean_ctor_get(v_toGoalState_4077_, 1);
v_exprs_4082_ = lean_ctor_get(v_toGoalState_4077_, 2);
v_parents_4083_ = lean_ctor_get(v_toGoalState_4077_, 3);
v_congrTable_4084_ = lean_ctor_get(v_toGoalState_4077_, 4);
v_appMap_4085_ = lean_ctor_get(v_toGoalState_4077_, 5);
v_indicesFound_4086_ = lean_ctor_get(v_toGoalState_4077_, 6);
v_newFacts_4087_ = lean_ctor_get(v_toGoalState_4077_, 7);
v_nextIdx_4088_ = lean_ctor_get(v_toGoalState_4077_, 8);
v_newRawFacts_4089_ = lean_ctor_get(v_toGoalState_4077_, 9);
v_facts_4090_ = lean_ctor_get(v_toGoalState_4077_, 10);
v_extThms_4091_ = lean_ctor_get(v_toGoalState_4077_, 11);
v_ematch_4092_ = lean_ctor_get(v_toGoalState_4077_, 12);
v_inj_4093_ = lean_ctor_get(v_toGoalState_4077_, 13);
v_split_4094_ = lean_ctor_get(v_toGoalState_4077_, 14);
v_clean_4095_ = lean_ctor_get(v_toGoalState_4077_, 15);
v_sstates_4096_ = lean_ctor_get(v_toGoalState_4077_, 16);
v_isSharedCheck_4134_ = !lean_is_exclusive(v_toGoalState_4077_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4098_ = v_toGoalState_4077_;
v_isShared_4099_ = v_isSharedCheck_4134_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_sstates_4096_);
lean_inc(v_clean_4095_);
lean_inc(v_split_4094_);
lean_inc(v_inj_4093_);
lean_inc(v_ematch_4092_);
lean_inc(v_extThms_4091_);
lean_inc(v_facts_4090_);
lean_inc(v_newRawFacts_4089_);
lean_inc(v_nextIdx_4088_);
lean_inc(v_newFacts_4087_);
lean_inc(v_indicesFound_4086_);
lean_inc(v_appMap_4085_);
lean_inc(v_congrTable_4084_);
lean_inc(v_parents_4083_);
lean_inc(v_exprs_4082_);
lean_inc(v_enodeMap_4081_);
lean_inc(v_nextDeclIdx_4080_);
lean_dec(v_toGoalState_4077_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4134_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4100_; 
v___x_4100_ = l_Std_Queue_dequeue_x3f___redArg(v_newRawFacts_4089_);
if (lean_obj_tag(v___x_4100_) == 1)
{
lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4130_; 
lean_inc(v_mvarId_4079_);
v_isSharedCheck_4130_ = !lean_is_exclusive(v_goal_4064_);
if (v_isSharedCheck_4130_ == 0)
{
lean_object* v_unused_4131_; lean_object* v_unused_4132_; 
v_unused_4131_ = lean_ctor_get(v_goal_4064_, 1);
lean_dec(v_unused_4131_);
v_unused_4132_ = lean_ctor_get(v_goal_4064_, 0);
lean_dec(v_unused_4132_);
v___x_4102_ = v_goal_4064_;
v_isShared_4103_ = v_isSharedCheck_4130_;
goto v_resetjp_4101_;
}
else
{
lean_dec(v_goal_4064_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4130_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v_val_4104_; lean_object* v_fst_4105_; lean_object* v_snd_4106_; lean_object* v_proof_4107_; lean_object* v_prop_4108_; lean_object* v_generation_4109_; lean_object* v_splitSource_4110_; lean_object* v_ematchDiagSource_4111_; lean_object* v_simp_4112_; lean_object* v_simpMethods_4113_; lean_object* v_config_4114_; lean_object* v_anchorRefs_x3f_4115_; uint8_t v_cheapCases_4116_; uint8_t v_reportMVarIssue_4117_; lean_object* v_symPrios_4118_; lean_object* v_extensions_4119_; uint8_t v_debug_4120_; uint8_t v_ematchDiag_4121_; lean_object* v___x_4123_; 
v_val_4104_ = lean_ctor_get(v___x_4100_, 0);
lean_inc(v_val_4104_);
lean_dec_ref_known(v___x_4100_, 1);
v_fst_4105_ = lean_ctor_get(v_val_4104_, 0);
lean_inc(v_fst_4105_);
v_snd_4106_ = lean_ctor_get(v_val_4104_, 1);
lean_inc(v_snd_4106_);
lean_dec(v_val_4104_);
v_proof_4107_ = lean_ctor_get(v_fst_4105_, 0);
lean_inc_ref(v_proof_4107_);
v_prop_4108_ = lean_ctor_get(v_fst_4105_, 1);
lean_inc_ref(v_prop_4108_);
v_generation_4109_ = lean_ctor_get(v_fst_4105_, 2);
lean_inc(v_generation_4109_);
v_splitSource_4110_ = lean_ctor_get(v_fst_4105_, 3);
lean_inc(v_splitSource_4110_);
v_ematchDiagSource_4111_ = lean_ctor_get(v_fst_4105_, 4);
lean_inc(v_ematchDiagSource_4111_);
lean_dec(v_fst_4105_);
v_simp_4112_ = lean_ctor_get(v_a_4068_, 0);
v_simpMethods_4113_ = lean_ctor_get(v_a_4068_, 1);
v_config_4114_ = lean_ctor_get(v_a_4068_, 2);
v_anchorRefs_x3f_4115_ = lean_ctor_get(v_a_4068_, 3);
v_cheapCases_4116_ = lean_ctor_get_uint8(v_a_4068_, sizeof(void*)*8);
v_reportMVarIssue_4117_ = lean_ctor_get_uint8(v_a_4068_, sizeof(void*)*8 + 1);
v_symPrios_4118_ = lean_ctor_get(v_a_4068_, 6);
v_extensions_4119_ = lean_ctor_get(v_a_4068_, 7);
v_debug_4120_ = lean_ctor_get_uint8(v_a_4068_, sizeof(void*)*8 + 2);
v_ematchDiag_4121_ = lean_ctor_get_uint8(v_a_4068_, sizeof(void*)*8 + 3);
if (v_isShared_4099_ == 0)
{
lean_ctor_set(v___x_4098_, 9, v_snd_4106_);
v___x_4123_ = v___x_4098_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v_nextDeclIdx_4080_);
lean_ctor_set(v_reuseFailAlloc_4129_, 1, v_enodeMap_4081_);
lean_ctor_set(v_reuseFailAlloc_4129_, 2, v_exprs_4082_);
lean_ctor_set(v_reuseFailAlloc_4129_, 3, v_parents_4083_);
lean_ctor_set(v_reuseFailAlloc_4129_, 4, v_congrTable_4084_);
lean_ctor_set(v_reuseFailAlloc_4129_, 5, v_appMap_4085_);
lean_ctor_set(v_reuseFailAlloc_4129_, 6, v_indicesFound_4086_);
lean_ctor_set(v_reuseFailAlloc_4129_, 7, v_newFacts_4087_);
lean_ctor_set(v_reuseFailAlloc_4129_, 8, v_nextIdx_4088_);
lean_ctor_set(v_reuseFailAlloc_4129_, 9, v_snd_4106_);
lean_ctor_set(v_reuseFailAlloc_4129_, 10, v_facts_4090_);
lean_ctor_set(v_reuseFailAlloc_4129_, 11, v_extThms_4091_);
lean_ctor_set(v_reuseFailAlloc_4129_, 12, v_ematch_4092_);
lean_ctor_set(v_reuseFailAlloc_4129_, 13, v_inj_4093_);
lean_ctor_set(v_reuseFailAlloc_4129_, 14, v_split_4094_);
lean_ctor_set(v_reuseFailAlloc_4129_, 15, v_clean_4095_);
lean_ctor_set(v_reuseFailAlloc_4129_, 16, v_sstates_4096_);
lean_ctor_set_uint8(v_reuseFailAlloc_4129_, sizeof(void*)*17, v_inconsistent_4078_);
v___x_4123_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
lean_object* v_goal_4125_; 
if (v_isShared_4103_ == 0)
{
lean_ctor_set(v___x_4102_, 0, v___x_4123_);
v_goal_4125_ = v___x_4102_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v___x_4123_);
lean_ctor_set(v_reuseFailAlloc_4128_, 1, v_mvarId_4079_);
v_goal_4125_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
lean_inc_ref(v_extensions_4119_);
lean_inc_ref(v_symPrios_4118_);
lean_inc(v_anchorRefs_x3f_4115_);
lean_inc_ref(v_config_4114_);
lean_inc_ref(v_simpMethods_4113_);
lean_inc_ref(v_simp_4112_);
v___x_4126_ = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(v___x_4126_, 0, v_simp_4112_);
lean_ctor_set(v___x_4126_, 1, v_simpMethods_4113_);
lean_ctor_set(v___x_4126_, 2, v_config_4114_);
lean_ctor_set(v___x_4126_, 3, v_anchorRefs_x3f_4115_);
lean_ctor_set(v___x_4126_, 4, v_splitSource_4110_);
lean_ctor_set(v___x_4126_, 5, v_ematchDiagSource_4111_);
lean_ctor_set(v___x_4126_, 6, v_symPrios_4118_);
lean_ctor_set(v___x_4126_, 7, v_extensions_4119_);
lean_ctor_set_uint8(v___x_4126_, sizeof(void*)*8, v_cheapCases_4116_);
lean_ctor_set_uint8(v___x_4126_, sizeof(void*)*8 + 1, v_reportMVarIssue_4117_);
lean_ctor_set_uint8(v___x_4126_, sizeof(void*)*8 + 2, v_debug_4120_);
lean_ctor_set_uint8(v___x_4126_, sizeof(void*)*8 + 3, v_ematchDiag_4121_);
v___x_4127_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(v_proof_4107_, v_prop_4108_, v_generation_4109_, v_goal_4125_, v_kna_4065_, v_kp_4066_, v_a_4067_, v___x_4126_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_);
lean_dec_ref_known(v___x_4126_, 8);
return v___x_4127_;
}
}
}
}
else
{
lean_object* v___x_4133_; 
lean_dec(v___x_4100_);
lean_del_object(v___x_4098_);
lean_dec_ref(v_sstates_4096_);
lean_dec_ref(v_clean_4095_);
lean_dec_ref(v_split_4094_);
lean_dec_ref(v_inj_4093_);
lean_dec_ref(v_ematch_4092_);
lean_dec_ref(v_extThms_4091_);
lean_dec_ref(v_facts_4090_);
lean_dec(v_nextIdx_4088_);
lean_dec_ref(v_newFacts_4087_);
lean_dec_ref(v_indicesFound_4086_);
lean_dec_ref(v_appMap_4085_);
lean_dec_ref(v_congrTable_4084_);
lean_dec_ref(v_parents_4083_);
lean_dec_ref(v_exprs_4082_);
lean_dec_ref(v_enodeMap_4081_);
lean_dec(v_nextDeclIdx_4080_);
lean_dec_ref(v_kp_4066_);
lean_inc(v_a_4075_);
lean_inc_ref(v_a_4074_);
lean_inc(v_a_4073_);
lean_inc_ref(v_a_4072_);
lean_inc(v_a_4071_);
lean_inc_ref(v_a_4070_);
lean_inc(v_a_4069_);
lean_inc_ref(v_a_4068_);
lean_inc(v_a_4067_);
v___x_4133_ = lean_apply_11(v_kna_4065_, v_goal_4064_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, lean_box(0));
return v___x_4133_;
}
}
}
else
{
lean_object* v___x_4135_; lean_object* v___x_4136_; 
lean_dec_ref(v_toGoalState_4077_);
lean_dec_ref(v_kp_4066_);
lean_dec_ref(v_kna_4065_);
lean_dec_ref(v_goal_4064_);
v___x_4135_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intro___closed__0));
v___x_4136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4136_, 0, v___x_4135_);
return v___x_4136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext___boxed(lean_object* v_goal_4137_, lean_object* v_kna_4138_, lean_object* v_kp_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_){
_start:
{
lean_object* v_res_4150_; 
v_res_4150_ = l_Lean_Meta_Grind_Action_assertNext(v_goal_4137_, v_kna_4138_, v_kp_4139_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_);
lean_dec(v_a_4148_);
lean_dec_ref(v_a_4147_);
lean_dec(v_a_4146_);
lean_dec_ref(v_a_4145_);
lean_dec(v_a_4144_);
lean_dec_ref(v_a_4143_);
lean_dec(v_a_4142_);
lean_dec_ref(v_a_4141_);
lean_dec(v_a_4140_);
return v_res_4150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg(lean_object* v_a_4151_, lean_object* v_kp_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_){
_start:
{
lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
v___x_4163_ = lean_unsigned_to_nat(1000000u);
v___x_4164_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_assertNext___boxed), 13, 0);
v___x_4165_ = l_Lean_Meta_Grind_Action_loop___redArg(v___x_4163_, v___x_4164_, v_a_4151_, v_kp_4152_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_);
return v___x_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg___boxed(lean_object* v_a_4166_, lean_object* v_kp_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4166_, v_kp_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_);
lean_dec(v_a_4176_);
lean_dec_ref(v_a_4175_);
lean_dec(v_a_4174_);
lean_dec_ref(v_a_4173_);
lean_dec(v_a_4172_);
lean_dec_ref(v_a_4171_);
lean_dec(v_a_4170_);
lean_dec_ref(v_a_4169_);
lean_dec(v_a_4168_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll(lean_object* v_a_4179_, lean_object* v_kna_4180_, lean_object* v_kp_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_){
_start:
{
lean_object* v___x_4192_; 
v___x_4192_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4179_, v_kp_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___boxed(lean_object* v_a_4193_, lean_object* v_kna_4194_, lean_object* v_kp_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_){
_start:
{
lean_object* v_res_4206_; 
v_res_4206_ = l_Lean_Meta_Grind_Action_assertAll(v_a_4193_, v_kna_4194_, v_kp_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_);
lean_dec(v_a_4204_);
lean_dec_ref(v_a_4203_);
lean_dec(v_a_4202_);
lean_dec_ref(v_a_4201_);
lean_dec(v_a_4200_);
lean_dec_ref(v_a_4199_);
lean_dec(v_a_4198_);
lean_dec_ref(v_a_4197_);
lean_dec(v_a_4196_);
lean_dec_ref(v_kna_4194_);
return v_res_4206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__0(lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_){
_start:
{
lean_object* v___x_4220_; 
v___x_4220_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_4207_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_);
return v___x_4220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__0___boxed(lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v_res_4234_; 
v_res_4234_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__0(v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
lean_dec(v___y_4232_);
lean_dec_ref(v___y_4231_);
lean_dec(v___y_4230_);
lean_dec_ref(v___y_4229_);
lean_dec(v___y_4228_);
lean_dec_ref(v___y_4227_);
lean_dec(v___y_4226_);
lean_dec_ref(v___y_4225_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4222_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__1(lean_object* v_a_4235_, lean_object* v___f_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v___x_4250_; 
v___x_4250_ = l_Lean_Meta_Grind_Action_andThen(v_a_4235_, v___f_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_);
return v___x_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed(lean_object* v_a_4251_, lean_object* v___f_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__1(v_a_4251_, v___f_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_dec(v___y_4256_);
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction(){
_start:
{
lean_object* v___x_4269_; 
v___x_4269_ = l_Lean_Meta_Grind_Solvers_mkActionCore();
if (lean_obj_tag(v___x_4269_) == 0)
{
lean_object* v_a_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4279_; 
v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4272_ = v___x_4269_;
v_isShared_4273_ = v_isSharedCheck_4279_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_a_4270_);
lean_dec(v___x_4269_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4279_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___f_4274_; lean_object* v___f_4275_; lean_object* v___x_4277_; 
v___f_4274_ = ((lean_object*)(l_Lean_Meta_Grind_Solvers_mkAction___closed__0));
v___f_4275_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed), 15, 2);
lean_closure_set(v___f_4275_, 0, v_a_4270_);
lean_closure_set(v___f_4275_, 1, v___f_4274_);
if (v_isShared_4273_ == 0)
{
lean_ctor_set(v___x_4272_, 0, v___f_4275_);
v___x_4277_ = v___x_4272_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v___f_4275_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
}
else
{
return v___x_4269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___boxed(lean_object* v_a_4280_){
_start:
{
lean_object* v_res_4281_; 
v_res_4281_ = l_Lean_Meta_Grind_Solvers_mkAction();
return v_res_4281_;
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
