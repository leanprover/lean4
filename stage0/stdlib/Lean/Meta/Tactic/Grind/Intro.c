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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
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
lean_object* lean_grind_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_getLocalInstances___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__1;
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
lean_inc(v_a_89_);
v___x_98_ = lean_grind_canon(v_val_97_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v___x_100_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_a_99_);
lean_dec_ref(v___x_98_);
v___x_100_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_99_, v_a_89_);
lean_dec(v_a_89_);
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
lean_dec(v_a_89_);
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
v___x_128_ = lean_grind_preprocess(v_e_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
return v___x_128_;
}
}
else
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = l_Lean_Meta_Grind_markAsPreMatchCond(v_e_83_);
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
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(lean_object* v___x_144_, lean_object* v_suffix_145_, lean_object* v___x_146_, lean_object* v_str_147_, lean_object* v_a_148_, lean_object* v_b_149_){
_start:
{
lean_object* v_startInclusive_150_; lean_object* v_endExclusive_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v_startInclusive_150_ = lean_ctor_get(v_suffix_145_, 1);
v_endExclusive_151_ = lean_ctor_get(v_suffix_145_, 2);
v___x_152_ = lean_nat_sub(v_endExclusive_151_, v_startInclusive_150_);
v___x_153_ = lean_nat_dec_eq(v_a_148_, v___x_152_);
lean_dec(v___x_152_);
if (v___x_153_ == 0)
{
lean_object* v_snd_154_; lean_object* v_snd_155_; lean_object* v_fst_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_220_; 
v_snd_154_ = lean_ctor_get(v_b_149_, 1);
lean_inc(v_snd_154_);
v_snd_155_ = lean_ctor_get(v_snd_154_, 1);
lean_inc(v_snd_155_);
v_fst_156_ = lean_ctor_get(v_b_149_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v_b_149_);
if (v_isSharedCheck_220_ == 0)
{
lean_object* v_unused_221_; 
v_unused_221_ = lean_ctor_get(v_b_149_, 1);
lean_dec(v_unused_221_);
v___x_158_ = v_b_149_;
v_isShared_159_ = v_isSharedCheck_220_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_fst_156_);
lean_dec(v_b_149_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_220_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v_fst_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_218_; 
v_fst_160_ = lean_ctor_get(v_snd_154_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v_snd_154_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v_snd_154_, 1);
lean_dec(v_unused_219_);
v___x_162_ = v_snd_154_;
v_isShared_163_ = v_isSharedCheck_218_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_fst_160_);
lean_dec(v_snd_154_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_218_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v_snd_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_216_; 
v_snd_164_ = lean_ctor_get(v_snd_155_, 1);
v_isSharedCheck_216_ = !lean_is_exclusive(v_snd_155_);
if (v_isSharedCheck_216_ == 0)
{
lean_object* v_unused_217_; 
v_unused_217_ = lean_ctor_get(v_snd_155_, 0);
lean_dec(v_unused_217_);
v___x_166_ = v_snd_155_;
v_isShared_167_ = v_isSharedCheck_216_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_snd_164_);
lean_dec(v_snd_155_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_216_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; uint8_t v___x_169_; uint8_t v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; uint32_t v___x_174_; uint8_t v___y_176_; uint8_t v___y_177_; uint8_t v___y_195_; uint8_t v___y_196_; uint8_t v___y_201_; uint8_t v___y_202_; uint8_t v___y_207_; uint32_t v___x_212_; uint8_t v___x_213_; 
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = lean_nat_dec_eq(v___x_144_, v___x_168_);
v___x_170_ = 1;
v___x_171_ = lean_nat_add(v___x_146_, v_a_148_);
lean_dec(v_a_148_);
v___x_172_ = lean_string_utf8_next_fast(v_str_147_, v___x_171_);
v___x_173_ = lean_nat_sub(v___x_172_, v___x_146_);
v___x_174_ = lean_string_utf8_get_fast(v_str_147_, v___x_171_);
lean_dec(v___x_171_);
v___x_212_ = 48;
v___x_213_ = lean_uint32_dec_le(v___x_212_, v___x_174_);
if (v___x_213_ == 0)
{
v___y_207_ = v___x_213_;
goto v___jp_206_;
}
else
{
uint32_t v___x_214_; uint8_t v___x_215_; 
v___x_214_ = 57;
v___x_215_ = lean_uint32_dec_le(v___x_174_, v___x_214_);
v___y_207_ = v___x_215_;
goto v___jp_206_;
}
v___jp_175_:
{
uint32_t v___x_178_; uint8_t v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_178_ = 95;
v___x_179_ = lean_uint32_dec_eq(v___x_174_, v___x_178_);
v___x_180_ = lean_box(v___y_176_);
v___x_181_ = lean_box(v___y_177_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v___x_181_);
lean_ctor_set(v___x_166_, 0, v___x_180_);
v___x_183_ = v___x_166_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_180_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v___x_181_);
v___x_183_ = v_reuseFailAlloc_193_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_184_ = lean_box(v___x_179_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 1, v___x_183_);
lean_ctor_set(v___x_162_, 0, v___x_184_);
v___x_186_ = v___x_162_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v___x_183_);
v___x_186_ = v_reuseFailAlloc_192_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_187_ = lean_box(v___x_169_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 1, v___x_186_);
lean_ctor_set(v___x_158_, 0, v___x_187_);
v___x_189_ = v___x_158_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v___x_186_);
v___x_189_ = v_reuseFailAlloc_191_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
v_a_148_ = v___x_173_;
v_b_149_ = v___x_189_;
goto _start;
}
}
}
}
v___jp_194_:
{
uint8_t v___x_197_; 
v___x_197_ = lean_unbox(v_fst_160_);
lean_dec(v_fst_160_);
if (v___x_197_ == 0)
{
v___y_176_ = v___y_195_;
v___y_177_ = v___y_196_;
goto v___jp_175_;
}
else
{
uint32_t v___x_198_; uint8_t v___x_199_; 
v___x_198_ = 95;
v___x_199_ = lean_uint32_dec_eq(v___x_174_, v___x_198_);
if (v___x_199_ == 0)
{
v___y_176_ = v___y_195_;
v___y_177_ = v___y_196_;
goto v___jp_175_;
}
else
{
v___y_176_ = v___y_195_;
v___y_177_ = v___x_169_;
goto v___jp_175_;
}
}
}
v___jp_200_:
{
uint8_t v___x_203_; 
v___x_203_ = lean_unbox(v_fst_156_);
lean_dec(v_fst_156_);
if (v___x_203_ == 0)
{
v___y_195_ = v___y_201_;
v___y_196_ = v___y_202_;
goto v___jp_194_;
}
else
{
uint32_t v___x_204_; uint8_t v___x_205_; 
v___x_204_ = 95;
v___x_205_ = lean_uint32_dec_eq(v___x_174_, v___x_204_);
if (v___x_205_ == 0)
{
v___y_195_ = v___y_201_;
v___y_196_ = v___y_202_;
goto v___jp_194_;
}
else
{
if (v___x_169_ == 0)
{
lean_dec(v_fst_160_);
v___y_176_ = v___y_201_;
v___y_177_ = v___x_169_;
goto v___jp_175_;
}
else
{
v___y_195_ = v___y_201_;
v___y_196_ = v___x_169_;
goto v___jp_194_;
}
}
}
}
v___jp_206_:
{
uint8_t v___x_208_; 
v___x_208_ = lean_unbox(v_snd_164_);
if (v___x_208_ == 0)
{
uint8_t v___x_209_; 
lean_dec(v_fst_160_);
lean_dec(v_fst_156_);
v___x_209_ = lean_unbox(v_snd_164_);
lean_dec(v_snd_164_);
v___y_176_ = v___y_207_;
v___y_177_ = v___x_209_;
goto v___jp_175_;
}
else
{
lean_dec(v_snd_164_);
if (v___y_207_ == 0)
{
uint32_t v___x_210_; uint8_t v___x_211_; 
v___x_210_ = 95;
v___x_211_ = lean_uint32_dec_eq(v___x_174_, v___x_210_);
if (v___x_211_ == 0)
{
lean_dec(v_fst_160_);
lean_dec(v_fst_156_);
v___y_176_ = v___y_207_;
v___y_177_ = v___x_211_;
goto v___jp_175_;
}
else
{
v___y_201_ = v___y_207_;
v___y_202_ = v___x_211_;
goto v___jp_200_;
}
}
else
{
v___y_201_ = v___y_207_;
v___y_202_ = v___x_170_;
goto v___jp_200_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_148_);
return v_b_149_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg___boxed(lean_object* v___x_222_, lean_object* v_suffix_223_, lean_object* v___x_224_, lean_object* v_str_225_, lean_object* v_a_226_, lean_object* v_b_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_222_, v_suffix_223_, v___x_224_, v_str_225_, v_a_226_, v_b_227_);
lean_dec_ref(v_str_225_);
lean_dec(v___x_224_);
lean_dec_ref(v_suffix_223_);
lean_dec(v___x_222_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__1___redArg(lean_object* v___x_229_, lean_object* v_str_230_, lean_object* v_a_231_, lean_object* v_b_232_){
_start:
{
lean_object* v_startInclusive_233_; lean_object* v_endExclusive_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v_startInclusive_233_ = lean_ctor_get(v___x_229_, 1);
v_endExclusive_234_ = lean_ctor_get(v___x_229_, 2);
v___x_235_ = lean_nat_sub(v_endExclusive_234_, v_startInclusive_233_);
v___x_236_ = lean_nat_dec_eq(v_a_231_, v___x_235_);
lean_dec(v___x_235_);
if (v___x_236_ == 0)
{
uint32_t v___x_237_; uint32_t v___x_238_; uint8_t v___x_239_; 
lean_dec(v_b_232_);
v___x_237_ = lean_string_utf8_get_fast(v_str_230_, v_a_231_);
v___x_238_ = 95;
v___x_239_ = lean_uint32_dec_eq(v___x_237_, v___x_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_box(0);
v___x_241_ = lean_string_utf8_next_fast(v_str_230_, v_a_231_);
lean_dec(v_a_231_);
v_a_231_ = v___x_241_;
v_b_232_ = v___x_240_;
goto _start;
}
else
{
lean_object* v___x_243_; 
v___x_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_243_, 0, v_a_231_);
return v___x_243_;
}
}
else
{
lean_dec(v_a_231_);
return v_b_232_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__1___redArg___boxed(lean_object* v___x_244_, lean_object* v_str_245_, lean_object* v_a_246_, lean_object* v_b_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__1___redArg(v___x_244_, v_str_245_, v_a_246_, v_b_247_);
lean_dec_ref(v_str_245_);
lean_dec_ref(v___x_244_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(lean_object* v_name_255_, lean_object* v_type_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v___y_266_; 
if (lean_obj_tag(v_name_255_) == 1)
{
lean_object* v_str_290_; lean_object* v___y_296_; uint8_t v___y_297_; lean_object* v___y_305_; lean_object* v_searcher_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v_str_290_ = lean_ctor_get(v_name_255_, 1);
lean_inc_ref(v_str_290_);
lean_dec_ref(v_name_255_);
v_searcher_332_ = lean_unsigned_to_nat(0u);
v___x_333_ = lean_string_utf8_byte_size(v_str_290_);
lean_inc_ref(v_str_290_);
v___x_334_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_334_, 0, v_str_290_);
lean_ctor_set(v___x_334_, 1, v_searcher_332_);
lean_ctor_set(v___x_334_, 2, v___x_333_);
v___x_335_ = lean_box(0);
v___x_336_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__1___redArg(v___x_334_, v_str_290_, v_searcher_332_, v___x_335_);
lean_dec_ref(v___x_334_);
if (lean_obj_tag(v___x_336_) == 0)
{
v___y_305_ = v___x_333_;
goto v___jp_304_;
}
else
{
lean_object* v_val_337_; 
v_val_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_val_337_);
lean_dec_ref(v___x_336_);
v___y_305_ = v_val_337_;
goto v___jp_304_;
}
v___jp_291_:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = lean_box(0);
v___x_293_ = l_Lean_Name_str___override(v___x_292_, v_str_290_);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
v___jp_295_:
{
if (v___y_297_ == 0)
{
lean_dec(v___y_296_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec_ref(v_type_256_);
goto v___jp_291_;
}
else
{
lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = lean_nat_dec_eq(v___y_296_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec_ref(v_type_256_);
v___x_300_ = lean_string_utf8_extract(v_str_290_, v___x_298_, v___y_296_);
lean_dec(v___y_296_);
lean_dec_ref(v_str_290_);
v___x_301_ = lean_box(0);
v___x_302_ = l_Lean_Name_str___override(v___x_301_, v___x_300_);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
else
{
lean_dec(v___y_296_);
lean_dec_ref(v_str_290_);
v___y_263_ = v_a_257_;
v___y_264_ = v_a_258_;
v___y_265_ = v_a_259_;
v___y_266_ = v_a_260_;
goto v___jp_262_;
}
}
}
v___jp_304_:
{
lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_306_ = lean_string_utf8_byte_size(v_str_290_);
v___x_307_ = lean_nat_dec_eq(v___y_305_, v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_308_ = lean_string_utf8_next_fast(v_str_290_, v___y_305_);
v___x_309_ = lean_nat_sub(v___x_306_, v___x_308_);
v___x_310_ = lean_unsigned_to_nat(0u);
v___x_311_ = lean_nat_dec_eq(v___x_309_, v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v_suffix_312_; uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v_result_322_; lean_object* v_snd_323_; lean_object* v_snd_324_; lean_object* v_snd_325_; uint8_t v___x_326_; 
lean_inc_ref(v_str_290_);
v_suffix_312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_suffix_312_, 0, v_str_290_);
lean_ctor_set(v_suffix_312_, 1, v___x_308_);
lean_ctor_set(v_suffix_312_, 2, v___x_306_);
v___x_313_ = 1;
v___x_314_ = lean_box(v___x_311_);
v___x_315_ = lean_box(v___x_313_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = lean_box(v___x_311_);
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v___x_316_);
v___x_319_ = lean_box(v___x_313_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v___x_318_);
v___x_321_ = l_String_Slice_positions(v_suffix_312_);
v_result_322_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_309_, v_suffix_312_, v___x_308_, v_str_290_, v___x_321_, v___x_320_);
lean_dec_ref(v_suffix_312_);
lean_dec(v___x_309_);
v_snd_323_ = lean_ctor_get(v_result_322_, 1);
lean_inc(v_snd_323_);
lean_dec_ref(v_result_322_);
v_snd_324_ = lean_ctor_get(v_snd_323_, 1);
lean_inc(v_snd_324_);
lean_dec(v_snd_323_);
v_snd_325_ = lean_ctor_get(v_snd_324_, 1);
v___x_326_ = lean_unbox(v_snd_325_);
if (v___x_326_ == 0)
{
lean_dec(v_snd_324_);
v___y_296_ = v___y_305_;
v___y_297_ = v___x_311_;
goto v___jp_295_;
}
else
{
lean_object* v_fst_327_; uint8_t v___x_328_; 
v_fst_327_ = lean_ctor_get(v_snd_324_, 0);
lean_inc(v_fst_327_);
lean_dec(v_snd_324_);
v___x_328_ = lean_unbox(v_fst_327_);
lean_dec(v_fst_327_);
v___y_296_ = v___y_305_;
v___y_297_ = v___x_328_;
goto v___jp_295_;
}
}
else
{
lean_dec(v___x_309_);
lean_dec(v___y_305_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec_ref(v_type_256_);
goto v___jp_291_;
}
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec(v___y_305_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec_ref(v_type_256_);
v___x_329_ = lean_box(0);
v___x_330_ = l_Lean_Name_str___override(v___x_329_, v_str_290_);
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
return v___x_331_;
}
}
}
else
{
lean_dec(v_name_255_);
v___y_263_ = v_a_257_;
v___y_264_ = v_a_258_;
v___y_265_ = v_a_259_;
v___y_266_ = v_a_260_;
goto v___jp_262_;
}
v___jp_262_:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_Meta_isProp(v_type_256_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_281_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_281_ == 0)
{
v___x_270_ = v___x_267_;
v_isShared_271_ = v_isSharedCheck_281_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_267_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_281_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
uint8_t v___x_272_; 
v___x_272_ = lean_unbox(v_a_268_);
lean_dec(v_a_268_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_273_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_273_);
v___x_275_ = v___x_270_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
else
{
lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_277_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_277_);
v___x_279_ = v___x_270_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
else
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
v_a_282_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_267_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_267_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___boxed(lean_object* v_name_338_, lean_object* v_type_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(v_name_338_, v_type_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0(lean_object* v___x_346_, lean_object* v_suffix_347_, lean_object* v___x_348_, lean_object* v_str_349_, lean_object* v_inst_350_, lean_object* v_R_351_, lean_object* v_a_352_, lean_object* v_b_353_, lean_object* v_c_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_346_, v_suffix_347_, v___x_348_, v_str_349_, v_a_352_, v_b_353_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___boxed(lean_object* v___x_356_, lean_object* v_suffix_357_, lean_object* v___x_358_, lean_object* v_str_359_, lean_object* v_inst_360_, lean_object* v_R_361_, lean_object* v_a_362_, lean_object* v_b_363_, lean_object* v_c_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0(v___x_356_, v_suffix_357_, v___x_358_, v_str_359_, v_inst_360_, v_R_361_, v_a_362_, v_b_363_, v_c_364_);
lean_dec_ref(v_str_359_);
lean_dec(v___x_358_);
lean_dec_ref(v_suffix_357_);
lean_dec(v___x_356_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__1(lean_object* v___x_366_, lean_object* v_str_367_, lean_object* v_inst_368_, lean_object* v_R_369_, lean_object* v_a_370_, lean_object* v_b_371_, lean_object* v_c_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__1___redArg(v___x_366_, v_str_367_, v_a_370_, v_b_371_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__1___boxed(lean_object* v___x_374_, lean_object* v_str_375_, lean_object* v_inst_376_, lean_object* v_R_377_, lean_object* v_a_378_, lean_object* v_b_379_, lean_object* v_c_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__1(v___x_374_, v_str_375_, v_inst_376_, v_R_377_, v_a_378_, v_b_379_, v_c_380_);
lean_dec_ref(v_str_375_);
lean_dec_ref(v___x_374_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_382_, lean_object* v_x_383_, lean_object* v_x_384_, lean_object* v_x_385_){
_start:
{
lean_object* v_ks_386_; lean_object* v_vs_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_411_; 
v_ks_386_ = lean_ctor_get(v_x_382_, 0);
v_vs_387_ = lean_ctor_get(v_x_382_, 1);
v_isSharedCheck_411_ = !lean_is_exclusive(v_x_382_);
if (v_isSharedCheck_411_ == 0)
{
v___x_389_ = v_x_382_;
v_isShared_390_ = v_isSharedCheck_411_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_vs_387_);
lean_inc(v_ks_386_);
lean_dec(v_x_382_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_411_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_391_ = lean_array_get_size(v_ks_386_);
v___x_392_ = lean_nat_dec_lt(v_x_383_, v___x_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
lean_dec(v_x_383_);
v___x_393_ = lean_array_push(v_ks_386_, v_x_384_);
v___x_394_ = lean_array_push(v_vs_387_, v_x_385_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 1, v___x_394_);
lean_ctor_set(v___x_389_, 0, v___x_393_);
v___x_396_ = v___x_389_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v___x_394_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
else
{
lean_object* v_k_x27_398_; uint8_t v___x_399_; 
v_k_x27_398_ = lean_array_fget_borrowed(v_ks_386_, v_x_383_);
v___x_399_ = lean_name_eq(v_x_384_, v_k_x27_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_401_; 
if (v_isShared_390_ == 0)
{
v___x_401_ = v___x_389_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_ks_386_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_vs_387_);
v___x_401_ = v_reuseFailAlloc_405_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_unsigned_to_nat(1u);
v___x_403_ = lean_nat_add(v_x_383_, v___x_402_);
lean_dec(v_x_383_);
v_x_382_ = v___x_401_;
v_x_383_ = v___x_403_;
goto _start;
}
}
else
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_406_ = lean_array_fset(v_ks_386_, v_x_383_, v_x_384_);
v___x_407_ = lean_array_fset(v_vs_387_, v_x_383_, v_x_385_);
lean_dec(v_x_383_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 1, v___x_407_);
lean_ctor_set(v___x_389_, 0, v___x_406_);
v___x_409_ = v___x_389_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_406_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(lean_object* v_n_412_, lean_object* v_k_413_, lean_object* v_v_414_){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(v_n_412_, v___x_415_, v_k_413_, v_v_414_);
return v___x_416_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_417_; uint64_t v___x_418_; 
v___x_417_ = lean_unsigned_to_nat(1723u);
v___x_418_ = lean_uint64_of_nat(v___x_417_);
return v___x_418_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_419_; size_t v___x_420_; size_t v___x_421_; 
v___x_419_ = ((size_t)5ULL);
v___x_420_ = ((size_t)1ULL);
v___x_421_ = lean_usize_shift_left(v___x_420_, v___x_419_);
return v___x_421_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_422_; size_t v___x_423_; size_t v___x_424_; 
v___x_422_ = ((size_t)1ULL);
v___x_423_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0);
v___x_424_ = lean_usize_sub(v___x_423_, v___x_422_);
return v___x_424_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(lean_object* v_x_426_, size_t v_x_427_, size_t v_x_428_, lean_object* v_x_429_, lean_object* v_x_430_){
_start:
{
if (lean_obj_tag(v_x_426_) == 0)
{
lean_object* v_es_431_; size_t v___x_432_; size_t v___x_433_; size_t v___x_434_; size_t v___x_435_; lean_object* v_j_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v_es_431_ = lean_ctor_get(v_x_426_, 0);
v___x_432_ = ((size_t)5ULL);
v___x_433_ = ((size_t)1ULL);
v___x_434_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1);
v___x_435_ = lean_usize_land(v_x_427_, v___x_434_);
v_j_436_ = lean_usize_to_nat(v___x_435_);
v___x_437_ = lean_array_get_size(v_es_431_);
v___x_438_ = lean_nat_dec_lt(v_j_436_, v___x_437_);
if (v___x_438_ == 0)
{
lean_dec(v_j_436_);
lean_dec(v_x_430_);
lean_dec(v_x_429_);
return v_x_426_;
}
else
{
lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_475_; 
lean_inc_ref(v_es_431_);
v_isSharedCheck_475_ = !lean_is_exclusive(v_x_426_);
if (v_isSharedCheck_475_ == 0)
{
lean_object* v_unused_476_; 
v_unused_476_ = lean_ctor_get(v_x_426_, 0);
lean_dec(v_unused_476_);
v___x_440_ = v_x_426_;
v_isShared_441_ = v_isSharedCheck_475_;
goto v_resetjp_439_;
}
else
{
lean_dec(v_x_426_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_475_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v_v_442_; lean_object* v___x_443_; lean_object* v_xs_x27_444_; lean_object* v___y_446_; 
v_v_442_ = lean_array_fget(v_es_431_, v_j_436_);
v___x_443_ = lean_box(0);
v_xs_x27_444_ = lean_array_fset(v_es_431_, v_j_436_, v___x_443_);
switch(lean_obj_tag(v_v_442_))
{
case 0:
{
lean_object* v_key_451_; lean_object* v_val_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_462_; 
v_key_451_ = lean_ctor_get(v_v_442_, 0);
v_val_452_ = lean_ctor_get(v_v_442_, 1);
v_isSharedCheck_462_ = !lean_is_exclusive(v_v_442_);
if (v_isSharedCheck_462_ == 0)
{
v___x_454_ = v_v_442_;
v_isShared_455_ = v_isSharedCheck_462_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_val_452_);
lean_inc(v_key_451_);
lean_dec(v_v_442_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_462_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
uint8_t v___x_456_; 
v___x_456_ = lean_name_eq(v_x_429_, v_key_451_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; 
lean_del_object(v___x_454_);
v___x_457_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_451_, v_val_452_, v_x_429_, v_x_430_);
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
v___y_446_ = v___x_458_;
goto v___jp_445_;
}
else
{
lean_object* v___x_460_; 
lean_dec(v_val_452_);
lean_dec(v_key_451_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 1, v_x_430_);
lean_ctor_set(v___x_454_, 0, v_x_429_);
v___x_460_ = v___x_454_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_x_429_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_x_430_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
v___y_446_ = v___x_460_;
goto v___jp_445_;
}
}
}
}
case 1:
{
lean_object* v_node_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_473_; 
v_node_463_ = lean_ctor_get(v_v_442_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v_v_442_);
if (v_isSharedCheck_473_ == 0)
{
v___x_465_ = v_v_442_;
v_isShared_466_ = v_isSharedCheck_473_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_node_463_);
lean_dec(v_v_442_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_473_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
size_t v___x_467_; size_t v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_467_ = lean_usize_shift_right(v_x_427_, v___x_432_);
v___x_468_ = lean_usize_add(v_x_428_, v___x_433_);
v___x_469_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_node_463_, v___x_467_, v___x_468_, v_x_429_, v_x_430_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v___x_469_);
v___x_471_ = v___x_465_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_469_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
v___y_446_ = v___x_471_;
goto v___jp_445_;
}
}
}
default: 
{
lean_object* v___x_474_; 
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v_x_429_);
lean_ctor_set(v___x_474_, 1, v_x_430_);
v___y_446_ = v___x_474_;
goto v___jp_445_;
}
}
v___jp_445_:
{
lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_447_ = lean_array_fset(v_xs_x27_444_, v_j_436_, v___y_446_);
lean_dec(v_j_436_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_447_);
v___x_449_ = v___x_440_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
}
else
{
lean_object* v_ks_477_; lean_object* v_vs_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_498_; 
v_ks_477_ = lean_ctor_get(v_x_426_, 0);
v_vs_478_ = lean_ctor_get(v_x_426_, 1);
v_isSharedCheck_498_ = !lean_is_exclusive(v_x_426_);
if (v_isSharedCheck_498_ == 0)
{
v___x_480_ = v_x_426_;
v_isShared_481_ = v_isSharedCheck_498_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_vs_478_);
lean_inc(v_ks_477_);
lean_dec(v_x_426_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_498_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_ks_477_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_vs_478_);
v___x_483_ = v_reuseFailAlloc_497_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v_newNode_484_; uint8_t v___y_486_; size_t v___x_492_; uint8_t v___x_493_; 
v_newNode_484_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(v___x_483_, v_x_429_, v_x_430_);
v___x_492_ = ((size_t)7ULL);
v___x_493_ = lean_usize_dec_le(v___x_492_, v_x_428_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_494_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_484_);
v___x_495_ = lean_unsigned_to_nat(4u);
v___x_496_ = lean_nat_dec_lt(v___x_494_, v___x_495_);
lean_dec(v___x_494_);
v___y_486_ = v___x_496_;
goto v___jp_485_;
}
else
{
v___y_486_ = v___x_493_;
goto v___jp_485_;
}
v___jp_485_:
{
if (v___y_486_ == 0)
{
lean_object* v_ks_487_; lean_object* v_vs_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v_ks_487_ = lean_ctor_get(v_newNode_484_, 0);
lean_inc_ref(v_ks_487_);
v_vs_488_ = lean_ctor_get(v_newNode_484_, 1);
lean_inc_ref(v_vs_488_);
lean_dec_ref(v_newNode_484_);
v___x_489_ = lean_unsigned_to_nat(0u);
v___x_490_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__2);
v___x_491_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_x_428_, v_ks_487_, v_vs_488_, v___x_489_, v___x_490_);
lean_dec_ref(v_vs_488_);
lean_dec_ref(v_ks_487_);
return v___x_491_;
}
else
{
return v_newNode_484_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(size_t v_depth_499_, lean_object* v_keys_500_, lean_object* v_vals_501_, lean_object* v_i_502_, lean_object* v_entries_503_){
_start:
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = lean_array_get_size(v_keys_500_);
v___x_505_ = lean_nat_dec_lt(v_i_502_, v___x_504_);
if (v___x_505_ == 0)
{
lean_dec(v_i_502_);
return v_entries_503_;
}
else
{
lean_object* v_k_506_; lean_object* v_v_507_; uint64_t v___y_509_; 
v_k_506_ = lean_array_fget_borrowed(v_keys_500_, v_i_502_);
v_v_507_ = lean_array_fget_borrowed(v_vals_501_, v_i_502_);
if (lean_obj_tag(v_k_506_) == 0)
{
uint64_t v___x_520_; 
v___x_520_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_509_ = v___x_520_;
goto v___jp_508_;
}
else
{
uint64_t v_hash_521_; 
v_hash_521_ = lean_ctor_get_uint64(v_k_506_, sizeof(void*)*2);
v___y_509_ = v_hash_521_;
goto v___jp_508_;
}
v___jp_508_:
{
size_t v_h_510_; size_t v___x_511_; lean_object* v___x_512_; size_t v___x_513_; size_t v___x_514_; size_t v___x_515_; size_t v_h_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v_h_510_ = lean_uint64_to_usize(v___y_509_);
v___x_511_ = ((size_t)5ULL);
v___x_512_ = lean_unsigned_to_nat(1u);
v___x_513_ = ((size_t)1ULL);
v___x_514_ = lean_usize_sub(v_depth_499_, v___x_513_);
v___x_515_ = lean_usize_mul(v___x_511_, v___x_514_);
v_h_516_ = lean_usize_shift_right(v_h_510_, v___x_515_);
v___x_517_ = lean_nat_add(v_i_502_, v___x_512_);
lean_dec(v_i_502_);
lean_inc(v_v_507_);
lean_inc(v_k_506_);
v___x_518_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_entries_503_, v_h_516_, v_depth_499_, v_k_506_, v_v_507_);
v_i_502_ = v___x_517_;
v_entries_503_ = v___x_518_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_522_, lean_object* v_keys_523_, lean_object* v_vals_524_, lean_object* v_i_525_, lean_object* v_entries_526_){
_start:
{
size_t v_depth_boxed_527_; lean_object* v_res_528_; 
v_depth_boxed_527_ = lean_unbox_usize(v_depth_522_);
lean_dec(v_depth_522_);
v_res_528_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_depth_boxed_527_, v_keys_523_, v_vals_524_, v_i_525_, v_entries_526_);
lean_dec_ref(v_vals_524_);
lean_dec_ref(v_keys_523_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___boxed(lean_object* v_x_529_, lean_object* v_x_530_, lean_object* v_x_531_, lean_object* v_x_532_, lean_object* v_x_533_){
_start:
{
size_t v_x_37561__boxed_534_; size_t v_x_37562__boxed_535_; lean_object* v_res_536_; 
v_x_37561__boxed_534_ = lean_unbox_usize(v_x_530_);
lean_dec(v_x_530_);
v_x_37562__boxed_535_ = lean_unbox_usize(v_x_531_);
lean_dec(v_x_531_);
v_res_536_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_529_, v_x_37561__boxed_534_, v_x_37562__boxed_535_, v_x_532_, v_x_533_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(lean_object* v_x_537_, lean_object* v_x_538_, lean_object* v_x_539_){
_start:
{
uint64_t v___y_541_; 
if (lean_obj_tag(v_x_538_) == 0)
{
uint64_t v___x_545_; 
v___x_545_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_541_ = v___x_545_;
goto v___jp_540_;
}
else
{
uint64_t v_hash_546_; 
v_hash_546_ = lean_ctor_get_uint64(v_x_538_, sizeof(void*)*2);
v___y_541_ = v_hash_546_;
goto v___jp_540_;
}
v___jp_540_:
{
size_t v___x_542_; size_t v___x_543_; lean_object* v___x_544_; 
v___x_542_ = lean_uint64_to_usize(v___y_541_);
v___x_543_ = ((size_t)1ULL);
v___x_544_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_537_, v___x_542_, v___x_543_, v_x_538_, v_x_539_);
return v___x_544_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(lean_object* v_keys_547_, lean_object* v_i_548_, lean_object* v_k_549_){
_start:
{
lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_550_ = lean_array_get_size(v_keys_547_);
v___x_551_ = lean_nat_dec_lt(v_i_548_, v___x_550_);
if (v___x_551_ == 0)
{
lean_dec(v_i_548_);
return v___x_551_;
}
else
{
lean_object* v_k_x27_552_; uint8_t v___x_553_; 
v_k_x27_552_ = lean_array_fget_borrowed(v_keys_547_, v_i_548_);
v___x_553_ = lean_name_eq(v_k_549_, v_k_x27_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = lean_unsigned_to_nat(1u);
v___x_555_ = lean_nat_add(v_i_548_, v___x_554_);
lean_dec(v_i_548_);
v_i_548_ = v___x_555_;
goto _start;
}
else
{
lean_dec(v_i_548_);
return v___x_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_keys_557_, lean_object* v_i_558_, lean_object* v_k_559_){
_start:
{
uint8_t v_res_560_; lean_object* v_r_561_; 
v_res_560_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_keys_557_, v_i_558_, v_k_559_);
lean_dec(v_k_559_);
lean_dec_ref(v_keys_557_);
v_r_561_ = lean_box(v_res_560_);
return v_r_561_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(lean_object* v_x_562_, size_t v_x_563_, lean_object* v_x_564_){
_start:
{
if (lean_obj_tag(v_x_562_) == 0)
{
lean_object* v_es_565_; lean_object* v___x_566_; size_t v___x_567_; size_t v___x_568_; size_t v___x_569_; lean_object* v_j_570_; lean_object* v___x_571_; 
v_es_565_ = lean_ctor_get(v_x_562_, 0);
lean_inc_ref(v_es_565_);
lean_dec_ref(v_x_562_);
v___x_566_ = lean_box(2);
v___x_567_ = ((size_t)5ULL);
v___x_568_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1);
v___x_569_ = lean_usize_land(v_x_563_, v___x_568_);
v_j_570_ = lean_usize_to_nat(v___x_569_);
v___x_571_ = lean_array_get(v___x_566_, v_es_565_, v_j_570_);
lean_dec(v_j_570_);
lean_dec_ref(v_es_565_);
switch(lean_obj_tag(v___x_571_))
{
case 0:
{
lean_object* v_key_572_; uint8_t v___x_573_; 
v_key_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_key_572_);
lean_dec_ref(v___x_571_);
v___x_573_ = lean_name_eq(v_x_564_, v_key_572_);
lean_dec(v_key_572_);
return v___x_573_;
}
case 1:
{
lean_object* v_node_574_; size_t v___x_575_; 
v_node_574_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_node_574_);
lean_dec_ref(v___x_571_);
v___x_575_ = lean_usize_shift_right(v_x_563_, v___x_567_);
v_x_562_ = v_node_574_;
v_x_563_ = v___x_575_;
goto _start;
}
default: 
{
uint8_t v___x_577_; 
v___x_577_ = 0;
return v___x_577_;
}
}
}
else
{
lean_object* v_ks_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v_ks_578_ = lean_ctor_get(v_x_562_, 0);
lean_inc_ref(v_ks_578_);
lean_dec_ref(v_x_562_);
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_ks_578_, v___x_579_, v_x_564_);
lean_dec_ref(v_ks_578_);
return v___x_580_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___boxed(lean_object* v_x_581_, lean_object* v_x_582_, lean_object* v_x_583_){
_start:
{
size_t v_x_37766__boxed_584_; uint8_t v_res_585_; lean_object* v_r_586_; 
v_x_37766__boxed_584_ = lean_unbox_usize(v_x_582_);
lean_dec(v_x_582_);
v_res_585_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_581_, v_x_37766__boxed_584_, v_x_583_);
lean_dec(v_x_583_);
v_r_586_ = lean_box(v_res_585_);
return v_r_586_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(lean_object* v_x_587_, lean_object* v_x_588_){
_start:
{
uint64_t v___y_590_; 
if (lean_obj_tag(v_x_588_) == 0)
{
uint64_t v___x_593_; 
v___x_593_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_590_ = v___x_593_;
goto v___jp_589_;
}
else
{
uint64_t v_hash_594_; 
v_hash_594_ = lean_ctor_get_uint64(v_x_588_, sizeof(void*)*2);
v___y_590_ = v_hash_594_;
goto v___jp_589_;
}
v___jp_589_:
{
size_t v___x_591_; uint8_t v___x_592_; 
v___x_591_ = lean_uint64_to_usize(v___y_590_);
v___x_592_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_587_, v___x_591_, v_x_588_);
return v___x_592_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___boxed(lean_object* v_x_595_, lean_object* v_x_596_){
_start:
{
uint8_t v_res_597_; lean_object* v_r_598_; 
v_res_597_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_x_595_, v_x_596_);
lean_dec(v_x_596_);
v_r_598_ = lean_box(v_res_597_);
return v_r_598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(lean_object* v_a_599_, lean_object* v_b_600_, lean_object* v___y_601_){
_start:
{
lean_object* v___x_603_; lean_object* v_toGoalState_604_; lean_object* v_clean_605_; lean_object* v_snd_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_623_; 
v___x_603_ = lean_st_ref_get(v___y_601_);
v_toGoalState_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc_ref(v_toGoalState_604_);
lean_dec(v___x_603_);
v_clean_605_ = lean_ctor_get(v_toGoalState_604_, 16);
lean_inc_ref(v_clean_605_);
lean_dec_ref(v_toGoalState_604_);
v_snd_606_ = lean_ctor_get(v_b_600_, 1);
v_isSharedCheck_623_ = !lean_is_exclusive(v_b_600_);
if (v_isSharedCheck_623_ == 0)
{
lean_object* v_unused_624_; 
v_unused_624_ = lean_ctor_get(v_b_600_, 0);
lean_dec(v_unused_624_);
v___x_608_ = v_b_600_;
v_isShared_609_ = v_isSharedCheck_623_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_snd_606_);
lean_dec(v_b_600_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_623_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v_used_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v_used_610_ = lean_ctor_get(v_clean_605_, 0);
lean_inc_ref(v_used_610_);
lean_dec_ref(v_clean_605_);
lean_inc(v_snd_606_);
lean_inc(v_a_599_);
v___x_611_ = lean_name_append_index_after(v_a_599_, v_snd_606_);
v___x_612_ = lean_unsigned_to_nat(1u);
v___x_613_ = lean_nat_add(v_snd_606_, v___x_612_);
lean_dec(v_snd_606_);
v___x_614_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_used_610_, v___x_611_);
if (v___x_614_ == 0)
{
lean_object* v___x_616_; 
lean_dec(v_a_599_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 1, v___x_613_);
lean_ctor_set(v___x_608_, 0, v___x_611_);
v___x_616_ = v___x_608_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v___x_613_);
v___x_616_ = v_reuseFailAlloc_618_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_617_; 
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
return v___x_617_;
}
}
else
{
lean_object* v___x_620_; 
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 1, v___x_613_);
lean_ctor_set(v___x_608_, 0, v___x_611_);
v___x_620_ = v___x_608_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v___x_613_);
v___x_620_ = v_reuseFailAlloc_622_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
v_b_600_ = v___x_620_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg___boxed(lean_object* v_a_625_, lean_object* v_b_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v_a_625_, v_b_626_, v___y_627_);
lean_dec(v___y_627_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(lean_object* v_keys_630_, lean_object* v_vals_631_, lean_object* v_i_632_, lean_object* v_k_633_){
_start:
{
lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_634_ = lean_array_get_size(v_keys_630_);
v___x_635_ = lean_nat_dec_lt(v_i_632_, v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; 
lean_dec(v_i_632_);
v___x_636_ = lean_box(0);
return v___x_636_;
}
else
{
lean_object* v_k_x27_637_; uint8_t v___x_638_; 
v_k_x27_637_ = lean_array_fget_borrowed(v_keys_630_, v_i_632_);
v___x_638_ = lean_name_eq(v_k_633_, v_k_x27_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_unsigned_to_nat(1u);
v___x_640_ = lean_nat_add(v_i_632_, v___x_639_);
lean_dec(v_i_632_);
v_i_632_ = v___x_640_;
goto _start;
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_array_fget_borrowed(v_vals_631_, v_i_632_);
lean_dec(v_i_632_);
lean_inc(v___x_642_);
v___x_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_keys_644_, lean_object* v_vals_645_, lean_object* v_i_646_, lean_object* v_k_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_keys_644_, v_vals_645_, v_i_646_, v_k_647_);
lean_dec(v_k_647_);
lean_dec_ref(v_vals_645_);
lean_dec_ref(v_keys_644_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(lean_object* v_x_649_, size_t v_x_650_, lean_object* v_x_651_){
_start:
{
if (lean_obj_tag(v_x_649_) == 0)
{
lean_object* v_es_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_673_; 
v_es_652_ = lean_ctor_get(v_x_649_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v_x_649_);
if (v_isSharedCheck_673_ == 0)
{
v___x_654_ = v_x_649_;
v_isShared_655_ = v_isSharedCheck_673_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_es_652_);
lean_dec(v_x_649_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_673_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; size_t v___x_657_; size_t v___x_658_; size_t v___x_659_; lean_object* v_j_660_; lean_object* v___x_661_; 
v___x_656_ = lean_box(2);
v___x_657_ = ((size_t)5ULL);
v___x_658_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1);
v___x_659_ = lean_usize_land(v_x_650_, v___x_658_);
v_j_660_ = lean_usize_to_nat(v___x_659_);
v___x_661_ = lean_array_get(v___x_656_, v_es_652_, v_j_660_);
lean_dec(v_j_660_);
lean_dec_ref(v_es_652_);
switch(lean_obj_tag(v___x_661_))
{
case 0:
{
lean_object* v_key_662_; lean_object* v_val_663_; uint8_t v___x_664_; 
v_key_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_key_662_);
v_val_663_ = lean_ctor_get(v___x_661_, 1);
lean_inc(v_val_663_);
lean_dec_ref(v___x_661_);
v___x_664_ = lean_name_eq(v_x_651_, v_key_662_);
lean_dec(v_key_662_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; 
lean_dec(v_val_663_);
lean_del_object(v___x_654_);
v___x_665_ = lean_box(0);
return v___x_665_;
}
else
{
lean_object* v___x_667_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set_tag(v___x_654_, 1);
lean_ctor_set(v___x_654_, 0, v_val_663_);
v___x_667_ = v___x_654_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_val_663_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
case 1:
{
lean_object* v_node_669_; size_t v___x_670_; 
lean_del_object(v___x_654_);
v_node_669_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_node_669_);
lean_dec_ref(v___x_661_);
v___x_670_ = lean_usize_shift_right(v_x_650_, v___x_657_);
v_x_649_ = v_node_669_;
v_x_650_ = v___x_670_;
goto _start;
}
default: 
{
lean_object* v___x_672_; 
lean_del_object(v___x_654_);
v___x_672_ = lean_box(0);
return v___x_672_;
}
}
}
}
else
{
lean_object* v_ks_674_; lean_object* v_vs_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_ks_674_ = lean_ctor_get(v_x_649_, 0);
lean_inc_ref(v_ks_674_);
v_vs_675_ = lean_ctor_get(v_x_649_, 1);
lean_inc_ref(v_vs_675_);
lean_dec_ref(v_x_649_);
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_ks_674_, v_vs_675_, v___x_676_, v_x_651_);
lean_dec_ref(v_vs_675_);
lean_dec_ref(v_ks_674_);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg___boxed(lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
size_t v_x_37897__boxed_681_; lean_object* v_res_682_; 
v_x_37897__boxed_681_ = lean_unbox_usize(v_x_679_);
lean_dec(v_x_679_);
v_res_682_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_678_, v_x_37897__boxed_681_, v_x_680_);
lean_dec(v_x_680_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(lean_object* v_x_683_, lean_object* v_x_684_){
_start:
{
uint64_t v___y_686_; 
if (lean_obj_tag(v_x_684_) == 0)
{
uint64_t v___x_689_; 
v___x_689_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_686_ = v___x_689_;
goto v___jp_685_;
}
else
{
uint64_t v_hash_690_; 
v_hash_690_ = lean_ctor_get_uint64(v_x_684_, sizeof(void*)*2);
v___y_686_ = v_hash_690_;
goto v___jp_685_;
}
v___jp_685_:
{
size_t v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_uint64_to_usize(v___y_686_);
v___x_688_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_683_, v___x_687_, v_x_684_);
return v___x_688_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg___boxed(lean_object* v_x_691_, lean_object* v_x_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_x_691_, v_x_692_);
lean_dec(v_x_692_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(lean_object* v_name_697_, lean_object* v_type_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v_name_711_; lean_object* v___y_712_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v_name_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___x_866_; 
v___x_866_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_701_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_927_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_927_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_927_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_927_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
uint8_t v_clean_892_; 
v_clean_892_ = lean_ctor_get_uint8(v_a_867_, sizeof(void*)*11 + 16);
lean_dec(v_a_867_);
if (v_clean_892_ == 0)
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_Meta_Grind_getOriginalName_x3f(v_name_697_);
if (lean_obj_tag(v___x_893_) == 1)
{
lean_object* v_val_894_; lean_object* v___x_896_; 
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec_ref(v_type_698_);
lean_dec(v_name_697_);
v_val_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_val_894_);
lean_dec_ref(v___x_893_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v_val_894_);
v___x_896_ = v___x_869_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_val_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
else
{
uint8_t v___x_898_; 
lean_dec(v___x_893_);
v___x_898_ = l_Lean_Name_hasMacroScopes(v_name_697_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; 
lean_del_object(v___x_869_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec_ref(v_type_698_);
v___x_899_ = l_Lean_Core_mkFreshUserName(v_name_697_, v_a_707_, v_a_708_);
return v___x_899_;
}
else
{
lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
lean_inc(v_name_697_);
v___x_900_ = lean_erase_macro_scopes(v_name_697_);
v___x_901_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
v___x_902_ = lean_name_eq(v___x_900_, v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_903_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1));
v___x_904_ = lean_name_eq(v___x_900_, v___x_903_);
lean_dec(v___x_900_);
if (v___x_904_ == 0)
{
lean_object* v___x_906_; 
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec_ref(v_type_698_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v_name_697_);
v___x_906_ = v___x_869_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_name_697_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
else
{
lean_del_object(v___x_869_);
goto v___jp_871_;
}
}
else
{
lean_dec(v___x_900_);
lean_del_object(v___x_869_);
goto v___jp_871_;
}
}
}
}
else
{
uint8_t v___x_908_; 
lean_del_object(v___x_869_);
v___x_908_ = l_Lean_Name_hasMacroScopes(v_name_697_);
if (v___x_908_ == 0)
{
v_name_841_ = v_name_697_;
v___y_842_ = v_a_699_;
v___y_843_ = v_a_700_;
v___y_844_ = v_a_701_;
v___y_845_ = v_a_702_;
v___y_846_ = v_a_703_;
v___y_847_ = v_a_704_;
v___y_848_ = v_a_705_;
v___y_849_ = v_a_706_;
v___y_850_ = v_a_707_;
v___y_851_ = v_a_708_;
goto v___jp_840_;
}
else
{
lean_object* v___x_909_; lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_909_ = lean_erase_macro_scopes(v_name_697_);
v___x_923_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
v___x_924_ = lean_name_eq(v___x_909_, v___x_923_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_925_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1));
v___x_926_ = lean_name_eq(v___x_909_, v___x_925_);
if (v___x_926_ == 0)
{
v_name_841_ = v___x_909_;
v___y_842_ = v_a_699_;
v___y_843_ = v_a_700_;
v___y_844_ = v_a_701_;
v___y_845_ = v_a_702_;
v___y_846_ = v_a_703_;
v___y_847_ = v_a_704_;
v___y_848_ = v_a_705_;
v___y_849_ = v_a_706_;
v___y_850_ = v_a_707_;
v___y_851_ = v_a_708_;
goto v___jp_840_;
}
else
{
goto v___jp_910_;
}
}
else
{
goto v___jp_910_;
}
v___jp_910_:
{
lean_object* v___x_911_; 
lean_inc(v_a_708_);
lean_inc_ref(v_a_707_);
lean_inc(v_a_706_);
lean_inc_ref(v_a_705_);
lean_inc_ref(v_type_698_);
v___x_911_ = l_Lean_Meta_isProp(v_type_698_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; uint8_t v___x_913_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref(v___x_911_);
v___x_913_ = lean_unbox(v_a_912_);
lean_dec(v_a_912_);
if (v___x_913_ == 0)
{
v_name_841_ = v___x_909_;
v___y_842_ = v_a_699_;
v___y_843_ = v_a_700_;
v___y_844_ = v_a_701_;
v___y_845_ = v_a_702_;
v___y_846_ = v_a_703_;
v___y_847_ = v_a_704_;
v___y_848_ = v_a_705_;
v___y_849_ = v_a_706_;
v___y_850_ = v_a_707_;
v___y_851_ = v_a_708_;
goto v___jp_840_;
}
else
{
lean_object* v___x_914_; 
lean_dec(v___x_909_);
v___x_914_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v_name_841_ = v___x_914_;
v___y_842_ = v_a_699_;
v___y_843_ = v_a_700_;
v___y_844_ = v_a_701_;
v___y_845_ = v_a_702_;
v___y_846_ = v_a_703_;
v___y_847_ = v_a_704_;
v___y_848_ = v_a_705_;
v___y_849_ = v_a_706_;
v___y_850_ = v_a_707_;
v___y_851_ = v_a_708_;
goto v___jp_840_;
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec(v___x_909_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec_ref(v_type_698_);
v_a_915_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_911_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_911_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
}
v___jp_871_:
{
lean_object* v___x_872_; 
lean_inc(v_a_708_);
lean_inc_ref(v_a_707_);
v___x_872_ = l_Lean_Meta_isProp(v_type_698_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_883_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_883_ == 0)
{
v___x_875_ = v___x_872_;
v_isShared_876_ = v_isSharedCheck_883_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_883_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
uint8_t v___x_877_; 
v___x_877_ = lean_unbox(v_a_873_);
lean_dec(v_a_873_);
if (v___x_877_ == 0)
{
lean_object* v___x_879_; 
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v_name_697_);
v___x_879_ = v___x_875_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_name_697_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
else
{
lean_object* v___x_881_; lean_object* v___x_882_; 
lean_del_object(v___x_875_);
lean_dec(v_name_697_);
v___x_881_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v___x_882_ = l_Lean_Core_mkFreshUserName(v___x_881_, v_a_707_, v_a_708_);
return v___x_882_;
}
}
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_name_697_);
v_a_884_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_872_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_872_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec_ref(v_type_698_);
lean_dec(v_name_697_);
v_a_928_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_866_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_866_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
v___jp_710_:
{
lean_object* v___x_713_; lean_object* v_toGoalState_714_; lean_object* v_clean_715_; lean_object* v_mvarId_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_762_; 
v___x_713_ = lean_st_ref_take(v___y_712_);
v_toGoalState_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc_ref(v_toGoalState_714_);
v_clean_715_ = lean_ctor_get(v_toGoalState_714_, 16);
lean_inc_ref(v_clean_715_);
v_mvarId_716_ = lean_ctor_get(v___x_713_, 1);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; 
v_unused_763_ = lean_ctor_get(v___x_713_, 0);
lean_dec(v_unused_763_);
v___x_718_ = v___x_713_;
v_isShared_719_ = v_isSharedCheck_762_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_mvarId_716_);
lean_dec(v___x_713_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_762_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v_nextDeclIdx_720_; lean_object* v_canon_721_; lean_object* v_enodeMap_722_; lean_object* v_exprs_723_; lean_object* v_parents_724_; lean_object* v_congrTable_725_; lean_object* v_appMap_726_; lean_object* v_indicesFound_727_; lean_object* v_newFacts_728_; uint8_t v_inconsistent_729_; lean_object* v_nextIdx_730_; lean_object* v_newRawFacts_731_; lean_object* v_facts_732_; lean_object* v_extThms_733_; lean_object* v_ematch_734_; lean_object* v_inj_735_; lean_object* v_split_736_; lean_object* v_sstates_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_760_; 
v_nextDeclIdx_720_ = lean_ctor_get(v_toGoalState_714_, 0);
v_canon_721_ = lean_ctor_get(v_toGoalState_714_, 1);
v_enodeMap_722_ = lean_ctor_get(v_toGoalState_714_, 2);
v_exprs_723_ = lean_ctor_get(v_toGoalState_714_, 3);
v_parents_724_ = lean_ctor_get(v_toGoalState_714_, 4);
v_congrTable_725_ = lean_ctor_get(v_toGoalState_714_, 5);
v_appMap_726_ = lean_ctor_get(v_toGoalState_714_, 6);
v_indicesFound_727_ = lean_ctor_get(v_toGoalState_714_, 7);
v_newFacts_728_ = lean_ctor_get(v_toGoalState_714_, 8);
v_inconsistent_729_ = lean_ctor_get_uint8(v_toGoalState_714_, sizeof(void*)*18);
v_nextIdx_730_ = lean_ctor_get(v_toGoalState_714_, 9);
v_newRawFacts_731_ = lean_ctor_get(v_toGoalState_714_, 10);
v_facts_732_ = lean_ctor_get(v_toGoalState_714_, 11);
v_extThms_733_ = lean_ctor_get(v_toGoalState_714_, 12);
v_ematch_734_ = lean_ctor_get(v_toGoalState_714_, 13);
v_inj_735_ = lean_ctor_get(v_toGoalState_714_, 14);
v_split_736_ = lean_ctor_get(v_toGoalState_714_, 15);
v_sstates_737_ = lean_ctor_get(v_toGoalState_714_, 17);
v_isSharedCheck_760_ = !lean_is_exclusive(v_toGoalState_714_);
if (v_isSharedCheck_760_ == 0)
{
lean_object* v_unused_761_; 
v_unused_761_ = lean_ctor_get(v_toGoalState_714_, 16);
lean_dec(v_unused_761_);
v___x_739_ = v_toGoalState_714_;
v_isShared_740_ = v_isSharedCheck_760_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_sstates_737_);
lean_inc(v_split_736_);
lean_inc(v_inj_735_);
lean_inc(v_ematch_734_);
lean_inc(v_extThms_733_);
lean_inc(v_facts_732_);
lean_inc(v_newRawFacts_731_);
lean_inc(v_nextIdx_730_);
lean_inc(v_newFacts_728_);
lean_inc(v_indicesFound_727_);
lean_inc(v_appMap_726_);
lean_inc(v_congrTable_725_);
lean_inc(v_parents_724_);
lean_inc(v_exprs_723_);
lean_inc(v_enodeMap_722_);
lean_inc(v_canon_721_);
lean_inc(v_nextDeclIdx_720_);
lean_dec(v_toGoalState_714_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_760_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v_used_741_; lean_object* v_next_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_759_; 
v_used_741_ = lean_ctor_get(v_clean_715_, 0);
v_next_742_ = lean_ctor_get(v_clean_715_, 1);
v_isSharedCheck_759_ = !lean_is_exclusive(v_clean_715_);
if (v_isSharedCheck_759_ == 0)
{
v___x_744_ = v_clean_715_;
v_isShared_745_ = v_isSharedCheck_759_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_next_742_);
lean_inc(v_used_741_);
lean_dec(v_clean_715_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_759_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_746_ = lean_box(0);
lean_inc(v_name_711_);
v___x_747_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_used_741_, v_name_711_, v___x_746_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_747_);
v___x_749_ = v___x_744_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_next_742_);
v___x_749_ = v_reuseFailAlloc_758_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_751_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 16, v___x_749_);
v___x_751_ = v___x_739_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_nextDeclIdx_720_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_canon_721_);
lean_ctor_set(v_reuseFailAlloc_757_, 2, v_enodeMap_722_);
lean_ctor_set(v_reuseFailAlloc_757_, 3, v_exprs_723_);
lean_ctor_set(v_reuseFailAlloc_757_, 4, v_parents_724_);
lean_ctor_set(v_reuseFailAlloc_757_, 5, v_congrTable_725_);
lean_ctor_set(v_reuseFailAlloc_757_, 6, v_appMap_726_);
lean_ctor_set(v_reuseFailAlloc_757_, 7, v_indicesFound_727_);
lean_ctor_set(v_reuseFailAlloc_757_, 8, v_newFacts_728_);
lean_ctor_set(v_reuseFailAlloc_757_, 9, v_nextIdx_730_);
lean_ctor_set(v_reuseFailAlloc_757_, 10, v_newRawFacts_731_);
lean_ctor_set(v_reuseFailAlloc_757_, 11, v_facts_732_);
lean_ctor_set(v_reuseFailAlloc_757_, 12, v_extThms_733_);
lean_ctor_set(v_reuseFailAlloc_757_, 13, v_ematch_734_);
lean_ctor_set(v_reuseFailAlloc_757_, 14, v_inj_735_);
lean_ctor_set(v_reuseFailAlloc_757_, 15, v_split_736_);
lean_ctor_set(v_reuseFailAlloc_757_, 16, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_757_, 17, v_sstates_737_);
lean_ctor_set_uint8(v_reuseFailAlloc_757_, sizeof(void*)*18, v_inconsistent_729_);
v___x_751_ = v_reuseFailAlloc_757_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_753_; 
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_751_);
v___x_753_ = v___x_718_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_mvarId_716_);
v___x_753_ = v_reuseFailAlloc_756_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_st_ref_set(v___y_712_, v___x_753_);
v___x_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_755_, 0, v_name_711_);
return v___x_755_;
}
}
}
}
}
}
}
v___jp_764_:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_768_);
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v___y_774_);
lean_ctor_set(v___x_778_, 1, v___y_777_);
lean_inc(v___y_775_);
v___x_779_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v___y_775_, v___x_778_, v___y_767_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_781_; lean_object* v_toGoalState_782_; lean_object* v_clean_783_; lean_object* v_fst_784_; lean_object* v_snd_785_; lean_object* v_mvarId_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_830_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_780_);
lean_dec_ref(v___x_779_);
v___x_781_ = lean_st_ref_take(v___y_767_);
v_toGoalState_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc_ref(v_toGoalState_782_);
v_clean_783_ = lean_ctor_get(v_toGoalState_782_, 16);
lean_inc_ref(v_clean_783_);
v_fst_784_ = lean_ctor_get(v_a_780_, 0);
lean_inc(v_fst_784_);
v_snd_785_ = lean_ctor_get(v_a_780_, 1);
lean_inc(v_snd_785_);
lean_dec(v_a_780_);
v_mvarId_786_ = lean_ctor_get(v___x_781_, 1);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_830_ == 0)
{
lean_object* v_unused_831_; 
v_unused_831_ = lean_ctor_get(v___x_781_, 0);
lean_dec(v_unused_831_);
v___x_788_ = v___x_781_;
v_isShared_789_ = v_isSharedCheck_830_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_mvarId_786_);
lean_dec(v___x_781_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_830_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v_nextDeclIdx_790_; lean_object* v_canon_791_; lean_object* v_enodeMap_792_; lean_object* v_exprs_793_; lean_object* v_parents_794_; lean_object* v_congrTable_795_; lean_object* v_appMap_796_; lean_object* v_indicesFound_797_; lean_object* v_newFacts_798_; uint8_t v_inconsistent_799_; lean_object* v_nextIdx_800_; lean_object* v_newRawFacts_801_; lean_object* v_facts_802_; lean_object* v_extThms_803_; lean_object* v_ematch_804_; lean_object* v_inj_805_; lean_object* v_split_806_; lean_object* v_sstates_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_828_; 
v_nextDeclIdx_790_ = lean_ctor_get(v_toGoalState_782_, 0);
v_canon_791_ = lean_ctor_get(v_toGoalState_782_, 1);
v_enodeMap_792_ = lean_ctor_get(v_toGoalState_782_, 2);
v_exprs_793_ = lean_ctor_get(v_toGoalState_782_, 3);
v_parents_794_ = lean_ctor_get(v_toGoalState_782_, 4);
v_congrTable_795_ = lean_ctor_get(v_toGoalState_782_, 5);
v_appMap_796_ = lean_ctor_get(v_toGoalState_782_, 6);
v_indicesFound_797_ = lean_ctor_get(v_toGoalState_782_, 7);
v_newFacts_798_ = lean_ctor_get(v_toGoalState_782_, 8);
v_inconsistent_799_ = lean_ctor_get_uint8(v_toGoalState_782_, sizeof(void*)*18);
v_nextIdx_800_ = lean_ctor_get(v_toGoalState_782_, 9);
v_newRawFacts_801_ = lean_ctor_get(v_toGoalState_782_, 10);
v_facts_802_ = lean_ctor_get(v_toGoalState_782_, 11);
v_extThms_803_ = lean_ctor_get(v_toGoalState_782_, 12);
v_ematch_804_ = lean_ctor_get(v_toGoalState_782_, 13);
v_inj_805_ = lean_ctor_get(v_toGoalState_782_, 14);
v_split_806_ = lean_ctor_get(v_toGoalState_782_, 15);
v_sstates_807_ = lean_ctor_get(v_toGoalState_782_, 17);
v_isSharedCheck_828_ = !lean_is_exclusive(v_toGoalState_782_);
if (v_isSharedCheck_828_ == 0)
{
lean_object* v_unused_829_; 
v_unused_829_ = lean_ctor_get(v_toGoalState_782_, 16);
lean_dec(v_unused_829_);
v___x_809_ = v_toGoalState_782_;
v_isShared_810_ = v_isSharedCheck_828_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_sstates_807_);
lean_inc(v_split_806_);
lean_inc(v_inj_805_);
lean_inc(v_ematch_804_);
lean_inc(v_extThms_803_);
lean_inc(v_facts_802_);
lean_inc(v_newRawFacts_801_);
lean_inc(v_nextIdx_800_);
lean_inc(v_newFacts_798_);
lean_inc(v_indicesFound_797_);
lean_inc(v_appMap_796_);
lean_inc(v_congrTable_795_);
lean_inc(v_parents_794_);
lean_inc(v_exprs_793_);
lean_inc(v_enodeMap_792_);
lean_inc(v_canon_791_);
lean_inc(v_nextDeclIdx_790_);
lean_dec(v_toGoalState_782_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_828_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v_used_811_; lean_object* v_next_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_827_; 
v_used_811_ = lean_ctor_get(v_clean_783_, 0);
v_next_812_ = lean_ctor_get(v_clean_783_, 1);
v_isSharedCheck_827_ = !lean_is_exclusive(v_clean_783_);
if (v_isSharedCheck_827_ == 0)
{
v___x_814_ = v_clean_783_;
v_isShared_815_ = v_isSharedCheck_827_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_next_812_);
lean_inc(v_used_811_);
lean_dec(v_clean_783_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_827_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_816_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_next_812_, v___y_775_, v_snd_785_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 1, v___x_816_);
v___x_818_ = v___x_814_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_used_811_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v___x_816_);
v___x_818_ = v_reuseFailAlloc_826_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_820_; 
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 16, v___x_818_);
v___x_820_ = v___x_809_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_nextDeclIdx_790_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_canon_791_);
lean_ctor_set(v_reuseFailAlloc_825_, 2, v_enodeMap_792_);
lean_ctor_set(v_reuseFailAlloc_825_, 3, v_exprs_793_);
lean_ctor_set(v_reuseFailAlloc_825_, 4, v_parents_794_);
lean_ctor_set(v_reuseFailAlloc_825_, 5, v_congrTable_795_);
lean_ctor_set(v_reuseFailAlloc_825_, 6, v_appMap_796_);
lean_ctor_set(v_reuseFailAlloc_825_, 7, v_indicesFound_797_);
lean_ctor_set(v_reuseFailAlloc_825_, 8, v_newFacts_798_);
lean_ctor_set(v_reuseFailAlloc_825_, 9, v_nextIdx_800_);
lean_ctor_set(v_reuseFailAlloc_825_, 10, v_newRawFacts_801_);
lean_ctor_set(v_reuseFailAlloc_825_, 11, v_facts_802_);
lean_ctor_set(v_reuseFailAlloc_825_, 12, v_extThms_803_);
lean_ctor_set(v_reuseFailAlloc_825_, 13, v_ematch_804_);
lean_ctor_set(v_reuseFailAlloc_825_, 14, v_inj_805_);
lean_ctor_set(v_reuseFailAlloc_825_, 15, v_split_806_);
lean_ctor_set(v_reuseFailAlloc_825_, 16, v___x_818_);
lean_ctor_set(v_reuseFailAlloc_825_, 17, v_sstates_807_);
lean_ctor_set_uint8(v_reuseFailAlloc_825_, sizeof(void*)*18, v_inconsistent_799_);
v___x_820_ = v_reuseFailAlloc_825_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_object* v___x_822_; 
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_820_);
v___x_822_ = v___x_788_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_820_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_mvarId_786_);
v___x_822_ = v_reuseFailAlloc_824_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_823_; 
v___x_823_ = lean_st_ref_set(v___y_767_, v___x_822_);
v_name_711_ = v_fst_784_;
v___y_712_ = v___y_767_;
goto v___jp_710_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec(v___y_775_);
v_a_832_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_779_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_779_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
v___jp_840_:
{
lean_object* v___x_852_; lean_object* v_toGoalState_853_; lean_object* v_clean_854_; lean_object* v_used_855_; uint8_t v___x_856_; 
v___x_852_ = lean_st_ref_get(v___y_842_);
v_toGoalState_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc_ref(v_toGoalState_853_);
lean_dec(v___x_852_);
v_clean_854_ = lean_ctor_get(v_toGoalState_853_, 16);
lean_inc_ref(v_clean_854_);
lean_dec_ref(v_toGoalState_853_);
v_used_855_ = lean_ctor_get(v_clean_854_, 0);
lean_inc_ref(v_used_855_);
lean_dec_ref(v_clean_854_);
v___x_856_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_used_855_, v_name_841_);
if (v___x_856_ == 0)
{
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec_ref(v_type_698_);
v_name_711_ = v_name_841_;
v___y_712_ = v___y_842_;
goto v___jp_710_;
}
else
{
lean_object* v___x_857_; 
lean_inc(v___y_851_);
lean_inc_ref(v___y_850_);
lean_inc(v___y_849_);
lean_inc_ref(v___y_848_);
lean_inc(v_name_841_);
v___x_857_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(v_name_841_, v_type_698_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_859_; lean_object* v_toGoalState_860_; lean_object* v_clean_861_; lean_object* v_next_862_; lean_object* v___x_863_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref(v___x_857_);
v___x_859_ = lean_st_ref_get(v___y_842_);
v_toGoalState_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc_ref(v_toGoalState_860_);
lean_dec(v___x_859_);
v_clean_861_ = lean_ctor_get(v_toGoalState_860_, 16);
lean_inc_ref(v_clean_861_);
lean_dec_ref(v_toGoalState_860_);
v_next_862_ = lean_ctor_get(v_clean_861_, 1);
lean_inc_ref(v_next_862_);
lean_dec_ref(v_clean_861_);
v___x_863_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_next_862_, v_a_858_);
if (lean_obj_tag(v___x_863_) == 1)
{
lean_object* v_val_864_; 
v_val_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_val_864_);
lean_dec_ref(v___x_863_);
v___y_765_ = v___y_844_;
v___y_766_ = v___y_847_;
v___y_767_ = v___y_842_;
v___y_768_ = v___y_849_;
v___y_769_ = v___y_845_;
v___y_770_ = v___y_846_;
v___y_771_ = v___y_848_;
v___y_772_ = v___y_851_;
v___y_773_ = v___y_850_;
v___y_774_ = v_name_841_;
v___y_775_ = v_a_858_;
v___y_776_ = v___y_843_;
v___y_777_ = v_val_864_;
goto v___jp_764_;
}
else
{
lean_object* v___x_865_; 
lean_dec(v___x_863_);
v___x_865_ = lean_unsigned_to_nat(1u);
v___y_765_ = v___y_844_;
v___y_766_ = v___y_847_;
v___y_767_ = v___y_842_;
v___y_768_ = v___y_849_;
v___y_769_ = v___y_845_;
v___y_770_ = v___y_846_;
v___y_771_ = v___y_848_;
v___y_772_ = v___y_851_;
v___y_773_ = v___y_850_;
v___y_774_ = v_name_841_;
v___y_775_ = v_a_858_;
v___y_776_ = v___y_843_;
v___y_777_ = v___x_865_;
goto v___jp_764_;
}
}
else
{
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v_name_841_);
return v___x_857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___boxed(lean_object* v_name_936_, lean_object* v_type_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v_name_936_, v_type_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec(v_a_938_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0(lean_object* v_00_u03b2_950_, lean_object* v_x_951_, lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_x_951_, v_x_952_, v_x_953_);
return v___x_954_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(lean_object* v_00_u03b2_955_, lean_object* v_x_956_, lean_object* v_x_957_){
_start:
{
uint8_t v___x_958_; 
v___x_958_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_x_956_, v_x_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___boxed(lean_object* v_00_u03b2_959_, lean_object* v_x_960_, lean_object* v_x_961_){
_start:
{
uint8_t v_res_962_; lean_object* v_r_963_; 
v_res_962_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(v_00_u03b2_959_, v_x_960_, v_x_961_);
lean_dec(v_x_961_);
v_r_963_ = lean_box(v_res_962_);
return v_r_963_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(lean_object* v_a_964_, lean_object* v_b_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v_a_964_, v_b_965_, v___y_966_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___boxed(lean_object* v_a_978_, lean_object* v_b_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(v_a_978_, v_b_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec(v___y_980_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(lean_object* v_00_u03b2_992_, lean_object* v_x_993_, lean_object* v_x_994_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_x_993_, v_x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___boxed(lean_object* v_00_u03b2_996_, lean_object* v_x_997_, lean_object* v_x_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(v_00_u03b2_996_, v_x_997_, v_x_998_);
lean_dec(v_x_998_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(lean_object* v_00_u03b2_1000_, lean_object* v_x_1001_, size_t v_x_1002_, size_t v_x_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_1001_, v_x_1002_, v_x_1003_, v_x_1004_, v_x_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_, lean_object* v_x_1012_){
_start:
{
size_t v_x_38435__boxed_1013_; size_t v_x_38436__boxed_1014_; lean_object* v_res_1015_; 
v_x_38435__boxed_1013_ = lean_unbox_usize(v_x_1009_);
lean_dec(v_x_1009_);
v_x_38436__boxed_1014_ = lean_unbox_usize(v_x_1010_);
lean_dec(v_x_1010_);
v_res_1015_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(v_00_u03b2_1007_, v_x_1008_, v_x_38435__boxed_1013_, v_x_38436__boxed_1014_, v_x_1011_, v_x_1012_);
return v_res_1015_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(lean_object* v_00_u03b2_1016_, lean_object* v_x_1017_, size_t v_x_1018_, lean_object* v_x_1019_){
_start:
{
uint8_t v___x_1020_; 
v___x_1020_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_1017_, v_x_1018_, v_x_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1021_, lean_object* v_x_1022_, lean_object* v_x_1023_, lean_object* v_x_1024_){
_start:
{
size_t v_x_38452__boxed_1025_; uint8_t v_res_1026_; lean_object* v_r_1027_; 
v_x_38452__boxed_1025_ = lean_unbox_usize(v_x_1023_);
lean_dec(v_x_1023_);
v_res_1026_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(v_00_u03b2_1021_, v_x_1022_, v_x_38452__boxed_1025_, v_x_1024_);
lean_dec(v_x_1024_);
v_r_1027_ = lean_box(v_res_1026_);
return v_r_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(lean_object* v_00_u03b2_1028_, lean_object* v_x_1029_, size_t v_x_1030_, lean_object* v_x_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_1029_, v_x_1030_, v_x_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1033_, lean_object* v_x_1034_, lean_object* v_x_1035_, lean_object* v_x_1036_){
_start:
{
size_t v_x_38463__boxed_1037_; lean_object* v_res_1038_; 
v_x_38463__boxed_1037_ = lean_unbox_usize(v_x_1035_);
lean_dec(v_x_1035_);
v_res_1038_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(v_00_u03b2_1033_, v_x_1034_, v_x_38463__boxed_1037_, v_x_1036_);
lean_dec(v_x_1036_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1039_, lean_object* v_n_1040_, lean_object* v_k_1041_, lean_object* v_v_1042_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(v_n_1040_, v_k_1041_, v_v_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1044_, size_t v_depth_1045_, lean_object* v_keys_1046_, lean_object* v_vals_1047_, lean_object* v_heq_1048_, lean_object* v_i_1049_, lean_object* v_entries_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_depth_1045_, v_keys_1046_, v_vals_1047_, v_i_1049_, v_entries_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1052_, lean_object* v_depth_1053_, lean_object* v_keys_1054_, lean_object* v_vals_1055_, lean_object* v_heq_1056_, lean_object* v_i_1057_, lean_object* v_entries_1058_){
_start:
{
size_t v_depth_boxed_1059_; lean_object* v_res_1060_; 
v_depth_boxed_1059_ = lean_unbox_usize(v_depth_1053_);
lean_dec(v_depth_1053_);
v_res_1060_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(v_00_u03b2_1052_, v_depth_boxed_1059_, v_keys_1054_, v_vals_1055_, v_heq_1056_, v_i_1057_, v_entries_1058_);
lean_dec_ref(v_vals_1055_);
lean_dec_ref(v_keys_1054_);
return v_res_1060_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1061_, lean_object* v_keys_1062_, lean_object* v_vals_1063_, lean_object* v_heq_1064_, lean_object* v_i_1065_, lean_object* v_k_1066_){
_start:
{
uint8_t v___x_1067_; 
v___x_1067_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_keys_1062_, v_i_1065_, v_k_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1068_, lean_object* v_keys_1069_, lean_object* v_vals_1070_, lean_object* v_heq_1071_, lean_object* v_i_1072_, lean_object* v_k_1073_){
_start:
{
uint8_t v_res_1074_; lean_object* v_r_1075_; 
v_res_1074_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(v_00_u03b2_1068_, v_keys_1069_, v_vals_1070_, v_heq_1071_, v_i_1072_, v_k_1073_);
lean_dec(v_k_1073_);
lean_dec_ref(v_vals_1070_);
lean_dec_ref(v_keys_1069_);
v_r_1075_ = lean_box(v_res_1074_);
return v_r_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_1076_, lean_object* v_keys_1077_, lean_object* v_vals_1078_, lean_object* v_heq_1079_, lean_object* v_i_1080_, lean_object* v_k_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_keys_1077_, v_vals_1078_, v_i_1080_, v_k_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1083_, lean_object* v_keys_1084_, lean_object* v_vals_1085_, lean_object* v_heq_1086_, lean_object* v_i_1087_, lean_object* v_k_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(v_00_u03b2_1083_, v_keys_1084_, v_vals_1085_, v_heq_1086_, v_i_1087_, v_k_1088_);
lean_dec(v_k_1088_);
lean_dec_ref(v_vals_1085_);
lean_dec_ref(v_keys_1084_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_, lean_object* v_x_1093_, lean_object* v_x_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1091_, v_x_1092_, v_x_1093_, v_x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(lean_object* v_msgData_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v___x_1102_; lean_object* v_env_1103_; lean_object* v___x_1104_; lean_object* v_mctx_1105_; lean_object* v_lctx_1106_; lean_object* v_options_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1102_ = lean_st_ref_get(v___y_1100_);
v_env_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc_ref(v_env_1103_);
lean_dec(v___x_1102_);
v___x_1104_ = lean_st_ref_get(v___y_1098_);
v_mctx_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc_ref(v_mctx_1105_);
lean_dec(v___x_1104_);
v_lctx_1106_ = lean_ctor_get(v___y_1097_, 2);
v_options_1107_ = lean_ctor_get(v___y_1099_, 2);
lean_inc_ref(v_options_1107_);
lean_inc_ref(v_lctx_1106_);
v___x_1108_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1108_, 0, v_env_1103_);
lean_ctor_set(v___x_1108_, 1, v_mctx_1105_);
lean_ctor_set(v___x_1108_, 2, v_lctx_1106_);
lean_ctor_set(v___x_1108_, 3, v_options_1107_);
v___x_1109_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
lean_ctor_set(v___x_1109_, 1, v_msgData_1096_);
v___x_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0___boxed(lean_object* v_msgData_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(v_msgData_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(lean_object* v_msg_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_ref_1124_; lean_object* v___x_1125_; lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1134_; 
v_ref_1124_ = lean_ctor_get(v___y_1121_, 5);
v___x_1125_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(v_msg_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1128_ = v___x_1125_;
v_isShared_1129_ = v_isSharedCheck_1134_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1125_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1134_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
lean_inc(v_ref_1124_);
v___x_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1130_, 0, v_ref_1124_);
lean_ctor_set(v___x_1130_, 1, v_a_1126_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set_tag(v___x_1128_, 1);
lean_ctor_set(v___x_1128_, 0, v___x_1130_);
v___x_1132_ = v___x_1128_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg___boxed(lean_object* v_msg_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v_msg_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
return v_res_1141_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__0));
v___x_1144_ = l_Lean_stringToMessageData(v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v_fst_1157_; lean_object* v_snd_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___x_1211_; lean_object* v_mvarId_1212_; lean_object* v___x_1213_; 
v___x_1211_ = lean_st_ref_get(v_a_1145_);
v_mvarId_1212_ = lean_ctor_get(v___x_1211_, 1);
lean_inc(v_mvarId_1212_);
lean_dec(v___x_1211_);
v___x_1213_ = l_Lean_MVarId_getType(v_mvarId_1212_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1214_);
lean_dec_ref(v___x_1213_);
switch(lean_obj_tag(v_a_1214_))
{
case 7:
{
lean_object* v_binderName_1215_; lean_object* v_binderType_1216_; 
v_binderName_1215_ = lean_ctor_get(v_a_1214_, 0);
lean_inc(v_binderName_1215_);
v_binderType_1216_ = lean_ctor_get(v_a_1214_, 1);
lean_inc_ref(v_binderType_1216_);
lean_dec_ref(v_a_1214_);
v_fst_1157_ = v_binderName_1215_;
v_snd_1158_ = v_binderType_1216_;
v___y_1159_ = v_a_1145_;
v___y_1160_ = v_a_1146_;
v___y_1161_ = v_a_1147_;
v___y_1162_ = v_a_1148_;
v___y_1163_ = v_a_1149_;
v___y_1164_ = v_a_1150_;
v___y_1165_ = v_a_1151_;
v___y_1166_ = v_a_1152_;
v___y_1167_ = v_a_1153_;
v___y_1168_ = v_a_1154_;
goto v___jp_1156_;
}
case 8:
{
lean_object* v_declName_1217_; lean_object* v_type_1218_; 
v_declName_1217_ = lean_ctor_get(v_a_1214_, 0);
lean_inc(v_declName_1217_);
v_type_1218_ = lean_ctor_get(v_a_1214_, 1);
lean_inc_ref(v_type_1218_);
lean_dec_ref(v_a_1214_);
v_fst_1157_ = v_declName_1217_;
v_snd_1158_ = v_type_1218_;
v___y_1159_ = v_a_1145_;
v___y_1160_ = v_a_1146_;
v___y_1161_ = v_a_1147_;
v___y_1162_ = v_a_1148_;
v___y_1163_ = v_a_1149_;
v___y_1164_ = v_a_1150_;
v___y_1165_ = v_a_1151_;
v___y_1166_ = v_a_1152_;
v___y_1167_ = v_a_1153_;
v___y_1168_ = v_a_1154_;
goto v___jp_1156_;
}
default: 
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec(v_a_1214_);
v___x_1219_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1);
v___x_1220_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v___x_1219_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1220_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
v_a_1229_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1213_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1213_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
v___jp_1156_:
{
lean_object* v___x_1169_; 
lean_inc(v___y_1168_);
lean_inc_ref(v___y_1167_);
lean_inc(v___y_1166_);
lean_inc_ref(v___y_1165_);
v___x_1169_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v_fst_1157_, v_snd_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v___x_1171_; lean_object* v_mvarId_1172_; lean_object* v___x_1173_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref(v___x_1169_);
v___x_1171_ = lean_st_ref_get(v___y_1159_);
v_mvarId_1172_ = lean_ctor_get(v___x_1171_, 1);
lean_inc(v_mvarId_1172_);
lean_dec(v___x_1171_);
v___x_1173_ = l_Lean_MVarId_intro(v_mvarId_1172_, v_a_1170_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1194_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1176_ = v___x_1173_;
v_isShared_1177_ = v_isSharedCheck_1194_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1173_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1194_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v_fst_1178_; lean_object* v_snd_1179_; lean_object* v___x_1180_; lean_object* v_toGoalState_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1192_; 
v_fst_1178_ = lean_ctor_get(v_a_1174_, 0);
lean_inc(v_fst_1178_);
v_snd_1179_ = lean_ctor_get(v_a_1174_, 1);
lean_inc(v_snd_1179_);
lean_dec(v_a_1174_);
v___x_1180_ = lean_st_ref_take(v___y_1159_);
v_toGoalState_1181_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1192_ == 0)
{
lean_object* v_unused_1193_; 
v_unused_1193_ = lean_ctor_get(v___x_1180_, 1);
lean_dec(v_unused_1193_);
v___x_1183_ = v___x_1180_;
v_isShared_1184_ = v_isSharedCheck_1192_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_toGoalState_1181_);
lean_dec(v___x_1180_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1192_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 1, v_snd_1179_);
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_toGoalState_1181_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_snd_1179_);
v___x_1186_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1187_ = lean_st_ref_set(v___y_1159_, v___x_1186_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 0, v_fst_1178_);
v___x_1189_ = v___x_1176_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_fst_1178_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
v_a_1195_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1173_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1173_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
v_a_1203_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1169_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1169_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___boxed(lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
lean_dec(v_a_1238_);
lean_dec(v_a_1237_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0(lean_object* v_00_u03b1_1249_, lean_object* v_msg_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v_msg_1250_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___boxed(lean_object* v_00_u03b1_1263_, lean_object* v_msg_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0(v_00_u03b1_1263_, v_msg_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec(v___y_1265_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(lean_object* v_x_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = lean_apply_11(v_x_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, lean_box(0));
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0___boxed(lean_object* v_x_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(v_x_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(lean_object* v_mvarId_1303_, lean_object* v_x_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v___f_1316_; lean_object* v___x_1317_; 
v___f_1316_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_1316_, 0, v_x_1304_);
lean_closure_set(v___f_1316_, 1, v___y_1305_);
lean_closure_set(v___f_1316_, 2, v___y_1306_);
lean_closure_set(v___f_1316_, 3, v___y_1307_);
lean_closure_set(v___f_1316_, 4, v___y_1308_);
lean_closure_set(v___f_1316_, 5, v___y_1309_);
lean_closure_set(v___f_1316_, 6, v___y_1310_);
v___x_1317_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1303_, v___f_1316_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
if (lean_obj_tag(v___x_1317_) == 0)
{
return v___x_1317_;
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1317_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1317_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___boxed(lean_object* v_mvarId_1326_, lean_object* v_x_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_1326_, v_x_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(lean_object* v_00_u03b1_1340_, lean_object* v_mvarId_1341_, lean_object* v_x_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_1341_, v_x_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___boxed(lean_object* v_00_u03b1_1355_, lean_object* v_mvarId_1356_, lean_object* v_x_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(v_00_u03b1_1355_, v_mvarId_1356_, v_x_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0(lean_object* v_x_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = lean_apply_10(v_x_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, lean_box(0));
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0___boxed(lean_object* v_x_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0(v_x_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(lean_object* v_mvarId_1394_, lean_object* v_x_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___f_1406_; lean_object* v___x_1407_; 
v___f_1406_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1406_, 0, v_x_1395_);
lean_closure_set(v___f_1406_, 1, v___y_1396_);
lean_closure_set(v___f_1406_, 2, v___y_1397_);
lean_closure_set(v___f_1406_, 3, v___y_1398_);
lean_closure_set(v___f_1406_, 4, v___y_1399_);
lean_closure_set(v___f_1406_, 5, v___y_1400_);
v___x_1407_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1394_, v___f_1406_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
if (lean_obj_tag(v___x_1407_) == 0)
{
return v___x_1407_;
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___boxed(lean_object* v_mvarId_1416_, lean_object* v_x_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_1416_, v_x_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3(lean_object* v_00_u03b1_1429_, lean_object* v_mvarId_1430_, lean_object* v_x_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_1430_, v_x_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___boxed(lean_object* v_00_u03b1_1443_, lean_object* v_mvarId_1444_, lean_object* v_x_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3(v_00_u03b1_1443_, v_mvarId_1444_, v_x_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(lean_object* v_a_1457_, lean_object* v_generation_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v___x_1470_; 
lean_inc_ref(v___y_1465_);
lean_inc(v_a_1457_);
v___x_1470_ = l_Lean_FVarId_getDecl___redArg(v_a_1457_, v___y_1465_, v___y_1467_, v___y_1468_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref(v___x_1470_);
v___x_1472_ = l_Lean_LocalDecl_type(v_a_1471_);
lean_dec(v_a_1471_);
lean_inc(v___y_1468_);
lean_inc_ref(v___y_1467_);
lean_inc(v___y_1466_);
lean_inc_ref(v___y_1465_);
lean_inc_ref(v___x_1472_);
v___x_1473_ = l_Lean_Meta_isProp(v___x_1472_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; uint8_t v___x_1475_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
lean_dec_ref(v___x_1473_);
v___x_1475_ = lean_unbox(v_a_1474_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; 
lean_dec_ref(v___x_1472_);
lean_inc_ref(v___y_1465_);
lean_inc(v_a_1457_);
v___x_1476_ = l_Lean_FVarId_getDecl___redArg(v_a_1457_, v___y_1465_, v___y_1467_, v___y_1468_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; uint8_t v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
lean_dec_ref(v___x_1476_);
v___x_1478_ = lean_unbox(v_a_1474_);
lean_dec(v_a_1474_);
v___x_1479_ = l_Lean_LocalDecl_value(v_a_1477_, v___x_1478_);
lean_dec(v_a_1477_);
lean_inc(v___y_1468_);
lean_inc_ref(v___y_1467_);
lean_inc(v___y_1466_);
lean_inc_ref(v___y_1465_);
lean_inc(v___y_1464_);
lean_inc_ref(v___y_1463_);
lean_inc(v___y_1462_);
lean_inc_ref(v___y_1461_);
lean_inc(v___y_1460_);
lean_inc(v___y_1459_);
v___x_1480_ = l_Lean_Meta_Grind_preprocessHypothesis(v___x_1479_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_a_1481_);
lean_dec_ref(v___x_1480_);
lean_inc(v_a_1457_);
v___x_1482_ = l_Lean_mkFVar(v_a_1457_);
v___x_1483_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_1482_, v___y_1464_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1485_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref(v___x_1483_);
lean_inc(v___y_1468_);
lean_inc_ref(v___y_1467_);
lean_inc(v___y_1466_);
lean_inc_ref(v___y_1465_);
lean_inc(v_a_1481_);
v___x_1485_ = l_Lean_Meta_Simp_Result_getProof(v_a_1481_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v_expr_1487_; lean_object* v___x_1488_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_a_1486_);
lean_dec_ref(v___x_1485_);
v_expr_1487_ = lean_ctor_get(v_a_1481_, 0);
lean_inc_ref(v_expr_1487_);
lean_dec(v_a_1481_);
lean_inc(v___y_1459_);
v___x_1488_ = l_Lean_Meta_Grind_addNewEq(v_a_1484_, v_expr_1487_, v_a_1486_, v_generation_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1497_; 
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1497_ == 0)
{
lean_object* v_unused_1498_; 
v_unused_1498_ = lean_ctor_get(v___x_1488_, 0);
lean_dec(v_unused_1498_);
v___x_1490_ = v___x_1488_;
v_isShared_1491_ = v_isSharedCheck_1497_;
goto v_resetjp_1489_;
}
else
{
lean_dec(v___x_1488_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1497_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1495_; 
v___x_1492_ = lean_st_ref_get(v___y_1459_);
lean_dec(v___y_1459_);
v___x_1493_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1493_, 0, v_a_1457_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 0, v___x_1493_);
v___x_1495_ = v___x_1490_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec(v___y_1459_);
lean_dec(v_a_1457_);
v_a_1499_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1488_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1488_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
else
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
lean_dec(v_a_1484_);
lean_dec(v_a_1481_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec(v_generation_1458_);
lean_dec(v_a_1457_);
v_a_1507_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1509_ = v___x_1485_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1485_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1507_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
else
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
lean_dec(v_a_1481_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec(v_generation_1458_);
lean_dec(v_a_1457_);
v_a_1515_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1483_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1483_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1515_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec(v_generation_1458_);
lean_dec(v_a_1457_);
v_a_1523_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___x_1480_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1480_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
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
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_dec(v_a_1474_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec(v_generation_1458_);
lean_dec(v_a_1457_);
v_a_1531_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1476_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1476_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
else
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_dec(v_a_1474_);
lean_dec(v_generation_1458_);
v___x_1539_ = lean_st_ref_get(v___y_1459_);
v___x_1540_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
lean_inc(v___y_1468_);
lean_inc_ref(v___y_1467_);
lean_inc(v___y_1466_);
lean_inc_ref(v___y_1465_);
lean_inc_ref(v___x_1472_);
v___x_1541_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v___x_1540_, v___x_1472_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v_mvarId_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref(v___x_1541_);
v_mvarId_1543_ = lean_ctor_get(v___x_1539_, 1);
lean_inc(v_mvarId_1543_);
lean_dec(v___x_1539_);
v___x_1544_ = l_Lean_mkFVar(v_a_1457_);
v___x_1545_ = l_Lean_MVarId_assert(v_mvarId_1543_, v_a_1542_, v___x_1472_, v___x_1544_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1564_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1548_ = v___x_1545_;
v_isShared_1549_ = v_isSharedCheck_1564_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1545_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1564_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1550_; lean_object* v_toGoalState_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1562_; 
v___x_1550_ = lean_st_ref_get(v___y_1459_);
lean_dec(v___y_1459_);
v_toGoalState_1551_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1562_ == 0)
{
lean_object* v_unused_1563_; 
v_unused_1563_ = lean_ctor_get(v___x_1550_, 1);
lean_dec(v_unused_1563_);
v___x_1553_ = v___x_1550_;
v_isShared_1554_ = v_isSharedCheck_1562_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_toGoalState_1551_);
lean_dec(v___x_1550_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1562_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 1, v_a_1546_);
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_toGoalState_1551_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v_a_1546_);
v___x_1556_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1557_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v___x_1557_);
v___x_1559_ = v___x_1548_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec(v___y_1459_);
v_a_1565_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1545_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1545_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec(v___x_1539_);
lean_dec_ref(v___x_1472_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1459_);
lean_dec(v_a_1457_);
v_a_1573_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1541_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1541_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec_ref(v___x_1472_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec(v_generation_1458_);
lean_dec(v_a_1457_);
v_a_1581_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1473_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1473_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec(v_generation_1458_);
lean_dec(v_a_1457_);
v_a_1589_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1470_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1470_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed(lean_object* v_a_1597_, lean_object* v_generation_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(v_a_1597_, v_generation_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(lean_object* v_x_1611_, lean_object* v_x_1612_, lean_object* v_x_1613_, lean_object* v_x_1614_){
_start:
{
lean_object* v_ks_1615_; lean_object* v_vs_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1640_; 
v_ks_1615_ = lean_ctor_get(v_x_1611_, 0);
v_vs_1616_ = lean_ctor_get(v_x_1611_, 1);
v_isSharedCheck_1640_ = !lean_is_exclusive(v_x_1611_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1618_ = v_x_1611_;
v_isShared_1619_ = v_isSharedCheck_1640_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_vs_1616_);
lean_inc(v_ks_1615_);
lean_dec(v_x_1611_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1640_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1620_ = lean_array_get_size(v_ks_1615_);
v___x_1621_ = lean_nat_dec_lt(v_x_1612_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1625_; 
lean_dec(v_x_1612_);
v___x_1622_ = lean_array_push(v_ks_1615_, v_x_1613_);
v___x_1623_ = lean_array_push(v_vs_1616_, v_x_1614_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 1, v___x_1623_);
lean_ctor_set(v___x_1618_, 0, v___x_1622_);
v___x_1625_ = v___x_1618_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1622_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v___x_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
else
{
lean_object* v_k_x27_1627_; uint8_t v___x_1628_; 
v_k_x27_1627_ = lean_array_fget_borrowed(v_ks_1615_, v_x_1612_);
v___x_1628_ = l_Lean_instBEqMVarId_beq(v_x_1613_, v_k_x27_1627_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1630_; 
if (v_isShared_1619_ == 0)
{
v___x_1630_ = v___x_1618_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_ks_1615_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_vs_1616_);
v___x_1630_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = lean_unsigned_to_nat(1u);
v___x_1632_ = lean_nat_add(v_x_1612_, v___x_1631_);
lean_dec(v_x_1612_);
v_x_1611_ = v___x_1630_;
v_x_1612_ = v___x_1632_;
goto _start;
}
}
else
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1638_; 
v___x_1635_ = lean_array_fset(v_ks_1615_, v_x_1612_, v_x_1613_);
v___x_1636_ = lean_array_fset(v_vs_1616_, v_x_1612_, v_x_1614_);
lean_dec(v_x_1612_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 1, v___x_1636_);
lean_ctor_set(v___x_1618_, 0, v___x_1635_);
v___x_1638_ = v___x_1618_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1635_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v___x_1636_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(lean_object* v_n_1641_, lean_object* v_k_1642_, lean_object* v_v_1643_){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = lean_unsigned_to_nat(0u);
v___x_1645_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_n_1641_, v___x_1644_, v_k_1642_, v_v_1643_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1646_, size_t v_x_1647_, size_t v_x_1648_, lean_object* v_x_1649_, lean_object* v_x_1650_){
_start:
{
if (lean_obj_tag(v_x_1646_) == 0)
{
lean_object* v_es_1651_; size_t v___x_1652_; size_t v___x_1653_; size_t v___x_1654_; size_t v___x_1655_; lean_object* v_j_1656_; lean_object* v___x_1657_; uint8_t v___x_1658_; 
v_es_1651_ = lean_ctor_get(v_x_1646_, 0);
v___x_1652_ = ((size_t)5ULL);
v___x_1653_ = ((size_t)1ULL);
v___x_1654_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__1);
v___x_1655_ = lean_usize_land(v_x_1647_, v___x_1654_);
v_j_1656_ = lean_usize_to_nat(v___x_1655_);
v___x_1657_ = lean_array_get_size(v_es_1651_);
v___x_1658_ = lean_nat_dec_lt(v_j_1656_, v___x_1657_);
if (v___x_1658_ == 0)
{
lean_dec(v_j_1656_);
lean_dec(v_x_1650_);
lean_dec(v_x_1649_);
return v_x_1646_;
}
else
{
lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1695_; 
lean_inc_ref(v_es_1651_);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_x_1646_);
if (v_isSharedCheck_1695_ == 0)
{
lean_object* v_unused_1696_; 
v_unused_1696_ = lean_ctor_get(v_x_1646_, 0);
lean_dec(v_unused_1696_);
v___x_1660_ = v_x_1646_;
v_isShared_1661_ = v_isSharedCheck_1695_;
goto v_resetjp_1659_;
}
else
{
lean_dec(v_x_1646_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1695_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v_v_1662_; lean_object* v___x_1663_; lean_object* v_xs_x27_1664_; lean_object* v___y_1666_; 
v_v_1662_ = lean_array_fget(v_es_1651_, v_j_1656_);
v___x_1663_ = lean_box(0);
v_xs_x27_1664_ = lean_array_fset(v_es_1651_, v_j_1656_, v___x_1663_);
switch(lean_obj_tag(v_v_1662_))
{
case 0:
{
lean_object* v_key_1671_; lean_object* v_val_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1682_; 
v_key_1671_ = lean_ctor_get(v_v_1662_, 0);
v_val_1672_ = lean_ctor_get(v_v_1662_, 1);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_v_1662_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1674_ = v_v_1662_;
v_isShared_1675_ = v_isSharedCheck_1682_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_val_1672_);
lean_inc(v_key_1671_);
lean_dec(v_v_1662_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1682_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
uint8_t v___x_1676_; 
v___x_1676_ = l_Lean_instBEqMVarId_beq(v_x_1649_, v_key_1671_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_del_object(v___x_1674_);
v___x_1677_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1671_, v_val_1672_, v_x_1649_, v_x_1650_);
v___x_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
v___y_1666_ = v___x_1678_;
goto v___jp_1665_;
}
else
{
lean_object* v___x_1680_; 
lean_dec(v_val_1672_);
lean_dec(v_key_1671_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 1, v_x_1650_);
lean_ctor_set(v___x_1674_, 0, v_x_1649_);
v___x_1680_ = v___x_1674_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_x_1649_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v_x_1650_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
v___y_1666_ = v___x_1680_;
goto v___jp_1665_;
}
}
}
}
case 1:
{
lean_object* v_node_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1693_; 
v_node_1683_ = lean_ctor_get(v_v_1662_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_v_1662_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1685_ = v_v_1662_;
v_isShared_1686_ = v_isSharedCheck_1693_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_node_1683_);
lean_dec(v_v_1662_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1693_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
size_t v___x_1687_; size_t v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1687_ = lean_usize_shift_right(v_x_1647_, v___x_1652_);
v___x_1688_ = lean_usize_add(v_x_1648_, v___x_1653_);
v___x_1689_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_node_1683_, v___x_1687_, v___x_1688_, v_x_1649_, v_x_1650_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 0, v___x_1689_);
v___x_1691_ = v___x_1685_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
v___y_1666_ = v___x_1691_;
goto v___jp_1665_;
}
}
}
default: 
{
lean_object* v___x_1694_; 
v___x_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1694_, 0, v_x_1649_);
lean_ctor_set(v___x_1694_, 1, v_x_1650_);
v___y_1666_ = v___x_1694_;
goto v___jp_1665_;
}
}
v___jp_1665_:
{
lean_object* v___x_1667_; lean_object* v___x_1669_; 
v___x_1667_ = lean_array_fset(v_xs_x27_1664_, v_j_1656_, v___y_1666_);
lean_dec(v_j_1656_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1667_);
v___x_1669_ = v___x_1660_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1667_);
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
else
{
lean_object* v_ks_1697_; lean_object* v_vs_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1718_; 
v_ks_1697_ = lean_ctor_get(v_x_1646_, 0);
v_vs_1698_ = lean_ctor_get(v_x_1646_, 1);
v_isSharedCheck_1718_ = !lean_is_exclusive(v_x_1646_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1700_ = v_x_1646_;
v_isShared_1701_ = v_isSharedCheck_1718_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_vs_1698_);
lean_inc(v_ks_1697_);
lean_dec(v_x_1646_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1718_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_ks_1697_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_vs_1698_);
v___x_1703_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
lean_object* v_newNode_1704_; uint8_t v___y_1706_; size_t v___x_1712_; uint8_t v___x_1713_; 
v_newNode_1704_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(v___x_1703_, v_x_1649_, v_x_1650_);
v___x_1712_ = ((size_t)7ULL);
v___x_1713_ = lean_usize_dec_le(v___x_1712_, v_x_1648_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; 
v___x_1714_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1704_);
v___x_1715_ = lean_unsigned_to_nat(4u);
v___x_1716_ = lean_nat_dec_lt(v___x_1714_, v___x_1715_);
lean_dec(v___x_1714_);
v___y_1706_ = v___x_1716_;
goto v___jp_1705_;
}
else
{
v___y_1706_ = v___x_1713_;
goto v___jp_1705_;
}
v___jp_1705_:
{
if (v___y_1706_ == 0)
{
lean_object* v_ks_1707_; lean_object* v_vs_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v_ks_1707_ = lean_ctor_get(v_newNode_1704_, 0);
lean_inc_ref(v_ks_1707_);
v_vs_1708_ = lean_ctor_get(v_newNode_1704_, 1);
lean_inc_ref(v_vs_1708_);
lean_dec_ref(v_newNode_1704_);
v___x_1709_ = lean_unsigned_to_nat(0u);
v___x_1710_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__2);
v___x_1711_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_x_1648_, v_ks_1707_, v_vs_1708_, v___x_1709_, v___x_1710_);
lean_dec_ref(v_vs_1708_);
lean_dec_ref(v_ks_1707_);
return v___x_1711_;
}
else
{
return v_newNode_1704_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(size_t v_depth_1719_, lean_object* v_keys_1720_, lean_object* v_vals_1721_, lean_object* v_i_1722_, lean_object* v_entries_1723_){
_start:
{
lean_object* v___x_1724_; uint8_t v___x_1725_; 
v___x_1724_ = lean_array_get_size(v_keys_1720_);
v___x_1725_ = lean_nat_dec_lt(v_i_1722_, v___x_1724_);
if (v___x_1725_ == 0)
{
lean_dec(v_i_1722_);
return v_entries_1723_;
}
else
{
lean_object* v_k_1726_; lean_object* v_v_1727_; uint64_t v___x_1728_; size_t v_h_1729_; size_t v___x_1730_; lean_object* v___x_1731_; size_t v___x_1732_; size_t v___x_1733_; size_t v___x_1734_; size_t v_h_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v_k_1726_ = lean_array_fget_borrowed(v_keys_1720_, v_i_1722_);
v_v_1727_ = lean_array_fget_borrowed(v_vals_1721_, v_i_1722_);
v___x_1728_ = l_Lean_instHashableMVarId_hash(v_k_1726_);
v_h_1729_ = lean_uint64_to_usize(v___x_1728_);
v___x_1730_ = ((size_t)5ULL);
v___x_1731_ = lean_unsigned_to_nat(1u);
v___x_1732_ = ((size_t)1ULL);
v___x_1733_ = lean_usize_sub(v_depth_1719_, v___x_1732_);
v___x_1734_ = lean_usize_mul(v___x_1730_, v___x_1733_);
v_h_1735_ = lean_usize_shift_right(v_h_1729_, v___x_1734_);
v___x_1736_ = lean_nat_add(v_i_1722_, v___x_1731_);
lean_dec(v_i_1722_);
lean_inc(v_v_1727_);
lean_inc(v_k_1726_);
v___x_1737_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_entries_1723_, v_h_1735_, v_depth_1719_, v_k_1726_, v_v_1727_);
v_i_1722_ = v___x_1736_;
v_entries_1723_ = v___x_1737_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_depth_1739_, lean_object* v_keys_1740_, lean_object* v_vals_1741_, lean_object* v_i_1742_, lean_object* v_entries_1743_){
_start:
{
size_t v_depth_boxed_1744_; lean_object* v_res_1745_; 
v_depth_boxed_1744_ = lean_unbox_usize(v_depth_1739_);
lean_dec(v_depth_1739_);
v_res_1745_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_boxed_1744_, v_keys_1740_, v_vals_1741_, v_i_1742_, v_entries_1743_);
lean_dec_ref(v_vals_1741_);
lean_dec_ref(v_keys_1740_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_1746_, lean_object* v_x_1747_, lean_object* v_x_1748_, lean_object* v_x_1749_, lean_object* v_x_1750_){
_start:
{
size_t v_x_196790__boxed_1751_; size_t v_x_196791__boxed_1752_; lean_object* v_res_1753_; 
v_x_196790__boxed_1751_ = lean_unbox_usize(v_x_1747_);
lean_dec(v_x_1747_);
v_x_196791__boxed_1752_ = lean_unbox_usize(v_x_1748_);
lean_dec(v_x_1748_);
v_res_1753_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_1746_, v_x_196790__boxed_1751_, v_x_196791__boxed_1752_, v_x_1749_, v_x_1750_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(lean_object* v_x_1754_, lean_object* v_x_1755_, lean_object* v_x_1756_){
_start:
{
uint64_t v___x_1757_; size_t v___x_1758_; size_t v___x_1759_; lean_object* v___x_1760_; 
v___x_1757_ = l_Lean_instHashableMVarId_hash(v_x_1755_);
v___x_1758_ = lean_uint64_to_usize(v___x_1757_);
v___x_1759_ = ((size_t)1ULL);
v___x_1760_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_1754_, v___x_1758_, v___x_1759_, v_x_1755_, v_x_1756_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(lean_object* v_mvarId_1761_, lean_object* v_val_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v___x_1765_; lean_object* v_mctx_1766_; lean_object* v_cache_1767_; lean_object* v_zetaDeltaFVarIds_1768_; lean_object* v_postponed_1769_; lean_object* v_diag_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1797_; 
v___x_1765_ = lean_st_ref_take(v___y_1763_);
v_mctx_1766_ = lean_ctor_get(v___x_1765_, 0);
v_cache_1767_ = lean_ctor_get(v___x_1765_, 1);
v_zetaDeltaFVarIds_1768_ = lean_ctor_get(v___x_1765_, 2);
v_postponed_1769_ = lean_ctor_get(v___x_1765_, 3);
v_diag_1770_ = lean_ctor_get(v___x_1765_, 4);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1772_ = v___x_1765_;
v_isShared_1773_ = v_isSharedCheck_1797_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_diag_1770_);
lean_inc(v_postponed_1769_);
lean_inc(v_zetaDeltaFVarIds_1768_);
lean_inc(v_cache_1767_);
lean_inc(v_mctx_1766_);
lean_dec(v___x_1765_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1797_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v_depth_1774_; lean_object* v_levelAssignDepth_1775_; lean_object* v_mvarCounter_1776_; lean_object* v_lDepth_1777_; lean_object* v_decls_1778_; lean_object* v_userNames_1779_; lean_object* v_lAssignment_1780_; lean_object* v_eAssignment_1781_; lean_object* v_dAssignment_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1796_; 
v_depth_1774_ = lean_ctor_get(v_mctx_1766_, 0);
v_levelAssignDepth_1775_ = lean_ctor_get(v_mctx_1766_, 1);
v_mvarCounter_1776_ = lean_ctor_get(v_mctx_1766_, 2);
v_lDepth_1777_ = lean_ctor_get(v_mctx_1766_, 3);
v_decls_1778_ = lean_ctor_get(v_mctx_1766_, 4);
v_userNames_1779_ = lean_ctor_get(v_mctx_1766_, 5);
v_lAssignment_1780_ = lean_ctor_get(v_mctx_1766_, 6);
v_eAssignment_1781_ = lean_ctor_get(v_mctx_1766_, 7);
v_dAssignment_1782_ = lean_ctor_get(v_mctx_1766_, 8);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_mctx_1766_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1784_ = v_mctx_1766_;
v_isShared_1785_ = v_isSharedCheck_1796_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_dAssignment_1782_);
lean_inc(v_eAssignment_1781_);
lean_inc(v_lAssignment_1780_);
lean_inc(v_userNames_1779_);
lean_inc(v_decls_1778_);
lean_inc(v_lDepth_1777_);
lean_inc(v_mvarCounter_1776_);
lean_inc(v_levelAssignDepth_1775_);
lean_inc(v_depth_1774_);
lean_dec(v_mctx_1766_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1796_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1786_; lean_object* v___x_1788_; 
v___x_1786_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_eAssignment_1781_, v_mvarId_1761_, v_val_1762_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 7, v___x_1786_);
v___x_1788_ = v___x_1784_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_depth_1774_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v_levelAssignDepth_1775_);
lean_ctor_set(v_reuseFailAlloc_1795_, 2, v_mvarCounter_1776_);
lean_ctor_set(v_reuseFailAlloc_1795_, 3, v_lDepth_1777_);
lean_ctor_set(v_reuseFailAlloc_1795_, 4, v_decls_1778_);
lean_ctor_set(v_reuseFailAlloc_1795_, 5, v_userNames_1779_);
lean_ctor_set(v_reuseFailAlloc_1795_, 6, v_lAssignment_1780_);
lean_ctor_set(v_reuseFailAlloc_1795_, 7, v___x_1786_);
lean_ctor_set(v_reuseFailAlloc_1795_, 8, v_dAssignment_1782_);
v___x_1788_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
lean_object* v___x_1790_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1788_);
v___x_1790_ = v___x_1772_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1788_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_cache_1767_);
lean_ctor_set(v_reuseFailAlloc_1794_, 2, v_zetaDeltaFVarIds_1768_);
lean_ctor_set(v_reuseFailAlloc_1794_, 3, v_postponed_1769_);
lean_ctor_set(v_reuseFailAlloc_1794_, 4, v_diag_1770_);
v___x_1790_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1791_ = lean_st_ref_set(v___y_1763_, v___x_1790_);
v___x_1792_ = lean_box(0);
v___x_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
return v___x_1793_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg___boxed(lean_object* v_mvarId_1798_, lean_object* v_val_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1798_, v_val_1799_, v___y_1800_);
lean_dec(v___y_1800_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(lean_object* v___y_1803_){
_start:
{
lean_object* v___x_1805_; lean_object* v_ngen_1806_; lean_object* v_namePrefix_1807_; lean_object* v_idx_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1837_; 
v___x_1805_ = lean_st_ref_get(v___y_1803_);
v_ngen_1806_ = lean_ctor_get(v___x_1805_, 2);
lean_inc_ref(v_ngen_1806_);
lean_dec(v___x_1805_);
v_namePrefix_1807_ = lean_ctor_get(v_ngen_1806_, 0);
v_idx_1808_ = lean_ctor_get(v_ngen_1806_, 1);
v_isSharedCheck_1837_ = !lean_is_exclusive(v_ngen_1806_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1810_ = v_ngen_1806_;
v_isShared_1811_ = v_isSharedCheck_1837_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_idx_1808_);
lean_inc(v_namePrefix_1807_);
lean_dec(v_ngen_1806_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1837_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1812_; lean_object* v_env_1813_; lean_object* v_nextMacroScope_1814_; lean_object* v_auxDeclNGen_1815_; lean_object* v_traceState_1816_; lean_object* v_cache_1817_; lean_object* v_messages_1818_; lean_object* v_infoState_1819_; lean_object* v_snapshotTasks_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1835_; 
v___x_1812_ = lean_st_ref_take(v___y_1803_);
v_env_1813_ = lean_ctor_get(v___x_1812_, 0);
v_nextMacroScope_1814_ = lean_ctor_get(v___x_1812_, 1);
v_auxDeclNGen_1815_ = lean_ctor_get(v___x_1812_, 3);
v_traceState_1816_ = lean_ctor_get(v___x_1812_, 4);
v_cache_1817_ = lean_ctor_get(v___x_1812_, 5);
v_messages_1818_ = lean_ctor_get(v___x_1812_, 6);
v_infoState_1819_ = lean_ctor_get(v___x_1812_, 7);
v_snapshotTasks_1820_ = lean_ctor_get(v___x_1812_, 8);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1835_ == 0)
{
lean_object* v_unused_1836_; 
v_unused_1836_ = lean_ctor_get(v___x_1812_, 2);
lean_dec(v_unused_1836_);
v___x_1822_ = v___x_1812_;
v_isShared_1823_ = v_isSharedCheck_1835_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_snapshotTasks_1820_);
lean_inc(v_infoState_1819_);
lean_inc(v_messages_1818_);
lean_inc(v_cache_1817_);
lean_inc(v_traceState_1816_);
lean_inc(v_auxDeclNGen_1815_);
lean_inc(v_nextMacroScope_1814_);
lean_inc(v_env_1813_);
lean_dec(v___x_1812_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1835_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v_r_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1828_; 
lean_inc(v_idx_1808_);
lean_inc(v_namePrefix_1807_);
v_r_1824_ = l_Lean_Name_num___override(v_namePrefix_1807_, v_idx_1808_);
v___x_1825_ = lean_unsigned_to_nat(1u);
v___x_1826_ = lean_nat_add(v_idx_1808_, v___x_1825_);
lean_dec(v_idx_1808_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 1, v___x_1826_);
v___x_1828_ = v___x_1810_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_namePrefix_1807_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v___x_1826_);
v___x_1828_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1830_; 
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 2, v___x_1828_);
v___x_1830_ = v___x_1822_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_env_1813_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v_nextMacroScope_1814_);
lean_ctor_set(v_reuseFailAlloc_1833_, 2, v___x_1828_);
lean_ctor_set(v_reuseFailAlloc_1833_, 3, v_auxDeclNGen_1815_);
lean_ctor_set(v_reuseFailAlloc_1833_, 4, v_traceState_1816_);
lean_ctor_set(v_reuseFailAlloc_1833_, 5, v_cache_1817_);
lean_ctor_set(v_reuseFailAlloc_1833_, 6, v_messages_1818_);
lean_ctor_set(v_reuseFailAlloc_1833_, 7, v_infoState_1819_);
lean_ctor_set(v_reuseFailAlloc_1833_, 8, v_snapshotTasks_1820_);
v___x_1830_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1831_ = lean_st_ref_set(v___y_1803_, v___x_1830_);
v___x_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1832_, 0, v_r_1824_);
return v___x_1832_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg___boxed(lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_1838_);
lean_dec(v___y_1838_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v___x_1852_; lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
v___x_1852_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_1850_);
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1852_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1852_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2___boxed(lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(lean_object* v___x_1878_, lean_object* v_a_1879_, uint8_t v___y_1880_, uint8_t v___x_1881_, uint8_t v___x_1882_, lean_object* v_a_1883_, lean_object* v___x_1884_, lean_object* v_expr_1885_, lean_object* v___x_1886_, lean_object* v_val_1887_, lean_object* v_mvarId_1888_, lean_object* v___x_1889_, lean_object* v_a_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Lean_Meta_mkLambdaFVars(v___x_1878_, v_a_1879_, v___y_1880_, v___x_1881_, v___y_1880_, v___x_1881_, v___x_1882_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref(v___x_1902_);
v___x_1904_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1));
v___x_1905_ = lean_box(0);
v___x_1906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1906_, 0, v_a_1883_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
v___x_1907_ = l_Lean_mkConst(v___x_1904_, v___x_1906_);
v___x_1908_ = lean_unsigned_to_nat(5u);
v___x_1909_ = lean_mk_empty_array_with_capacity(v___x_1908_);
v___x_1910_ = lean_array_push(v___x_1909_, v___x_1884_);
v___x_1911_ = lean_array_push(v___x_1910_, v_expr_1885_);
v___x_1912_ = lean_array_push(v___x_1911_, v___x_1886_);
v___x_1913_ = lean_array_push(v___x_1912_, v_val_1887_);
v___x_1914_ = lean_array_push(v___x_1913_, v_a_1903_);
v___x_1915_ = l_Lean_mkAppN(v___x_1907_, v___x_1914_);
lean_dec_ref(v___x_1914_);
v___x_1916_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1888_, v___x_1915_, v___y_1898_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1934_; 
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1934_ == 0)
{
lean_object* v_unused_1935_; 
v_unused_1935_ = lean_ctor_get(v___x_1916_, 0);
lean_dec(v_unused_1935_);
v___x_1918_ = v___x_1916_;
v_isShared_1919_ = v_isSharedCheck_1934_;
goto v_resetjp_1917_;
}
else
{
lean_dec(v___x_1916_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1934_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1920_; lean_object* v_toGoalState_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1932_; 
v___x_1920_ = lean_st_ref_get(v___y_1891_);
v_toGoalState_1921_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1932_ == 0)
{
lean_object* v_unused_1933_; 
v_unused_1933_ = lean_ctor_get(v___x_1920_, 1);
lean_dec(v_unused_1933_);
v___x_1923_ = v___x_1920_;
v_isShared_1924_ = v_isSharedCheck_1932_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_toGoalState_1921_);
lean_dec(v___x_1920_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1932_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 1, v___x_1889_);
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_toGoalState_1921_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v___x_1889_);
v___x_1926_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
lean_object* v___x_1927_; lean_object* v___x_1929_; 
v___x_1927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1927_, 0, v_a_1890_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 0, v___x_1927_);
v___x_1929_ = v___x_1918_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_dec(v_a_1890_);
lean_dec(v___x_1889_);
v_a_1936_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1916_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1916_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec(v_a_1890_);
lean_dec(v___x_1889_);
lean_dec(v_mvarId_1888_);
lean_dec_ref(v_val_1887_);
lean_dec_ref(v___x_1886_);
lean_dec_ref(v_expr_1885_);
lean_dec_ref(v___x_1884_);
lean_dec(v_a_1883_);
v_a_1944_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1902_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1902_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed(lean_object** _args){
lean_object* v___x_1952_ = _args[0];
lean_object* v_a_1953_ = _args[1];
lean_object* v___y_1954_ = _args[2];
lean_object* v___x_1955_ = _args[3];
lean_object* v___x_1956_ = _args[4];
lean_object* v_a_1957_ = _args[5];
lean_object* v___x_1958_ = _args[6];
lean_object* v_expr_1959_ = _args[7];
lean_object* v___x_1960_ = _args[8];
lean_object* v_val_1961_ = _args[9];
lean_object* v_mvarId_1962_ = _args[10];
lean_object* v___x_1963_ = _args[11];
lean_object* v_a_1964_ = _args[12];
lean_object* v___y_1965_ = _args[13];
lean_object* v___y_1966_ = _args[14];
lean_object* v___y_1967_ = _args[15];
lean_object* v___y_1968_ = _args[16];
lean_object* v___y_1969_ = _args[17];
lean_object* v___y_1970_ = _args[18];
lean_object* v___y_1971_ = _args[19];
lean_object* v___y_1972_ = _args[20];
lean_object* v___y_1973_ = _args[21];
lean_object* v___y_1974_ = _args[22];
lean_object* v___y_1975_ = _args[23];
_start:
{
uint8_t v___y_197117__boxed_1976_; uint8_t v___x_197118__boxed_1977_; uint8_t v___x_197119__boxed_1978_; lean_object* v_res_1979_; 
v___y_197117__boxed_1976_ = lean_unbox(v___y_1954_);
v___x_197118__boxed_1977_ = lean_unbox(v___x_1955_);
v___x_197119__boxed_1978_ = lean_unbox(v___x_1956_);
v_res_1979_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(v___x_1952_, v_a_1953_, v___y_197117__boxed_1976_, v___x_197118__boxed_1977_, v___x_197119__boxed_1978_, v_a_1957_, v___x_1958_, v_expr_1959_, v___x_1960_, v_val_1961_, v_mvarId_1962_, v___x_1963_, v_a_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec_ref(v___x_1952_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(lean_object* v___x_1985_, lean_object* v_a_1986_, uint8_t v___x_1987_, uint8_t v___x_1988_, uint8_t v___x_1989_, lean_object* v_a_1990_, lean_object* v___x_1991_, lean_object* v___x_1992_, lean_object* v_expr_1993_, lean_object* v___x_1994_, lean_object* v_val_1995_, lean_object* v_mvarId_1996_, lean_object* v___x_1997_, lean_object* v_a_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = l_Lean_Meta_mkLambdaFVars(v___x_1985_, v_a_1986_, v___x_1987_, v___x_1988_, v___x_1987_, v___x_1988_, v___x_1989_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref(v___x_2010_);
v___x_2012_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1));
v___x_2013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2013_, 0, v_a_1990_);
lean_ctor_set(v___x_2013_, 1, v___x_1991_);
v___x_2014_ = l_Lean_mkConst(v___x_2012_, v___x_2013_);
v___x_2015_ = lean_unsigned_to_nat(5u);
v___x_2016_ = lean_mk_empty_array_with_capacity(v___x_2015_);
v___x_2017_ = lean_array_push(v___x_2016_, v___x_1992_);
v___x_2018_ = lean_array_push(v___x_2017_, v_expr_1993_);
v___x_2019_ = lean_array_push(v___x_2018_, v___x_1994_);
v___x_2020_ = lean_array_push(v___x_2019_, v_val_1995_);
v___x_2021_ = lean_array_push(v___x_2020_, v_a_2011_);
v___x_2022_ = l_Lean_mkAppN(v___x_2014_, v___x_2021_);
lean_dec_ref(v___x_2021_);
v___x_2023_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1996_, v___x_2022_, v___y_2006_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2041_; 
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2041_ == 0)
{
lean_object* v_unused_2042_; 
v_unused_2042_ = lean_ctor_get(v___x_2023_, 0);
lean_dec(v_unused_2042_);
v___x_2025_ = v___x_2023_;
v_isShared_2026_ = v_isSharedCheck_2041_;
goto v_resetjp_2024_;
}
else
{
lean_dec(v___x_2023_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2041_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2027_; lean_object* v_toGoalState_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2039_; 
v___x_2027_ = lean_st_ref_get(v___y_1999_);
v_toGoalState_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2039_ == 0)
{
lean_object* v_unused_2040_; 
v_unused_2040_ = lean_ctor_get(v___x_2027_, 1);
lean_dec(v_unused_2040_);
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2039_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_toGoalState_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2039_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 1, v___x_1997_);
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_toGoalState_2028_);
lean_ctor_set(v_reuseFailAlloc_2038_, 1, v___x_1997_);
v___x_2033_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_2034_; lean_object* v___x_2036_; 
v___x_2034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2034_, 0, v_a_1998_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v___x_2034_);
v___x_2036_ = v___x_2025_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2034_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec(v_a_1998_);
lean_dec(v___x_1997_);
v_a_2043_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2023_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2023_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec(v_a_1998_);
lean_dec(v___x_1997_);
lean_dec(v_mvarId_1996_);
lean_dec_ref(v_val_1995_);
lean_dec_ref(v___x_1994_);
lean_dec_ref(v_expr_1993_);
lean_dec_ref(v___x_1992_);
lean_dec(v___x_1991_);
lean_dec(v_a_1990_);
v_a_2051_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2010_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2010_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed(lean_object** _args){
lean_object* v___x_2059_ = _args[0];
lean_object* v_a_2060_ = _args[1];
lean_object* v___x_2061_ = _args[2];
lean_object* v___x_2062_ = _args[3];
lean_object* v___x_2063_ = _args[4];
lean_object* v_a_2064_ = _args[5];
lean_object* v___x_2065_ = _args[6];
lean_object* v___x_2066_ = _args[7];
lean_object* v_expr_2067_ = _args[8];
lean_object* v___x_2068_ = _args[9];
lean_object* v_val_2069_ = _args[10];
lean_object* v_mvarId_2070_ = _args[11];
lean_object* v___x_2071_ = _args[12];
lean_object* v_a_2072_ = _args[13];
lean_object* v___y_2073_ = _args[14];
lean_object* v___y_2074_ = _args[15];
lean_object* v___y_2075_ = _args[16];
lean_object* v___y_2076_ = _args[17];
lean_object* v___y_2077_ = _args[18];
lean_object* v___y_2078_ = _args[19];
lean_object* v___y_2079_ = _args[20];
lean_object* v___y_2080_ = _args[21];
lean_object* v___y_2081_ = _args[22];
lean_object* v___y_2082_ = _args[23];
lean_object* v___y_2083_ = _args[24];
_start:
{
uint8_t v___x_197299__boxed_2084_; uint8_t v___x_197300__boxed_2085_; uint8_t v___x_197301__boxed_2086_; lean_object* v_res_2087_; 
v___x_197299__boxed_2084_ = lean_unbox(v___x_2061_);
v___x_197300__boxed_2085_ = lean_unbox(v___x_2062_);
v___x_197301__boxed_2086_ = lean_unbox(v___x_2063_);
v_res_2087_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(v___x_2059_, v_a_2060_, v___x_197299__boxed_2084_, v___x_197300__boxed_2085_, v___x_197301__boxed_2086_, v_a_2064_, v___x_2065_, v___x_2066_, v_expr_2067_, v___x_2068_, v_val_2069_, v_mvarId_2070_, v___x_2071_, v_a_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___x_2059_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(lean_object* v___x_2088_, lean_object* v_a_2089_, uint8_t v___y_2090_, uint8_t v___x_2091_, uint8_t v___x_2092_, lean_object* v_mvarId_2093_, lean_object* v___x_2094_, lean_object* v_a_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l_Lean_Meta_mkLambdaFVars(v___x_2088_, v_a_2089_, v___y_2090_, v___x_2091_, v___y_2090_, v___x_2091_, v___x_2092_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; lean_object* v___x_2109_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref(v___x_2107_);
v___x_2109_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2093_, v_a_2108_, v___y_2103_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2127_; 
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2127_ == 0)
{
lean_object* v_unused_2128_; 
v_unused_2128_ = lean_ctor_get(v___x_2109_, 0);
lean_dec(v_unused_2128_);
v___x_2111_ = v___x_2109_;
v_isShared_2112_ = v_isSharedCheck_2127_;
goto v_resetjp_2110_;
}
else
{
lean_dec(v___x_2109_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2127_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2113_; lean_object* v_toGoalState_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2125_; 
v___x_2113_ = lean_st_ref_get(v___y_2096_);
v_toGoalState_2114_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2125_ == 0)
{
lean_object* v_unused_2126_; 
v_unused_2126_ = lean_ctor_get(v___x_2113_, 1);
lean_dec(v_unused_2126_);
v___x_2116_ = v___x_2113_;
v_isShared_2117_ = v_isSharedCheck_2125_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_toGoalState_2114_);
lean_dec(v___x_2113_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2125_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 1, v___x_2094_);
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_toGoalState_2114_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v___x_2094_);
v___x_2119_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v___x_2120_; lean_object* v___x_2122_; 
v___x_2120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2120_, 0, v_a_2095_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v___x_2120_);
v___x_2122_ = v___x_2111_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_dec(v_a_2095_);
lean_dec(v___x_2094_);
v_a_2129_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2109_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2109_);
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
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec(v_a_2095_);
lean_dec(v___x_2094_);
lean_dec(v_mvarId_2093_);
v_a_2137_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2107_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2107_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed(lean_object** _args){
lean_object* v___x_2145_ = _args[0];
lean_object* v_a_2146_ = _args[1];
lean_object* v___y_2147_ = _args[2];
lean_object* v___x_2148_ = _args[3];
lean_object* v___x_2149_ = _args[4];
lean_object* v_mvarId_2150_ = _args[5];
lean_object* v___x_2151_ = _args[6];
lean_object* v_a_2152_ = _args[7];
lean_object* v___y_2153_ = _args[8];
lean_object* v___y_2154_ = _args[9];
lean_object* v___y_2155_ = _args[10];
lean_object* v___y_2156_ = _args[11];
lean_object* v___y_2157_ = _args[12];
lean_object* v___y_2158_ = _args[13];
lean_object* v___y_2159_ = _args[14];
lean_object* v___y_2160_ = _args[15];
lean_object* v___y_2161_ = _args[16];
lean_object* v___y_2162_ = _args[17];
lean_object* v___y_2163_ = _args[18];
_start:
{
uint8_t v___y_197470__boxed_2164_; uint8_t v___x_197471__boxed_2165_; uint8_t v___x_197472__boxed_2166_; lean_object* v_res_2167_; 
v___y_197470__boxed_2164_ = lean_unbox(v___y_2147_);
v___x_197471__boxed_2165_ = lean_unbox(v___x_2148_);
v___x_197472__boxed_2166_ = lean_unbox(v___x_2149_);
v_res_2167_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(v___x_2145_, v_a_2146_, v___y_197470__boxed_2164_, v___x_197471__boxed_2165_, v___x_197472__boxed_2166_, v_mvarId_2150_, v___x_2151_, v_a_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___x_2145_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(lean_object* v_mvarId_2170_, lean_object* v___x_2171_, lean_object* v_generation_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v___x_2184_; 
lean_inc(v_mvarId_2170_);
v___x_2184_ = l_Lean_MVarId_getTag(v_mvarId_2170_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___x_2186_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
lean_dec_ref(v___x_2184_);
lean_inc_ref(v___y_2179_);
v___x_2186_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2171_, v_a_2185_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v___x_2188_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
lean_dec_ref(v___x_2186_);
lean_inc(v_a_2187_);
v___x_2188_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2170_, v_a_2187_, v___y_2180_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v___x_2189_; lean_object* v_toGoalState_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2199_; 
lean_dec_ref(v___x_2188_);
v___x_2189_ = lean_st_ref_get(v___y_2173_);
v_toGoalState_2190_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2199_ == 0)
{
lean_object* v_unused_2200_; 
v_unused_2200_ = lean_ctor_get(v___x_2189_, 1);
lean_dec(v_unused_2200_);
v___x_2192_ = v___x_2189_;
v_isShared_2193_ = v_isSharedCheck_2199_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_toGoalState_2190_);
lean_dec(v___x_2189_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2199_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2194_ = l_Lean_Expr_mvarId_x21(v_a_2187_);
lean_dec(v_a_2187_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 1, v___x_2194_);
v___x_2196_ = v___x_2192_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_toGoalState_2190_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2197_; 
v___x_2197_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v___x_2196_, v_generation_2172_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
return v___x_2197_;
}
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_dec(v_a_2187_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec(v_generation_2172_);
v_a_2201_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2188_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2188_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec(v_generation_2172_);
lean_dec(v_mvarId_2170_);
v_a_2209_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2186_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2186_);
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
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec(v_generation_2172_);
lean_dec_ref(v___x_2171_);
lean_dec(v_mvarId_2170_);
v_a_2217_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2184_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2184_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed(lean_object* v_mvarId_2225_, lean_object* v___x_2226_, lean_object* v_generation_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(v_mvarId_2225_, v___x_2226_, v_generation_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
lean_dec(v___y_2228_);
return v_res_2239_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4(void){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2245_ = lean_box(0);
v___x_2246_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3));
v___x_2247_ = l_Lean_mkConst(v___x_2246_, v___x_2245_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(lean_object* v_goal_2248_, lean_object* v_generation_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v___x_2260_; lean_object* v_a_2262_; lean_object* v___y_2267_; lean_object* v___x_2277_; lean_object* v_mvarId_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2575_; 
lean_inc_ref(v_goal_2248_);
v___x_2260_ = lean_st_mk_ref(v_goal_2248_);
v___x_2277_ = lean_st_ref_get(v___x_2260_);
v_mvarId_2278_ = lean_ctor_get(v___x_2277_, 1);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2575_ == 0)
{
lean_object* v_unused_2576_; 
v_unused_2576_ = lean_ctor_get(v___x_2277_, 0);
lean_dec(v_unused_2576_);
v___x_2280_ = v___x_2277_;
v_isShared_2281_ = v_isSharedCheck_2575_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_mvarId_2278_);
lean_dec(v___x_2277_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2575_;
goto v_resetjp_2279_;
}
v___jp_2261_:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2263_ = lean_st_ref_get(v___x_2260_);
lean_dec(v___x_2260_);
v___x_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2264_, 0, v_a_2262_);
lean_ctor_set(v___x_2264_, 1, v___x_2263_);
v___x_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
return v___x_2265_;
}
v___jp_2266_:
{
if (lean_obj_tag(v___y_2267_) == 0)
{
lean_object* v_a_2268_; 
v_a_2268_ = lean_ctor_get(v___y_2267_, 0);
lean_inc(v_a_2268_);
lean_dec_ref(v___y_2267_);
v_a_2262_ = v_a_2268_;
goto v___jp_2261_;
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
lean_dec(v___x_2260_);
v_a_2269_ = lean_ctor_get(v___y_2267_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___y_2267_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___y_2267_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___y_2267_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
v_resetjp_2279_:
{
lean_object* v___x_2282_; 
v___x_2282_ = l_Lean_MVarId_getType(v_mvarId_2278_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; uint8_t v___x_2284_; uint8_t v___x_2285_; lean_object* v___y_2287_; uint8_t v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2304_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref(v___x_2282_);
v___x_2284_ = l_Lean_Expr_isForall(v_a_2283_);
v___x_2285_ = 1;
if (v___x_2284_ == 0)
{
uint8_t v___x_2327_; 
lean_del_object(v___x_2280_);
v___x_2327_ = l_Lean_Expr_isLet(v_a_2283_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; 
lean_dec(v_a_2283_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec(v_generation_2249_);
v___x_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2328_, 0, v_goal_2248_);
v_a_2262_ = v___x_2328_;
goto v___jp_2261_;
}
else
{
lean_object* v___x_2329_; 
lean_dec_ref(v_goal_2248_);
v___x_2329_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_2251_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; uint8_t v_zetaDelta_2331_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref(v___x_2329_);
v_zetaDelta_2331_ = lean_ctor_get_uint8(v_a_2330_, sizeof(void*)*11 + 19);
lean_dec(v_a_2330_);
if (v_zetaDelta_2331_ == 0)
{
lean_object* v___x_2332_; 
lean_dec(v_a_2283_);
lean_inc(v___y_2258_);
lean_inc_ref(v___y_2257_);
lean_inc(v___y_2256_);
lean_inc_ref(v___y_2255_);
v___x_2332_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_2260_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v___x_2334_; lean_object* v_mvarId_2335_; lean_object* v___f_2336_; lean_object* v___x_2337_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref(v___x_2332_);
v___x_2334_ = lean_st_ref_get(v___x_2260_);
v_mvarId_2335_ = lean_ctor_get(v___x_2334_, 1);
lean_inc(v_mvarId_2335_);
lean_dec(v___x_2334_);
v___f_2336_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed), 13, 2);
lean_closure_set(v___f_2336_, 0, v_a_2333_);
lean_closure_set(v___f_2336_, 1, v_generation_2249_);
lean_inc(v___x_2260_);
v___x_2337_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_2335_, v___f_2336_, v___x_2260_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
v___y_2267_ = v___x_2337_;
goto v___jp_2266_;
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec(v___x_2260_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec(v_generation_2249_);
v_a_2338_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2332_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2332_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
else
{
lean_object* v___x_2346_; lean_object* v_mvarId_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___f_2350_; lean_object* v___x_2351_; 
v___x_2346_ = lean_st_ref_get(v___x_2260_);
v_mvarId_2347_ = lean_ctor_get(v___x_2346_, 1);
lean_inc(v_mvarId_2347_);
lean_dec(v___x_2346_);
v___x_2348_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__0));
v___x_2349_ = l_Lean_Meta_expandLet(v_a_2283_, v___x_2348_, v___x_2285_);
lean_dec(v_a_2283_);
lean_inc(v_mvarId_2347_);
v___f_2350_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed), 14, 3);
lean_closure_set(v___f_2350_, 0, v_mvarId_2347_);
lean_closure_set(v___f_2350_, 1, v___x_2349_);
lean_closure_set(v___f_2350_, 2, v_generation_2249_);
lean_inc(v___x_2260_);
v___x_2351_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_2347_, v___f_2350_, v___x_2260_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
v___y_2267_ = v___x_2351_;
goto v___jp_2266_;
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_dec(v_a_2283_);
lean_dec(v___x_2260_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec(v_generation_2249_);
v_a_2352_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2329_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2329_);
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
}
else
{
lean_object* v___x_2360_; lean_object* v___y_2362_; uint8_t v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; uint8_t v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v_localInsts_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___x_2458_; 
lean_dec(v_generation_2249_);
lean_dec_ref(v_goal_2248_);
v___x_2360_ = l_Lean_Expr_bindingDomain_x21(v_a_2283_);
lean_inc(v___y_2258_);
lean_inc_ref(v___y_2257_);
lean_inc(v___y_2256_);
lean_inc_ref(v___y_2255_);
lean_inc_ref(v___x_2360_);
v___x_2458_ = l_Lean_Meta_isProp(v___x_2360_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; uint8_t v___y_2461_; uint8_t v___x_2543_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2459_);
lean_dec_ref(v___x_2458_);
v___x_2543_ = lean_unbox(v_a_2459_);
lean_dec(v_a_2459_);
if (v___x_2543_ == 0)
{
if (v___x_2284_ == 0)
{
lean_del_object(v___x_2280_);
v___y_2461_ = v___x_2284_;
goto v___jp_2460_;
}
else
{
lean_object* v___x_2544_; 
lean_dec_ref(v___x_2360_);
lean_dec(v_a_2283_);
v___x_2544_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_2260_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v___x_2546_; lean_object* v___x_2548_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2545_);
lean_dec_ref(v___x_2544_);
v___x_2546_ = lean_st_ref_get(v___x_2260_);
if (v_isShared_2281_ == 0)
{
lean_ctor_set_tag(v___x_2280_, 3);
lean_ctor_set(v___x_2280_, 1, v___x_2546_);
lean_ctor_set(v___x_2280_, 0, v_a_2545_);
v___x_2548_ = v___x_2280_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2545_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v___x_2546_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
v_a_2262_ = v___x_2548_;
goto v___jp_2261_;
}
}
else
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2557_; 
lean_del_object(v___x_2280_);
lean_dec(v___x_2260_);
v_a_2550_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2552_ = v___x_2544_;
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2544_);
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
}
else
{
uint8_t v___x_2558_; 
lean_del_object(v___x_2280_);
v___x_2558_ = 0;
v___y_2461_ = v___x_2558_;
goto v___jp_2460_;
}
v___jp_2460_:
{
lean_object* v___x_2462_; lean_object* v_mvarId_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2541_; 
v___x_2462_ = lean_st_ref_get(v___x_2260_);
v_mvarId_2463_ = lean_ctor_get(v___x_2462_, 1);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2541_ == 0)
{
lean_object* v_unused_2542_; 
v_unused_2542_ = lean_ctor_get(v___x_2462_, 0);
lean_dec(v_unused_2542_);
v___x_2465_ = v___x_2462_;
v_isShared_2466_ = v_isSharedCheck_2541_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_mvarId_2463_);
lean_dec(v___x_2462_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2541_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2467_; 
lean_inc(v_mvarId_2463_);
v___x_2467_ = l_Lean_MVarId_getTag(v_mvarId_2463_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; lean_object* v___x_2469_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_a_2468_);
lean_dec_ref(v___x_2467_);
v___x_2469_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___x_2260_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v_a_2470_; lean_object* v___x_2471_; 
v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_a_2470_);
lean_dec_ref(v___x_2469_);
lean_inc(v___y_2258_);
lean_inc_ref(v___y_2257_);
lean_inc(v___y_2256_);
lean_inc_ref(v___y_2255_);
lean_inc(v___y_2254_);
lean_inc_ref(v___y_2253_);
lean_inc(v___y_2252_);
lean_inc_ref(v___y_2251_);
lean_inc(v___y_2250_);
lean_inc(v___x_2260_);
lean_inc_ref(v___x_2360_);
v___x_2471_ = l_Lean_Meta_Grind_preprocessHypothesis(v___x_2360_, v___x_2260_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; lean_object* v_lctx_2473_; lean_object* v_expr_2474_; lean_object* v_proof_x3f_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2472_);
lean_dec_ref(v___x_2471_);
v_lctx_2473_ = lean_ctor_get(v___y_2255_, 2);
v_expr_2474_ = lean_ctor_get(v_a_2472_, 0);
lean_inc_ref(v_expr_2474_);
v_proof_x3f_2475_ = lean_ctor_get(v_a_2472_, 1);
lean_inc(v_proof_x3f_2475_);
lean_dec(v_a_2472_);
v___x_2476_ = l_Lean_Expr_bindingName_x21(v_a_2283_);
lean_inc(v___y_2258_);
lean_inc_ref(v___y_2257_);
lean_inc(v___y_2256_);
lean_inc_ref(v___y_2255_);
lean_inc_ref(v_expr_2474_);
lean_inc(v___x_2476_);
v___x_2477_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v___x_2476_, v_expr_2474_, v___x_2260_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; lean_object* v___x_2479_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2478_);
lean_dec_ref(v___x_2477_);
v___x_2479_ = l_Lean_Meta_getLocalInstances___redArg(v___y_2255_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_a_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; uint8_t v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_a_2480_);
lean_dec_ref(v___x_2479_);
lean_inc(v_a_2470_);
v___x_2481_ = l_Lean_mkFVar(v_a_2470_);
v___x_2482_ = l_Lean_Expr_bindingInfo_x21(v_a_2283_);
v___x_2483_ = 0;
lean_inc_ref(v_expr_2474_);
lean_inc(v_a_2470_);
lean_inc_ref(v_lctx_2473_);
v___x_2484_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_2473_, v_a_2470_, v_a_2478_, v_expr_2474_, v___x_2482_, v___x_2483_);
lean_inc(v___y_2258_);
lean_inc_ref(v___y_2257_);
lean_inc(v___y_2256_);
lean_inc_ref(v___y_2255_);
lean_inc_ref(v_expr_2474_);
v___x_2485_ = l_Lean_Meta_isClass_x3f(v_expr_2474_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; lean_object* v___x_2487_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
lean_inc(v_a_2486_);
lean_dec_ref(v___x_2485_);
v___x_2487_ = l_Lean_Expr_bindingBody_x21(v_a_2283_);
if (lean_obj_tag(v_a_2486_) == 1)
{
lean_object* v_val_2488_; lean_object* v___x_2490_; 
v_val_2488_ = lean_ctor_get(v_a_2486_, 0);
lean_inc(v_val_2488_);
lean_dec_ref(v_a_2486_);
lean_inc_ref(v___x_2481_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 1, v___x_2481_);
lean_ctor_set(v___x_2465_, 0, v_val_2488_);
v___x_2490_ = v___x_2465_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_val_2488_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v___x_2481_);
v___x_2490_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
lean_object* v___x_2491_; 
v___x_2491_ = lean_array_push(v_a_2480_, v___x_2490_);
lean_inc(v___x_2260_);
lean_inc_ref(v_expr_2474_);
v___y_2362_ = v_a_2470_;
v___y_2363_ = v___y_2461_;
v___y_2364_ = v___x_2487_;
v___y_2365_ = v_expr_2474_;
v___y_2366_ = v_mvarId_2463_;
v___y_2367_ = v_expr_2474_;
v___y_2368_ = v___x_2482_;
v___y_2369_ = v___x_2481_;
v___y_2370_ = v___x_2484_;
v___y_2371_ = v_a_2468_;
v___y_2372_ = v_proof_x3f_2475_;
v___y_2373_ = v___x_2476_;
v_localInsts_2374_ = v___x_2491_;
v___y_2375_ = v___x_2260_;
v___y_2376_ = v___y_2250_;
v___y_2377_ = v___y_2251_;
v___y_2378_ = v___y_2252_;
v___y_2379_ = v___y_2253_;
v___y_2380_ = v___y_2254_;
v___y_2381_ = v___y_2255_;
v___y_2382_ = v___y_2256_;
v___y_2383_ = v___y_2257_;
v___y_2384_ = v___y_2258_;
goto v___jp_2361_;
}
}
else
{
lean_dec(v_a_2486_);
lean_del_object(v___x_2465_);
lean_inc(v___x_2260_);
lean_inc_ref(v_expr_2474_);
v___y_2362_ = v_a_2470_;
v___y_2363_ = v___y_2461_;
v___y_2364_ = v___x_2487_;
v___y_2365_ = v_expr_2474_;
v___y_2366_ = v_mvarId_2463_;
v___y_2367_ = v_expr_2474_;
v___y_2368_ = v___x_2482_;
v___y_2369_ = v___x_2481_;
v___y_2370_ = v___x_2484_;
v___y_2371_ = v_a_2468_;
v___y_2372_ = v_proof_x3f_2475_;
v___y_2373_ = v___x_2476_;
v_localInsts_2374_ = v_a_2480_;
v___y_2375_ = v___x_2260_;
v___y_2376_ = v___y_2250_;
v___y_2377_ = v___y_2251_;
v___y_2378_ = v___y_2252_;
v___y_2379_ = v___y_2253_;
v___y_2380_ = v___y_2254_;
v___y_2381_ = v___y_2255_;
v___y_2382_ = v___y_2256_;
v___y_2383_ = v___y_2257_;
v___y_2384_ = v___y_2258_;
goto v___jp_2361_;
}
}
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
lean_dec_ref(v___x_2484_);
lean_dec_ref(v___x_2481_);
lean_dec(v_a_2480_);
lean_dec(v___x_2476_);
lean_dec(v_proof_x3f_2475_);
lean_dec_ref(v_expr_2474_);
lean_dec(v_a_2470_);
lean_dec(v_a_2468_);
lean_del_object(v___x_2465_);
lean_dec(v_mvarId_2463_);
lean_dec_ref(v___x_2360_);
lean_dec(v_a_2283_);
lean_dec(v___x_2260_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
v_a_2493_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2485_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2485_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
else
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2508_; 
lean_dec(v_a_2478_);
lean_dec(v___x_2476_);
lean_dec(v_proof_x3f_2475_);
lean_dec_ref(v_expr_2474_);
lean_dec(v_a_2470_);
lean_dec(v_a_2468_);
lean_del_object(v___x_2465_);
lean_dec(v_mvarId_2463_);
lean_dec_ref(v___x_2360_);
lean_dec(v_a_2283_);
lean_dec(v___x_2260_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
v_a_2501_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2479_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2479_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2504_ == 0)
{
v___x_2506_ = v___x_2503_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2501_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
lean_dec(v___x_2476_);
lean_dec(v_proof_x3f_2475_);
lean_dec_ref(v_expr_2474_);
lean_dec(v_a_2470_);
lean_dec(v_a_2468_);
lean_del_object(v___x_2465_);
lean_dec(v_mvarId_2463_);
lean_dec_ref(v___x_2360_);
lean_dec(v_a_2283_);
lean_dec(v___x_2260_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
v_a_2509_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2477_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2477_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2524_; 
lean_dec(v_a_2470_);
lean_dec(v_a_2468_);
lean_del_object(v___x_2465_);
lean_dec(v_mvarId_2463_);
lean_dec_ref(v___x_2360_);
lean_dec(v_a_2283_);
lean_dec(v___x_2260_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
v_a_2517_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2519_ = v___x_2471_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2471_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
if (v_isShared_2520_ == 0)
{
v___x_2522_ = v___x_2519_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_a_2517_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
else
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
lean_dec(v_a_2468_);
lean_del_object(v___x_2465_);
lean_dec(v_mvarId_2463_);
lean_dec_ref(v___x_2360_);
lean_dec(v_a_2283_);
lean_dec(v___x_2260_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
v_a_2525_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2527_ = v___x_2469_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2469_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_del_object(v___x_2465_);
lean_dec(v_mvarId_2463_);
lean_dec_ref(v___x_2360_);
lean_dec(v_a_2283_);
lean_dec(v___x_2260_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
v_a_2533_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2467_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2467_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec_ref(v___x_2360_);
lean_dec(v_a_2283_);
lean_del_object(v___x_2280_);
lean_dec(v___x_2260_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
v_a_2559_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2458_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2458_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
v___jp_2361_:
{
if (lean_obj_tag(v___y_2372_) == 0)
{
uint8_t v___x_2385_; 
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2367_);
lean_dec_ref(v___y_2365_);
lean_dec_ref(v___x_2360_);
v___x_2385_ = l_Lean_Expr_isArrow(v_a_2283_);
lean_dec(v_a_2283_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; 
v___x_2386_ = lean_expr_instantiate1(v___y_2364_, v___y_2369_);
lean_dec_ref(v___y_2364_);
v___y_2287_ = v___y_2362_;
v___y_2288_ = v___y_2363_;
v___y_2289_ = v___y_2366_;
v___y_2290_ = v___y_2383_;
v___y_2291_ = v___y_2371_;
v___y_2292_ = v___y_2379_;
v___y_2293_ = v___y_2376_;
v___y_2294_ = v___y_2381_;
v___y_2295_ = v_localInsts_2374_;
v___y_2296_ = v___y_2382_;
v___y_2297_ = v___y_2377_;
v___y_2298_ = v___y_2384_;
v___y_2299_ = v___y_2370_;
v___y_2300_ = v___y_2369_;
v___y_2301_ = v___y_2378_;
v___y_2302_ = v___y_2375_;
v___y_2303_ = v___y_2380_;
v___y_2304_ = v___x_2386_;
goto v___jp_2286_;
}
else
{
v___y_2287_ = v___y_2362_;
v___y_2288_ = v___y_2363_;
v___y_2289_ = v___y_2366_;
v___y_2290_ = v___y_2383_;
v___y_2291_ = v___y_2371_;
v___y_2292_ = v___y_2379_;
v___y_2293_ = v___y_2376_;
v___y_2294_ = v___y_2381_;
v___y_2295_ = v_localInsts_2374_;
v___y_2296_ = v___y_2382_;
v___y_2297_ = v___y_2377_;
v___y_2298_ = v___y_2384_;
v___y_2299_ = v___y_2370_;
v___y_2300_ = v___y_2369_;
v___y_2301_ = v___y_2378_;
v___y_2302_ = v___y_2375_;
v___y_2303_ = v___y_2380_;
v___y_2304_ = v___y_2364_;
goto v___jp_2286_;
}
}
else
{
lean_object* v_val_2387_; uint8_t v___x_2388_; 
v_val_2387_ = lean_ctor_get(v___y_2372_, 0);
lean_inc(v_val_2387_);
lean_dec_ref(v___y_2372_);
v___x_2388_ = l_Lean_Expr_isArrow(v_a_2283_);
lean_dec(v_a_2283_);
if (v___x_2388_ == 0)
{
lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
lean_inc_ref(v___y_2364_);
lean_inc_ref(v___x_2360_);
v___x_2389_ = l_Lean_mkLambda(v___y_2373_, v___y_2368_, v___x_2360_, v___y_2364_);
v___x_2390_ = lean_box(0);
v___x_2391_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4);
lean_inc_ref(v___y_2369_);
lean_inc(v_val_2387_);
lean_inc_ref(v___x_2360_);
v___x_2392_ = l_Lean_mkApp4(v___x_2391_, v___x_2360_, v___y_2367_, v_val_2387_, v___y_2369_);
v___x_2393_ = lean_expr_instantiate1(v___y_2364_, v___x_2392_);
lean_dec_ref(v___x_2392_);
lean_dec_ref(v___y_2364_);
lean_inc(v___y_2384_);
lean_inc_ref(v___y_2383_);
lean_inc(v___y_2382_);
lean_inc_ref(v___y_2381_);
lean_inc_ref(v___x_2393_);
v___x_2394_ = l_Lean_Meta_getLevel(v___x_2393_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; uint8_t v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
lean_dec_ref(v___x_2394_);
v___x_2396_ = 2;
v___x_2397_ = lean_unsigned_to_nat(0u);
v___x_2398_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_2370_, v_localInsts_2374_, v___x_2393_, v___x_2396_, v___y_2371_, v___x_2397_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; uint8_t v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___f_2408_; lean_object* v___x_2409_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_a_2399_);
lean_dec_ref(v___x_2398_);
v___x_2400_ = l_Lean_Expr_mvarId_x21(v_a_2399_);
v___x_2401_ = lean_unsigned_to_nat(1u);
v___x_2402_ = lean_mk_empty_array_with_capacity(v___x_2401_);
v___x_2403_ = lean_array_push(v___x_2402_, v___y_2369_);
v___x_2404_ = 1;
v___x_2405_ = lean_box(v___x_2388_);
v___x_2406_ = lean_box(v___x_2285_);
v___x_2407_ = lean_box(v___x_2404_);
lean_inc(v___x_2400_);
v___f_2408_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed), 25, 14);
lean_closure_set(v___f_2408_, 0, v___x_2403_);
lean_closure_set(v___f_2408_, 1, v_a_2399_);
lean_closure_set(v___f_2408_, 2, v___x_2405_);
lean_closure_set(v___f_2408_, 3, v___x_2406_);
lean_closure_set(v___f_2408_, 4, v___x_2407_);
lean_closure_set(v___f_2408_, 5, v_a_2395_);
lean_closure_set(v___f_2408_, 6, v___x_2390_);
lean_closure_set(v___f_2408_, 7, v___x_2360_);
lean_closure_set(v___f_2408_, 8, v___y_2365_);
lean_closure_set(v___f_2408_, 9, v___x_2389_);
lean_closure_set(v___f_2408_, 10, v_val_2387_);
lean_closure_set(v___f_2408_, 11, v___y_2366_);
lean_closure_set(v___f_2408_, 12, v___x_2400_);
lean_closure_set(v___f_2408_, 13, v___y_2362_);
v___x_2409_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2400_, v___f_2408_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
v___y_2267_ = v___x_2409_;
goto v___jp_2266_;
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
lean_dec(v_a_2395_);
lean_dec_ref(v___x_2389_);
lean_dec(v_val_2387_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2362_);
lean_dec_ref(v___x_2360_);
lean_dec(v___x_2260_);
v_a_2410_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2398_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2398_);
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
}
else
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2425_; 
lean_dec_ref(v___x_2393_);
lean_dec_ref(v___x_2389_);
lean_dec(v_val_2387_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v_localInsts_2374_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2362_);
lean_dec_ref(v___x_2360_);
lean_dec(v___x_2260_);
v_a_2418_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2420_ = v___x_2394_;
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2394_);
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
else
{
lean_object* v___x_2426_; 
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2367_);
lean_inc(v___y_2384_);
lean_inc_ref(v___y_2383_);
lean_inc(v___y_2382_);
lean_inc_ref(v___y_2381_);
lean_inc_ref(v___y_2364_);
v___x_2426_ = l_Lean_Meta_getLevel(v___y_2364_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v_a_2427_; uint8_t v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
lean_inc(v_a_2427_);
lean_dec_ref(v___x_2426_);
v___x_2428_ = 2;
v___x_2429_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___y_2364_);
v___x_2430_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_2370_, v_localInsts_2374_, v___y_2364_, v___x_2428_, v___y_2371_, v___x_2429_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; uint8_t v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___f_2440_; lean_object* v___x_2441_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_a_2431_);
lean_dec_ref(v___x_2430_);
v___x_2432_ = l_Lean_Expr_mvarId_x21(v_a_2431_);
v___x_2433_ = lean_unsigned_to_nat(1u);
v___x_2434_ = lean_mk_empty_array_with_capacity(v___x_2433_);
v___x_2435_ = lean_array_push(v___x_2434_, v___y_2369_);
v___x_2436_ = 1;
v___x_2437_ = lean_box(v___y_2363_);
v___x_2438_ = lean_box(v___x_2285_);
v___x_2439_ = lean_box(v___x_2436_);
lean_inc(v___x_2432_);
v___f_2440_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed), 24, 13);
lean_closure_set(v___f_2440_, 0, v___x_2435_);
lean_closure_set(v___f_2440_, 1, v_a_2431_);
lean_closure_set(v___f_2440_, 2, v___x_2437_);
lean_closure_set(v___f_2440_, 3, v___x_2438_);
lean_closure_set(v___f_2440_, 4, v___x_2439_);
lean_closure_set(v___f_2440_, 5, v_a_2427_);
lean_closure_set(v___f_2440_, 6, v___x_2360_);
lean_closure_set(v___f_2440_, 7, v___y_2365_);
lean_closure_set(v___f_2440_, 8, v___y_2364_);
lean_closure_set(v___f_2440_, 9, v_val_2387_);
lean_closure_set(v___f_2440_, 10, v___y_2366_);
lean_closure_set(v___f_2440_, 11, v___x_2432_);
lean_closure_set(v___f_2440_, 12, v___y_2362_);
v___x_2441_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2432_, v___f_2440_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
v___y_2267_ = v___x_2441_;
goto v___jp_2266_;
}
else
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2449_; 
lean_dec(v_a_2427_);
lean_dec(v_val_2387_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2362_);
lean_dec_ref(v___x_2360_);
lean_dec(v___x_2260_);
v_a_2442_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2444_ = v___x_2430_;
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2430_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2447_; 
if (v_isShared_2445_ == 0)
{
v___x_2447_ = v___x_2444_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_a_2442_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
lean_dec(v_val_2387_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v_localInsts_2374_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2362_);
lean_dec_ref(v___x_2360_);
lean_dec(v___x_2260_);
v_a_2450_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2426_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2426_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
}
}
}
v___jp_2286_:
{
uint8_t v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = 2;
v___x_2306_ = lean_unsigned_to_nat(0u);
v___x_2307_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_2299_, v___y_2295_, v___y_2304_, v___x_2305_, v___y_2291_, v___x_2306_, v___y_2294_, v___y_2296_, v___y_2290_, v___y_2298_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; uint8_t v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___f_2317_; lean_object* v___x_2318_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2308_);
lean_dec_ref(v___x_2307_);
v___x_2309_ = l_Lean_Expr_mvarId_x21(v_a_2308_);
v___x_2310_ = lean_unsigned_to_nat(1u);
v___x_2311_ = lean_mk_empty_array_with_capacity(v___x_2310_);
v___x_2312_ = lean_array_push(v___x_2311_, v___y_2300_);
v___x_2313_ = 1;
v___x_2314_ = lean_box(v___y_2288_);
v___x_2315_ = lean_box(v___x_2285_);
v___x_2316_ = lean_box(v___x_2313_);
lean_inc(v___x_2309_);
v___f_2317_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed), 19, 8);
lean_closure_set(v___f_2317_, 0, v___x_2312_);
lean_closure_set(v___f_2317_, 1, v_a_2308_);
lean_closure_set(v___f_2317_, 2, v___x_2314_);
lean_closure_set(v___f_2317_, 3, v___x_2315_);
lean_closure_set(v___f_2317_, 4, v___x_2316_);
lean_closure_set(v___f_2317_, 5, v___y_2289_);
lean_closure_set(v___f_2317_, 6, v___x_2309_);
lean_closure_set(v___f_2317_, 7, v___y_2287_);
v___x_2318_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2309_, v___f_2317_, v___y_2302_, v___y_2293_, v___y_2297_, v___y_2301_, v___y_2292_, v___y_2303_, v___y_2294_, v___y_2296_, v___y_2290_, v___y_2298_);
v___y_2267_ = v___x_2318_;
goto v___jp_2266_;
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec(v___y_2287_);
lean_dec(v___x_2260_);
v_a_2319_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2307_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2307_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
lean_del_object(v___x_2280_);
lean_dec(v___x_2260_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec(v_generation_2249_);
lean_dec_ref(v_goal_2248_);
v_a_2567_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2282_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2282_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed(lean_object* v_goal_2577_, lean_object* v_generation_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(v_goal_2577_, v_generation_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(lean_object* v_goal_2590_, lean_object* v_generation_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_){
_start:
{
lean_object* v_mvarId_2602_; lean_object* v___f_2603_; lean_object* v___x_2604_; 
v_mvarId_2602_ = lean_ctor_get(v_goal_2590_, 1);
lean_inc(v_mvarId_2602_);
v___f_2603_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed), 12, 2);
lean_closure_set(v___f_2603_, 0, v_goal_2590_);
lean_closure_set(v___f_2603_, 1, v_generation_2591_);
v___x_2604_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_2602_, v___f_2603_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2613_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2607_ = v___x_2604_;
v_isShared_2608_ = v_isSharedCheck_2613_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2604_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2613_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v_fst_2609_; lean_object* v___x_2611_; 
v_fst_2609_ = lean_ctor_get(v_a_2605_, 0);
lean_inc(v_fst_2609_);
lean_dec(v_a_2605_);
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 0, v_fst_2609_);
v___x_2611_ = v___x_2607_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_fst_2609_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
v_a_2614_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2604_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2604_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___boxed(lean_object* v_goal_2622_, lean_object* v_generation_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_2622_, v_generation_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(lean_object* v_mvarId_2635_, lean_object* v_val_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2635_, v_val_2636_, v___y_2644_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___boxed(lean_object* v_mvarId_2649_, lean_object* v_val_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(v_mvarId_2649_, v_val_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec(v___y_2651_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v___x_2674_; 
v___x_2674_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_2672_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___boxed(lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec(v___y_2675_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1(lean_object* v_00_u03b2_2687_, lean_object* v_x_2688_, lean_object* v_x_2689_, lean_object* v_x_2690_){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_x_2688_, v_x_2689_, v_x_2690_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2692_, lean_object* v_x_2693_, size_t v_x_2694_, size_t v_x_2695_, lean_object* v_x_2696_, lean_object* v_x_2697_){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_2693_, v_x_2694_, v_x_2695_, v_x_2696_, v_x_2697_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2699_, lean_object* v_x_2700_, lean_object* v_x_2701_, lean_object* v_x_2702_, lean_object* v_x_2703_, lean_object* v_x_2704_){
_start:
{
size_t v_x_198544__boxed_2705_; size_t v_x_198545__boxed_2706_; lean_object* v_res_2707_; 
v_x_198544__boxed_2705_ = lean_unbox_usize(v_x_2701_);
lean_dec(v_x_2701_);
v_x_198545__boxed_2706_ = lean_unbox_usize(v_x_2702_);
lean_dec(v_x_2702_);
v_res_2707_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(v_00_u03b2_2699_, v_x_2700_, v_x_198544__boxed_2705_, v_x_198545__boxed_2706_, v_x_2703_, v_x_2704_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_2708_, lean_object* v_n_2709_, lean_object* v_k_2710_, lean_object* v_v_2711_){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(v_n_2709_, v_k_2710_, v_v_2711_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2713_, size_t v_depth_2714_, lean_object* v_keys_2715_, lean_object* v_vals_2716_, lean_object* v_heq_2717_, lean_object* v_i_2718_, lean_object* v_entries_2719_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_2714_, v_keys_2715_, v_vals_2716_, v_i_2718_, v_entries_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2721_, lean_object* v_depth_2722_, lean_object* v_keys_2723_, lean_object* v_vals_2724_, lean_object* v_heq_2725_, lean_object* v_i_2726_, lean_object* v_entries_2727_){
_start:
{
size_t v_depth_boxed_2728_; lean_object* v_res_2729_; 
v_depth_boxed_2728_ = lean_unbox_usize(v_depth_2722_);
lean_dec(v_depth_2722_);
v_res_2729_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(v_00_u03b2_2721_, v_depth_boxed_2728_, v_keys_2723_, v_vals_2724_, v_heq_2725_, v_i_2726_, v_entries_2727_);
lean_dec_ref(v_vals_2724_);
lean_dec_ref(v_keys_2723_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_2730_, lean_object* v_x_2731_, lean_object* v_x_2732_, lean_object* v_x_2733_, lean_object* v_x_2734_){
_start:
{
lean_object* v___x_2735_; 
v___x_2735_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_x_2731_, v_x_2732_, v_x_2733_, v_x_2734_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(lean_object* v_type_2736_, lean_object* v_a_2737_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_Lean_Expr_getAppFn(v_type_2736_);
if (lean_obj_tag(v___x_2739_) == 4)
{
lean_object* v_declName_2740_; lean_object* v___x_2741_; 
v_declName_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc(v_declName_2740_);
lean_dec_ref(v___x_2739_);
v___x_2741_ = l_Lean_Meta_Grind_isEagerSplit___redArg(v_declName_2740_, v_a_2737_);
lean_dec(v_declName_2740_);
return v___x_2741_;
}
else
{
uint8_t v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
lean_dec_ref(v___x_2739_);
v___x_2742_ = 0;
v___x_2743_ = lean_box(v___x_2742_);
v___x_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
return v___x_2744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg___boxed(lean_object* v_type_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_2745_, v_a_2746_);
lean_dec_ref(v_a_2746_);
lean_dec_ref(v_type_2745_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(lean_object* v_type_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_2749_, v_a_2751_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___boxed(lean_object* v_type_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(v_type_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
lean_dec(v_a_2770_);
lean_dec_ref(v_a_2769_);
lean_dec(v_a_2768_);
lean_dec_ref(v_a_2767_);
lean_dec(v_a_2766_);
lean_dec_ref(v_a_2765_);
lean_dec(v_a_2764_);
lean_dec_ref(v_a_2763_);
lean_dec(v_a_2762_);
lean_dec_ref(v_type_2761_);
return v_res_2772_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2773_; 
v___x_2773_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2773_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2774_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
return v___x_2775_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2776_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_2777_ = lean_unsigned_to_nat(0u);
v___x_2778_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2777_);
lean_ctor_set(v___x_2778_, 1, v___x_2777_);
lean_ctor_set(v___x_2778_, 2, v___x_2777_);
lean_ctor_set(v___x_2778_, 3, v___x_2776_);
lean_ctor_set(v___x_2778_, 4, v___x_2776_);
lean_ctor_set(v___x_2778_, 5, v___x_2776_);
lean_ctor_set(v___x_2778_, 6, v___x_2776_);
lean_ctor_set(v___x_2778_, 7, v___x_2776_);
lean_ctor_set(v___x_2778_, 8, v___x_2776_);
return v___x_2778_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2779_ = lean_unsigned_to_nat(32u);
v___x_2780_ = lean_mk_empty_array_with_capacity(v___x_2779_);
v___x_2781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2780_);
return v___x_2781_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2782_ = ((size_t)5ULL);
v___x_2783_ = lean_unsigned_to_nat(0u);
v___x_2784_ = lean_unsigned_to_nat(32u);
v___x_2785_ = lean_mk_empty_array_with_capacity(v___x_2784_);
v___x_2786_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_2787_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
lean_ctor_set(v___x_2787_, 1, v___x_2785_);
lean_ctor_set(v___x_2787_, 2, v___x_2783_);
lean_ctor_set(v___x_2787_, 3, v___x_2783_);
lean_ctor_set_usize(v___x_2787_, 4, v___x_2782_);
return v___x_2787_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2788_ = lean_box(1);
v___x_2789_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_2790_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_2791_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2790_);
lean_ctor_set(v___x_2791_, 1, v___x_2789_);
lean_ctor_set(v___x_2791_, 2, v___x_2788_);
return v___x_2791_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_2794_ = l_Lean_stringToMessageData(v___x_2793_);
return v___x_2794_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2796_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_2797_ = l_Lean_stringToMessageData(v___x_2796_);
return v___x_2797_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_2800_ = l_Lean_stringToMessageData(v___x_2799_);
return v___x_2800_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2802_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_2803_ = l_Lean_stringToMessageData(v___x_2802_);
return v___x_2803_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2805_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_2806_ = l_Lean_stringToMessageData(v___x_2805_);
return v___x_2806_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2808_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_2809_ = l_Lean_stringToMessageData(v___x_2808_);
return v___x_2809_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_2812_ = l_Lean_stringToMessageData(v___x_2811_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_2813_, lean_object* v_declHint_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v___x_2817_; lean_object* v_env_2818_; uint8_t v___x_2819_; 
v___x_2817_ = lean_st_ref_get(v___y_2815_);
v_env_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc_ref(v_env_2818_);
lean_dec(v___x_2817_);
v___x_2819_ = l_Lean_Name_isAnonymous(v_declHint_2814_);
if (v___x_2819_ == 0)
{
uint8_t v_isExporting_2820_; 
v_isExporting_2820_ = lean_ctor_get_uint8(v_env_2818_, sizeof(void*)*8);
if (v_isExporting_2820_ == 0)
{
lean_object* v___x_2821_; 
lean_dec_ref(v_env_2818_);
lean_dec(v_declHint_2814_);
v___x_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2821_, 0, v_msg_2813_);
return v___x_2821_;
}
else
{
lean_object* v___x_2822_; uint8_t v___x_2823_; 
lean_inc_ref(v_env_2818_);
v___x_2822_ = l_Lean_Environment_setExporting(v_env_2818_, v___x_2819_);
lean_inc(v_declHint_2814_);
lean_inc_ref(v___x_2822_);
v___x_2823_ = l_Lean_Environment_contains(v___x_2822_, v_declHint_2814_, v_isExporting_2820_);
if (v___x_2823_ == 0)
{
lean_object* v___x_2824_; 
lean_dec_ref(v___x_2822_);
lean_dec_ref(v_env_2818_);
lean_dec(v_declHint_2814_);
v___x_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2824_, 0, v_msg_2813_);
return v___x_2824_;
}
else
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v_c_2830_; lean_object* v___x_2831_; 
v___x_2825_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_2826_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_2827_ = l_Lean_Options_empty;
v___x_2828_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2822_);
lean_ctor_set(v___x_2828_, 1, v___x_2825_);
lean_ctor_set(v___x_2828_, 2, v___x_2826_);
lean_ctor_set(v___x_2828_, 3, v___x_2827_);
lean_inc(v_declHint_2814_);
v___x_2829_ = l_Lean_MessageData_ofConstName(v_declHint_2814_, v___x_2819_);
v_c_2830_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2830_, 0, v___x_2828_);
lean_ctor_set(v_c_2830_, 1, v___x_2829_);
v___x_2831_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2818_, v_declHint_2814_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
lean_dec_ref(v_env_2818_);
lean_dec(v_declHint_2814_);
v___x_2832_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_2833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
lean_ctor_set(v___x_2833_, 1, v_c_2830_);
v___x_2834_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_2835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2833_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
v___x_2836_ = l_Lean_MessageData_note(v___x_2835_);
v___x_2837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2837_, 0, v_msg_2813_);
lean_ctor_set(v___x_2837_, 1, v___x_2836_);
v___x_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2837_);
return v___x_2838_;
}
else
{
lean_object* v_val_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2874_; 
v_val_2839_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2841_ = v___x_2831_;
v_isShared_2842_ = v_isSharedCheck_2874_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_val_2839_);
lean_dec(v___x_2831_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2874_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v_mod_2846_; uint8_t v___x_2847_; 
v___x_2843_ = lean_box(0);
v___x_2844_ = l_Lean_Environment_header(v_env_2818_);
lean_dec_ref(v_env_2818_);
v___x_2845_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2844_);
v_mod_2846_ = lean_array_get(v___x_2843_, v___x_2845_, v_val_2839_);
lean_dec(v_val_2839_);
lean_dec_ref(v___x_2845_);
v___x_2847_ = l_Lean_isPrivateName(v_declHint_2814_);
lean_dec(v_declHint_2814_);
if (v___x_2847_ == 0)
{
lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2859_; 
v___x_2848_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_2849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
lean_ctor_set(v___x_2849_, 1, v_c_2830_);
v___x_2850_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_2851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2849_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
v___x_2852_ = l_Lean_MessageData_ofName(v_mod_2846_);
v___x_2853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2851_);
lean_ctor_set(v___x_2853_, 1, v___x_2852_);
v___x_2854_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_2855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2853_);
lean_ctor_set(v___x_2855_, 1, v___x_2854_);
v___x_2856_ = l_Lean_MessageData_note(v___x_2855_);
v___x_2857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2857_, 0, v_msg_2813_);
lean_ctor_set(v___x_2857_, 1, v___x_2856_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set_tag(v___x_2841_, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2857_);
v___x_2859_ = v___x_2841_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2857_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
else
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2872_; 
v___x_2861_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_2862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2861_);
lean_ctor_set(v___x_2862_, 1, v_c_2830_);
v___x_2863_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_2864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2862_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
v___x_2865_ = l_Lean_MessageData_ofName(v_mod_2846_);
v___x_2866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2864_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
v___x_2867_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_2868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2866_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
v___x_2869_ = l_Lean_MessageData_note(v___x_2868_);
v___x_2870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2870_, 0, v_msg_2813_);
lean_ctor_set(v___x_2870_, 1, v___x_2869_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set_tag(v___x_2841_, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2870_);
v___x_2872_ = v___x_2841_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v___x_2870_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2875_; 
lean_dec_ref(v_env_2818_);
lean_dec(v_declHint_2814_);
v___x_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2875_, 0, v_msg_2813_);
return v___x_2875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_2876_, lean_object* v_declHint_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2876_, v_declHint_2877_, v___y_2878_);
lean_dec(v___y_2878_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_2881_, lean_object* v_declHint_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v___x_2886_; lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2896_; 
v___x_2886_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2881_, v_declHint_2882_, v___y_2884_);
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2889_ = v___x_2886_;
v_isShared_2890_ = v_isSharedCheck_2896_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2886_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2896_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2894_; 
v___x_2891_ = l_Lean_unknownIdentifierMessageTag;
v___x_2892_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
lean_ctor_set(v___x_2892_, 1, v_a_2887_);
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 0, v___x_2892_);
v___x_2894_ = v___x_2889_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2892_);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_2897_, lean_object* v_declHint_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2897_, v_declHint_2898_, v___y_2899_, v___y_2900_);
lean_dec(v___y_2900_);
lean_dec_ref(v___y_2899_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msgData_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_){
_start:
{
lean_object* v___x_2907_; lean_object* v_env_2908_; lean_object* v_options_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2907_ = lean_st_ref_get(v___y_2905_);
v_env_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc_ref(v_env_2908_);
lean_dec(v___x_2907_);
v_options_2909_ = lean_ctor_get(v___y_2904_, 2);
v___x_2910_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_2911_ = lean_unsigned_to_nat(32u);
v___x_2912_ = lean_mk_empty_array_with_capacity(v___x_2911_);
lean_dec_ref(v___x_2912_);
v___x_2913_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
lean_inc_ref(v_options_2909_);
v___x_2914_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2914_, 0, v_env_2908_);
lean_ctor_set(v___x_2914_, 1, v___x_2910_);
lean_ctor_set(v___x_2914_, 2, v___x_2913_);
lean_ctor_set(v___x_2914_, 3, v_options_2909_);
v___x_2915_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2914_);
lean_ctor_set(v___x_2915_, 1, v_msgData_2903_);
v___x_2916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msgData_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_2917_, v___y_2918_, v___y_2919_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_msg_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v_ref_2926_; lean_object* v___x_2927_; lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2936_; 
v_ref_2926_ = lean_ctor_get(v___y_2923_, 5);
v___x_2927_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_2922_, v___y_2923_, v___y_2924_);
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2930_ = v___x_2927_;
v_isShared_2931_ = v_isSharedCheck_2936_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2927_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2936_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2932_; lean_object* v___x_2934_; 
lean_inc(v_ref_2926_);
v___x_2932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2932_, 0, v_ref_2926_);
lean_ctor_set(v___x_2932_, 1, v_a_2928_);
if (v_isShared_2931_ == 0)
{
lean_ctor_set_tag(v___x_2930_, 1);
lean_ctor_set(v___x_2930_, 0, v___x_2932_);
v___x_2934_ = v___x_2930_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2932_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_msg_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2937_, v___y_2938_, v___y_2939_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_2942_, lean_object* v_msg_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v_fileName_2947_; lean_object* v_fileMap_2948_; lean_object* v_options_2949_; lean_object* v_currRecDepth_2950_; lean_object* v_maxRecDepth_2951_; lean_object* v_ref_2952_; lean_object* v_currNamespace_2953_; lean_object* v_openDecls_2954_; lean_object* v_initHeartbeats_2955_; lean_object* v_maxHeartbeats_2956_; lean_object* v_quotContext_2957_; lean_object* v_currMacroScope_2958_; uint8_t v_diag_2959_; lean_object* v_cancelTk_x3f_2960_; uint8_t v_suppressElabErrors_2961_; lean_object* v_inheritedTraceOptions_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2971_; 
v_fileName_2947_ = lean_ctor_get(v___y_2944_, 0);
v_fileMap_2948_ = lean_ctor_get(v___y_2944_, 1);
v_options_2949_ = lean_ctor_get(v___y_2944_, 2);
v_currRecDepth_2950_ = lean_ctor_get(v___y_2944_, 3);
v_maxRecDepth_2951_ = lean_ctor_get(v___y_2944_, 4);
v_ref_2952_ = lean_ctor_get(v___y_2944_, 5);
v_currNamespace_2953_ = lean_ctor_get(v___y_2944_, 6);
v_openDecls_2954_ = lean_ctor_get(v___y_2944_, 7);
v_initHeartbeats_2955_ = lean_ctor_get(v___y_2944_, 8);
v_maxHeartbeats_2956_ = lean_ctor_get(v___y_2944_, 9);
v_quotContext_2957_ = lean_ctor_get(v___y_2944_, 10);
v_currMacroScope_2958_ = lean_ctor_get(v___y_2944_, 11);
v_diag_2959_ = lean_ctor_get_uint8(v___y_2944_, sizeof(void*)*14);
v_cancelTk_x3f_2960_ = lean_ctor_get(v___y_2944_, 12);
v_suppressElabErrors_2961_ = lean_ctor_get_uint8(v___y_2944_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2962_ = lean_ctor_get(v___y_2944_, 13);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___y_2944_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2964_ = v___y_2944_;
v_isShared_2965_ = v_isSharedCheck_2971_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_inheritedTraceOptions_2962_);
lean_inc(v_cancelTk_x3f_2960_);
lean_inc(v_currMacroScope_2958_);
lean_inc(v_quotContext_2957_);
lean_inc(v_maxHeartbeats_2956_);
lean_inc(v_initHeartbeats_2955_);
lean_inc(v_openDecls_2954_);
lean_inc(v_currNamespace_2953_);
lean_inc(v_ref_2952_);
lean_inc(v_maxRecDepth_2951_);
lean_inc(v_currRecDepth_2950_);
lean_inc(v_options_2949_);
lean_inc(v_fileMap_2948_);
lean_inc(v_fileName_2947_);
lean_dec(v___y_2944_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2971_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v_ref_2966_; lean_object* v___x_2968_; 
v_ref_2966_ = l_Lean_replaceRef(v_ref_2942_, v_ref_2952_);
lean_dec(v_ref_2952_);
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 5, v_ref_2966_);
v___x_2968_ = v___x_2964_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_fileName_2947_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v_fileMap_2948_);
lean_ctor_set(v_reuseFailAlloc_2970_, 2, v_options_2949_);
lean_ctor_set(v_reuseFailAlloc_2970_, 3, v_currRecDepth_2950_);
lean_ctor_set(v_reuseFailAlloc_2970_, 4, v_maxRecDepth_2951_);
lean_ctor_set(v_reuseFailAlloc_2970_, 5, v_ref_2966_);
lean_ctor_set(v_reuseFailAlloc_2970_, 6, v_currNamespace_2953_);
lean_ctor_set(v_reuseFailAlloc_2970_, 7, v_openDecls_2954_);
lean_ctor_set(v_reuseFailAlloc_2970_, 8, v_initHeartbeats_2955_);
lean_ctor_set(v_reuseFailAlloc_2970_, 9, v_maxHeartbeats_2956_);
lean_ctor_set(v_reuseFailAlloc_2970_, 10, v_quotContext_2957_);
lean_ctor_set(v_reuseFailAlloc_2970_, 11, v_currMacroScope_2958_);
lean_ctor_set(v_reuseFailAlloc_2970_, 12, v_cancelTk_x3f_2960_);
lean_ctor_set(v_reuseFailAlloc_2970_, 13, v_inheritedTraceOptions_2962_);
lean_ctor_set_uint8(v_reuseFailAlloc_2970_, sizeof(void*)*14, v_diag_2959_);
lean_ctor_set_uint8(v_reuseFailAlloc_2970_, sizeof(void*)*14 + 1, v_suppressElabErrors_2961_);
v___x_2968_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
lean_object* v___x_2969_; 
v___x_2969_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2943_, v___x_2968_, v___y_2945_);
lean_dec_ref(v___x_2968_);
return v___x_2969_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_2972_, lean_object* v_msg_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2972_, v_msg_2973_, v___y_2974_, v___y_2975_);
lean_dec(v___y_2975_);
lean_dec(v_ref_2972_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_2978_, lean_object* v_msg_2979_, lean_object* v_declHint_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_){
_start:
{
lean_object* v___x_2984_; lean_object* v_a_2985_; lean_object* v___x_2986_; 
v___x_2984_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2979_, v_declHint_2980_, v___y_2981_, v___y_2982_);
v_a_2985_ = lean_ctor_get(v___x_2984_, 0);
lean_inc(v_a_2985_);
lean_dec_ref(v___x_2984_);
v___x_2986_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2978_, v_a_2985_, v___y_2981_, v___y_2982_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_2987_, lean_object* v_msg_2988_, lean_object* v_declHint_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2987_, v_msg_2988_, v_declHint_2989_, v___y_2990_, v___y_2991_);
lean_dec(v___y_2991_);
lean_dec(v_ref_2987_);
return v_res_2993_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2995_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2996_ = l_Lean_stringToMessageData(v___x_2995_);
return v___x_2996_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2998_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_2999_ = l_Lean_stringToMessageData(v___x_2998_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3000_, lean_object* v_constName_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
lean_object* v___x_3005_; uint8_t v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3005_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_3006_ = 0;
lean_inc(v_constName_3001_);
v___x_3007_ = l_Lean_MessageData_ofConstName(v_constName_3001_, v___x_3006_);
v___x_3008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3005_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
v___x_3009_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_3010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3008_);
lean_ctor_set(v___x_3010_, 1, v___x_3009_);
v___x_3011_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3000_, v___x_3010_, v_constName_3001_, v___y_3002_, v___y_3003_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3012_, lean_object* v_constName_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_3012_, v_constName_3013_, v___y_3014_, v___y_3015_);
lean_dec(v___y_3015_);
lean_dec(v_ref_3012_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(lean_object* v_constName_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v_ref_3022_; lean_object* v___x_3023_; 
v_ref_3022_ = lean_ctor_get(v___y_3019_, 5);
lean_inc(v_ref_3022_);
v___x_3023_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_3022_, v_constName_3018_, v___y_3019_, v___y_3020_);
lean_dec(v_ref_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_3024_, v___y_3025_, v___y_3026_);
lean_dec(v___y_3026_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(lean_object* v_constName_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v___x_3033_; lean_object* v_env_3034_; uint8_t v___x_3035_; lean_object* v___x_3036_; 
v___x_3033_ = lean_st_ref_get(v___y_3031_);
v_env_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc_ref(v_env_3034_);
lean_dec(v___x_3033_);
v___x_3035_ = 0;
lean_inc(v_constName_3029_);
v___x_3036_ = l_Lean_Environment_find_x3f(v_env_3034_, v_constName_3029_, v___x_3035_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v___x_3037_; 
v___x_3037_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_3029_, v___y_3030_, v___y_3031_);
return v___x_3037_;
}
else
{
lean_object* v_val_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec_ref(v___y_3030_);
lean_dec(v_constName_3029_);
v_val_3038_ = lean_ctor_get(v___x_3036_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3036_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_val_3038_);
lean_dec(v___x_3036_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
lean_ctor_set_tag(v___x_3040_, 0);
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_val_3038_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0___boxed(lean_object* v_constName_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_constName_3046_, v___y_3047_, v___y_3048_);
lean_dec(v___y_3048_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(lean_object* v_type_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v___x_3055_; 
v___x_3055_ = l_Lean_Expr_getAppFn(v_type_3051_);
if (lean_obj_tag(v___x_3055_) == 4)
{
lean_object* v_declName_3056_; lean_object* v___x_3057_; 
v_declName_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc(v_declName_3056_);
lean_dec_ref(v___x_3055_);
v___x_3057_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_declName_3056_, v_a_3052_, v_a_3053_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3075_; 
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3060_ = v___x_3057_;
v_isShared_3061_ = v_isSharedCheck_3075_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3057_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3075_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
if (lean_obj_tag(v_a_3058_) == 5)
{
lean_object* v_val_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; uint8_t v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3068_; 
v_val_3062_ = lean_ctor_get(v_a_3058_, 0);
lean_inc_ref(v_val_3062_);
lean_dec_ref(v_a_3058_);
v___x_3063_ = l_Lean_InductiveVal_numCtors(v_val_3062_);
lean_dec_ref(v_val_3062_);
v___x_3064_ = lean_unsigned_to_nat(1u);
v___x_3065_ = lean_nat_dec_le(v___x_3063_, v___x_3064_);
lean_dec(v___x_3063_);
v___x_3066_ = lean_box(v___x_3065_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 0, v___x_3066_);
v___x_3068_ = v___x_3060_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v___x_3066_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
else
{
uint8_t v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3073_; 
lean_dec(v_a_3058_);
v___x_3070_ = 0;
v___x_3071_ = lean_box(v___x_3070_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 0, v___x_3071_);
v___x_3073_ = v___x_3060_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3071_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
v_a_3076_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_3057_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3057_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
else
{
uint8_t v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
lean_dec_ref(v___x_3055_);
lean_dec_ref(v_a_3052_);
v___x_3084_ = 0;
v___x_3085_ = lean_box(v___x_3084_);
v___x_3086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3085_);
return v___x_3086_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive___boxed(lean_object* v_type_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_type_3087_, v_a_3088_, v_a_3089_);
lean_dec(v_a_3089_);
lean_dec_ref(v_type_3087_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(lean_object* v_00_u03b1_3092_, lean_object* v_constName_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_){
_start:
{
lean_object* v___x_3097_; 
v___x_3097_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_3093_, v___y_3094_, v___y_3095_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3098_, lean_object* v_constName_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(v_00_u03b1_3098_, v_constName_3099_, v___y_3100_, v___y_3101_);
lean_dec(v___y_3101_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3104_, lean_object* v_ref_3105_, lean_object* v_constName_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v___x_3110_; 
v___x_3110_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_3105_, v_constName_3106_, v___y_3107_, v___y_3108_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3111_, lean_object* v_ref_3112_, lean_object* v_constName_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(v_00_u03b1_3111_, v_ref_3112_, v_constName_3113_, v___y_3114_, v___y_3115_);
lean_dec(v___y_3115_);
lean_dec(v_ref_3112_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3118_, lean_object* v_ref_3119_, lean_object* v_msg_3120_, lean_object* v_declHint_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v___x_3125_; 
v___x_3125_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3119_, v_msg_3120_, v_declHint_3121_, v___y_3122_, v___y_3123_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3126_, lean_object* v_ref_3127_, lean_object* v_msg_3128_, lean_object* v_declHint_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3126_, v_ref_3127_, v_msg_3128_, v_declHint_3129_, v___y_3130_, v___y_3131_);
lean_dec(v___y_3131_);
lean_dec(v_ref_3127_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_3134_, lean_object* v_declHint_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
lean_object* v___x_3139_; 
v___x_3139_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_3134_, v_declHint_3135_, v___y_3137_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_3140_, lean_object* v_declHint_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_3140_, v_declHint_3141_, v___y_3142_, v___y_3143_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_3146_, lean_object* v_ref_3147_, lean_object* v_msg_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3147_, v_msg_3148_, v___y_3149_, v___y_3150_);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_3153_, lean_object* v_ref_3154_, lean_object* v_msg_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_3153_, v_ref_3154_, v_msg_3155_, v___y_3156_, v___y_3157_);
lean_dec(v___y_3157_);
lean_dec(v_ref_3154_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_3160_, lean_object* v_msg_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v___x_3165_; 
v___x_3165_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_3161_, v___y_3162_, v___y_3163_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_3166_, lean_object* v_msg_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_3166_, v_msg_3167_, v___y_3168_, v___y_3169_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(lean_object* v_goal_3172_, lean_object* v_fvarId_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_){
_start:
{
lean_object* v_toGoalState_3179_; lean_object* v_mvarId_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3216_; 
v_toGoalState_3179_ = lean_ctor_get(v_goal_3172_, 0);
v_mvarId_3180_ = lean_ctor_get(v_goal_3172_, 1);
v_isSharedCheck_3216_ = !lean_is_exclusive(v_goal_3172_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3182_ = v_goal_3172_;
v_isShared_3183_ = v_isSharedCheck_3216_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_mvarId_3180_);
lean_inc(v_toGoalState_3179_);
lean_dec(v_goal_3172_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3216_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3184_; 
v___x_3184_ = l_Lean_Meta_Grind_injection_x3f(v_mvarId_3180_, v_fvarId_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3207_; 
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3187_ = v___x_3184_;
v_isShared_3188_ = v_isSharedCheck_3207_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3184_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3207_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
if (lean_obj_tag(v_a_3185_) == 1)
{
lean_object* v_val_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3202_; 
v_val_3189_ = lean_ctor_get(v_a_3185_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v_a_3185_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3191_ = v_a_3185_;
v_isShared_3192_ = v_isSharedCheck_3202_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_val_3189_);
lean_dec(v_a_3185_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3202_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 1, v_val_3189_);
v___x_3194_ = v___x_3182_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_toGoalState_3179_);
lean_ctor_set(v_reuseFailAlloc_3201_, 1, v_val_3189_);
v___x_3194_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
lean_object* v___x_3196_; 
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 0, v___x_3194_);
v___x_3196_ = v___x_3191_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3194_);
v___x_3196_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
lean_object* v___x_3198_; 
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 0, v___x_3196_);
v___x_3198_ = v___x_3187_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3196_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
}
else
{
lean_object* v___x_3203_; lean_object* v___x_3205_; 
lean_dec(v_a_3185_);
lean_del_object(v___x_3182_);
lean_dec_ref(v_toGoalState_3179_);
v___x_3203_ = lean_box(0);
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 0, v___x_3203_);
v___x_3205_ = v___x_3187_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3203_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
else
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
lean_del_object(v___x_3182_);
lean_dec_ref(v_toGoalState_3179_);
v_a_3208_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3184_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3184_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f___boxed(lean_object* v_goal_3217_, lean_object* v_fvarId_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_3217_, v_fvarId_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(lean_object* v_mvarId_3225_, lean_object* v_x_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
lean_object* v___x_3232_; 
v___x_3232_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3225_, v_x_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3240_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3235_ = v___x_3232_;
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_a_3233_);
lean_dec(v___x_3232_);
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
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3248_; 
v_a_3241_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3243_ = v___x_3232_;
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_a_3241_);
lean_dec(v___x_3232_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3246_; 
if (v_isShared_3244_ == 0)
{
v___x_3246_ = v___x_3243_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_a_3241_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg___boxed(lean_object* v_mvarId_3249_, lean_object* v_x_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
lean_object* v_res_3256_; 
v_res_3256_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3249_, v_x_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(lean_object* v_00_u03b1_3257_, lean_object* v_mvarId_3258_, lean_object* v_x_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
lean_object* v___x_3265_; 
v___x_3265_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3258_, v_x_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___boxed(lean_object* v_00_u03b1_3266_, lean_object* v_mvarId_3267_, lean_object* v_x_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(v_00_u03b1_3266_, v_mvarId_3267_, v_x_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(lean_object* v_mvarId_3275_, lean_object* v_toGoalState_3276_, lean_object* v_goal_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v___x_3283_; 
lean_inc(v_mvarId_3275_);
v___x_3283_ = l_Lean_MVarId_getType(v_mvarId_3275_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v_a_3284_; lean_object* v___x_3285_; 
v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
lean_inc(v_a_3284_);
lean_dec_ref(v___x_3283_);
lean_inc(v___y_3281_);
lean_inc_ref(v___y_3280_);
lean_inc(v___y_3279_);
lean_inc_ref(v___y_3278_);
v___x_3285_ = l_Lean_Meta_isProp(v_a_3284_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3312_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3288_ = v___x_3285_;
v_isShared_3289_ = v_isSharedCheck_3312_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3285_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3312_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
uint8_t v___x_3290_; 
v___x_3290_ = lean_unbox(v_a_3286_);
lean_dec(v_a_3286_);
if (v___x_3290_ == 0)
{
lean_object* v___x_3291_; 
lean_del_object(v___x_3288_);
lean_dec_ref(v_goal_3277_);
v___x_3291_ = l_Lean_MVarId_exfalso(v_mvarId_3275_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v_a_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3300_; 
v_a_3292_ = lean_ctor_get(v___x_3291_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3294_ = v___x_3291_;
v_isShared_3295_ = v_isSharedCheck_3300_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_a_3292_);
lean_dec(v___x_3291_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3300_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3296_; lean_object* v___x_3298_; 
v___x_3296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3296_, 0, v_toGoalState_3276_);
lean_ctor_set(v___x_3296_, 1, v_a_3292_);
if (v_isShared_3295_ == 0)
{
lean_ctor_set(v___x_3294_, 0, v___x_3296_);
v___x_3298_ = v___x_3294_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v___x_3296_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
else
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3308_; 
lean_dec_ref(v_toGoalState_3276_);
v_a_3301_ = lean_ctor_get(v___x_3291_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3303_ = v___x_3291_;
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3291_);
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
else
{
lean_object* v___x_3310_; 
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec_ref(v_toGoalState_3276_);
lean_dec(v_mvarId_3275_);
if (v_isShared_3289_ == 0)
{
lean_ctor_set(v___x_3288_, 0, v_goal_3277_);
v___x_3310_ = v___x_3288_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_goal_3277_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
}
else
{
lean_object* v_a_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3320_; 
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec_ref(v_goal_3277_);
lean_dec_ref(v_toGoalState_3276_);
lean_dec(v_mvarId_3275_);
v_a_3313_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3315_ = v___x_3285_;
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_a_3313_);
lean_dec(v___x_3285_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3318_; 
if (v_isShared_3316_ == 0)
{
v___x_3318_ = v___x_3315_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_a_3313_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
}
else
{
lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3328_; 
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec_ref(v_goal_3277_);
lean_dec_ref(v_toGoalState_3276_);
lean_dec(v_mvarId_3275_);
v_a_3321_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3323_ = v___x_3283_;
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_a_3321_);
lean_dec(v___x_3283_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3326_; 
if (v_isShared_3324_ == 0)
{
v___x_3326_ = v___x_3323_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_a_3321_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed(lean_object* v_mvarId_3329_, lean_object* v_toGoalState_3330_, lean_object* v_goal_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_){
_start:
{
lean_object* v_res_3337_; 
v_res_3337_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(v_mvarId_3329_, v_toGoalState_3330_, v_goal_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(lean_object* v_goal_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_){
_start:
{
lean_object* v_toGoalState_3344_; lean_object* v_mvarId_3345_; lean_object* v___f_3346_; lean_object* v___x_3347_; 
v_toGoalState_3344_ = lean_ctor_get(v_goal_3338_, 0);
lean_inc_ref(v_toGoalState_3344_);
v_mvarId_3345_ = lean_ctor_get(v_goal_3338_, 1);
lean_inc(v_mvarId_3345_);
lean_inc(v_mvarId_3345_);
v___f_3346_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3346_, 0, v_mvarId_3345_);
lean_closure_set(v___f_3346_, 1, v_toGoalState_3344_);
lean_closure_set(v___f_3346_, 2, v_goal_3338_);
v___x_3347_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3345_, v___f_3346_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___boxed(lean_object* v_goal_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f(lean_object* v_goal_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_){
_start:
{
lean_object* v_mvarId_3361_; lean_object* v___x_3362_; 
v_mvarId_3361_ = lean_ctor_get(v_goal_3355_, 1);
lean_inc(v_mvarId_3361_);
lean_dec_ref(v_goal_3355_);
v___x_3362_ = l_Lean_MVarId_getDecl(v_mvarId_3361_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3372_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3365_ = v___x_3362_;
v_isShared_3366_ = v_isSharedCheck_3372_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3362_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3372_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v_lctx_3367_; lean_object* v___x_3368_; lean_object* v___x_3370_; 
v_lctx_3367_ = lean_ctor_get(v_a_3363_, 1);
lean_inc_ref(v_lctx_3367_);
lean_dec(v_a_3363_);
v___x_3368_ = l_Lean_LocalContext_lastDecl(v_lctx_3367_);
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 0, v___x_3368_);
v___x_3370_ = v___x_3365_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v___x_3368_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
else
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3380_; 
v_a_3373_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3375_ = v___x_3362_;
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3362_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f___boxed(lean_object* v_goal_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_Lean_Meta_Grind_Goal_lastDecl_x3f(v_goal_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_);
lean_dec(v_a_3385_);
lean_dec_ref(v_a_3384_);
lean_dec(v_a_3383_);
lean_dec_ref(v_a_3382_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(lean_object* v_goal_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_){
_start:
{
if (lean_obj_tag(v_a_3389_) == 0)
{
lean_object* v___x_3391_; 
v___x_3391_ = l_List_reverse___redArg(v_a_3390_);
return v___x_3391_;
}
else
{
lean_object* v_head_3392_; lean_object* v_tail_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3403_; 
v_head_3392_ = lean_ctor_get(v_a_3389_, 0);
v_tail_3393_ = lean_ctor_get(v_a_3389_, 1);
v_isSharedCheck_3403_ = !lean_is_exclusive(v_a_3389_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3395_ = v_a_3389_;
v_isShared_3396_ = v_isSharedCheck_3403_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_tail_3393_);
lean_inc(v_head_3392_);
lean_dec(v_a_3389_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3403_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v_toGoalState_3397_; lean_object* v___x_3398_; lean_object* v___x_3400_; 
v_toGoalState_3397_ = lean_ctor_get(v_goal_3388_, 0);
lean_inc_ref(v_toGoalState_3397_);
v___x_3398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3398_, 0, v_toGoalState_3397_);
lean_ctor_set(v___x_3398_, 1, v_head_3392_);
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 1, v_a_3390_);
lean_ctor_set(v___x_3395_, 0, v___x_3398_);
v___x_3400_ = v___x_3395_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___x_3398_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v_a_3390_);
v___x_3400_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
v_a_3389_ = v_tail_3393_;
v_a_3390_ = v___x_3400_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0___boxed(lean_object* v_goal_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v_goal_3404_, v_a_3405_, v_a_3406_);
lean_dec_ref(v_goal_3404_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(lean_object* v_kp_3408_, lean_object* v_as_x27_3409_, lean_object* v_b_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_){
_start:
{
if (lean_obj_tag(v_as_x27_3409_) == 0)
{
lean_object* v___x_3421_; 
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v_kp_3408_);
v___x_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3421_, 0, v_b_3410_);
return v___x_3421_;
}
else
{
lean_object* v_head_3422_; lean_object* v_tail_3423_; lean_object* v___x_3424_; 
v_head_3422_ = lean_ctor_get(v_as_x27_3409_, 0);
lean_inc(v_head_3422_);
v_tail_3423_ = lean_ctor_get(v_as_x27_3409_, 1);
lean_inc(v_tail_3423_);
lean_dec_ref(v_as_x27_3409_);
lean_inc_ref(v_kp_3408_);
lean_inc(v___y_3419_);
lean_inc_ref(v___y_3418_);
lean_inc(v___y_3417_);
lean_inc_ref(v___y_3416_);
lean_inc(v___y_3415_);
lean_inc_ref(v___y_3414_);
lean_inc(v___y_3413_);
lean_inc_ref(v___y_3412_);
lean_inc(v___y_3411_);
v___x_3424_ = lean_apply_11(v_kp_3408_, v_head_3422_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, lean_box(0));
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_a_3425_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3425_);
lean_dec_ref(v___x_3424_);
if (lean_obj_tag(v_a_3425_) == 0)
{
lean_object* v_fst_3426_; lean_object* v_snd_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3437_; 
v_fst_3426_ = lean_ctor_get(v_b_3410_, 0);
v_snd_3427_ = lean_ctor_get(v_b_3410_, 1);
v_isSharedCheck_3437_ = !lean_is_exclusive(v_b_3410_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3429_ = v_b_3410_;
v_isShared_3430_ = v_isSharedCheck_3437_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_snd_3427_);
lean_inc(v_fst_3426_);
lean_dec(v_b_3410_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3437_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v_seq_3431_; lean_object* v___x_3432_; lean_object* v___x_3434_; 
v_seq_3431_ = lean_ctor_get(v_a_3425_, 0);
lean_inc(v_seq_3431_);
lean_dec_ref(v_a_3425_);
v___x_3432_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_fst_3426_, v_seq_3431_);
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 0, v___x_3432_);
v___x_3434_ = v___x_3429_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3432_);
lean_ctor_set(v_reuseFailAlloc_3436_, 1, v_snd_3427_);
v___x_3434_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
v_as_x27_3409_ = v_tail_3423_;
v_b_3410_ = v___x_3434_;
goto _start;
}
}
}
else
{
lean_object* v_fst_3438_; lean_object* v_snd_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3449_; 
v_fst_3438_ = lean_ctor_get(v_b_3410_, 0);
v_snd_3439_ = lean_ctor_get(v_b_3410_, 1);
v_isSharedCheck_3449_ = !lean_is_exclusive(v_b_3410_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3441_ = v_b_3410_;
v_isShared_3442_ = v_isSharedCheck_3449_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_snd_3439_);
lean_inc(v_fst_3438_);
lean_dec(v_b_3410_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3449_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v_gs_3443_; lean_object* v___x_3444_; lean_object* v___x_3446_; 
v_gs_3443_ = lean_ctor_get(v_a_3425_, 0);
lean_inc(v_gs_3443_);
lean_dec_ref(v_a_3425_);
v___x_3444_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_snd_3439_, v_gs_3443_);
if (v_isShared_3442_ == 0)
{
lean_ctor_set(v___x_3441_, 1, v___x_3444_);
v___x_3446_ = v___x_3441_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_fst_3438_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v___x_3444_);
v___x_3446_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
v_as_x27_3409_ = v_tail_3423_;
v_b_3410_ = v___x_3446_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3457_; 
lean_dec(v_tail_3423_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v_b_3410_);
lean_dec_ref(v_kp_3408_);
v_a_3450_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3452_ = v___x_3424_;
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3424_);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg___boxed(lean_object* v_kp_3458_, lean_object* v_as_x27_3459_, lean_object* v_b_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v_res_3471_; 
v_res_3471_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3458_, v_as_x27_3459_, v_b_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
return v_res_3471_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3474_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__0));
v___x_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
lean_ctor_set(v___x_3475_, 1, v___x_3474_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(lean_object* v_fvarId_3476_, lean_object* v_mvarId_3477_, lean_object* v_goal_3478_, lean_object* v_kp_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_){
_start:
{
lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___x_3545_; 
lean_inc_ref(v___y_3485_);
lean_inc(v_fvarId_3476_);
v___x_3545_ = l_Lean_FVarId_getType___redArg(v_fvarId_3476_, v___y_3485_, v___y_3487_, v___y_3488_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v_a_3546_; lean_object* v___x_3547_; 
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
lean_inc(v_a_3546_);
lean_dec_ref(v___x_3545_);
lean_inc(v___y_3488_);
lean_inc_ref(v___y_3487_);
lean_inc(v___y_3486_);
lean_inc_ref(v___y_3485_);
v___x_3547_ = lean_whnf(v_a_3546_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v_a_3548_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___x_3570_; 
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3548_);
lean_dec_ref(v___x_3547_);
v___x_3570_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_a_3548_, v___y_3481_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3610_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3573_ = v___x_3570_;
v_isShared_3574_ = v_isSharedCheck_3610_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3570_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3610_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
uint8_t v___x_3575_; 
v___x_3575_ = lean_unbox(v_a_3571_);
lean_dec(v_a_3571_);
if (v___x_3575_ == 0)
{
lean_object* v___x_3576_; lean_object* v___x_3578_; 
lean_dec(v_a_3548_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v_kp_3479_);
lean_dec(v_mvarId_3477_);
lean_dec(v_fvarId_3476_);
v___x_3576_ = lean_box(0);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 0, v___x_3576_);
v___x_3578_ = v___x_3573_;
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
else
{
lean_object* v___x_3580_; 
lean_del_object(v___x_3573_);
v___x_3580_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3481_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v_a_3581_; uint8_t v___x_3582_; 
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
lean_inc(v_a_3581_);
lean_dec_ref(v___x_3580_);
v___x_3582_ = lean_unbox(v_a_3581_);
lean_dec(v_a_3581_);
if (v___x_3582_ == 0)
{
v___y_3550_ = v___y_3480_;
v___y_3551_ = v___y_3481_;
v___y_3552_ = v___y_3482_;
v___y_3553_ = v___y_3483_;
v___y_3554_ = v___y_3484_;
v___y_3555_ = v___y_3485_;
v___y_3556_ = v___y_3486_;
v___y_3557_ = v___y_3487_;
v___y_3558_ = v___y_3488_;
goto v___jp_3549_;
}
else
{
lean_object* v___x_3583_; 
lean_inc_ref(v___y_3487_);
v___x_3583_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_a_3548_, v___y_3487_, v___y_3488_);
if (lean_obj_tag(v___x_3583_) == 0)
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3593_; 
v_a_3584_ = lean_ctor_get(v___x_3583_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3586_ = v___x_3583_;
v_isShared_3587_ = v_isSharedCheck_3593_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3583_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3593_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
uint8_t v___x_3588_; 
v___x_3588_ = lean_unbox(v_a_3584_);
lean_dec(v_a_3584_);
if (v___x_3588_ == 0)
{
lean_object* v___x_3589_; lean_object* v___x_3591_; 
lean_dec(v_a_3548_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v_kp_3479_);
lean_dec(v_mvarId_3477_);
lean_dec(v_fvarId_3476_);
v___x_3589_ = lean_box(0);
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 0, v___x_3589_);
v___x_3591_ = v___x_3586_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___x_3589_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
else
{
lean_del_object(v___x_3586_);
v___y_3550_ = v___y_3480_;
v___y_3551_ = v___y_3481_;
v___y_3552_ = v___y_3482_;
v___y_3553_ = v___y_3483_;
v___y_3554_ = v___y_3484_;
v___y_3555_ = v___y_3485_;
v___y_3556_ = v___y_3486_;
v___y_3557_ = v___y_3487_;
v___y_3558_ = v___y_3488_;
goto v___jp_3549_;
}
}
}
else
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
lean_dec(v_a_3548_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v_kp_3479_);
lean_dec(v_mvarId_3477_);
lean_dec(v_fvarId_3476_);
v_a_3594_ = lean_ctor_get(v___x_3583_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___x_3583_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3583_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3597_ == 0)
{
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3594_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
}
else
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3609_; 
lean_dec(v_a_3548_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v_kp_3479_);
lean_dec(v_mvarId_3477_);
lean_dec(v_fvarId_3476_);
v_a_3602_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3604_ = v___x_3580_;
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3580_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3607_; 
if (v_isShared_3605_ == 0)
{
v___x_3607_ = v___x_3604_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3602_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
}
}
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec(v_a_3548_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v_kp_3479_);
lean_dec(v_mvarId_3477_);
lean_dec(v_fvarId_3476_);
v_a_3611_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3570_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3570_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
v___jp_3549_:
{
lean_object* v___x_3559_; 
v___x_3559_ = l_Lean_Expr_getAppFn(v_a_3548_);
lean_dec(v_a_3548_);
if (lean_obj_tag(v___x_3559_) == 4)
{
lean_object* v_declName_3560_; lean_object* v___x_3561_; 
v_declName_3560_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_declName_3560_);
lean_dec_ref(v___x_3559_);
v___x_3561_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3560_, v___y_3552_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_dec_ref(v___x_3561_);
v___y_3491_ = v___y_3550_;
v___y_3492_ = v___y_3551_;
v___y_3493_ = v___y_3552_;
v___y_3494_ = v___y_3553_;
v___y_3495_ = v___y_3554_;
v___y_3496_ = v___y_3555_;
v___y_3497_ = v___y_3556_;
v___y_3498_ = v___y_3557_;
v___y_3499_ = v___y_3558_;
goto v___jp_3490_;
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v_kp_3479_);
lean_dec(v_mvarId_3477_);
lean_dec(v_fvarId_3476_);
v_a_3562_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___x_3561_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3561_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
else
{
lean_dec_ref(v___x_3559_);
v___y_3491_ = v___y_3550_;
v___y_3492_ = v___y_3551_;
v___y_3493_ = v___y_3552_;
v___y_3494_ = v___y_3553_;
v___y_3495_ = v___y_3554_;
v___y_3496_ = v___y_3555_;
v___y_3497_ = v___y_3556_;
v___y_3498_ = v___y_3557_;
v___y_3499_ = v___y_3558_;
goto v___jp_3490_;
}
}
}
else
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3626_; 
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v_kp_3479_);
lean_dec(v_mvarId_3477_);
lean_dec(v_fvarId_3476_);
v_a_3619_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3621_ = v___x_3547_;
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3547_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3624_; 
if (v_isShared_3622_ == 0)
{
v___x_3624_ = v___x_3621_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3619_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
else
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v_kp_3479_);
lean_dec(v_mvarId_3477_);
lean_dec(v_fvarId_3476_);
v_a_3627_ = lean_ctor_get(v___x_3545_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3545_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3545_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3545_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
v___jp_3490_:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3500_ = l_Lean_mkFVar(v_fvarId_3476_);
lean_inc(v___y_3499_);
lean_inc_ref(v___y_3498_);
lean_inc(v___y_3497_);
lean_inc_ref(v___y_3496_);
v___x_3501_ = l_Lean_Meta_Grind_cases(v_mvarId_3477_, v___x_3500_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref(v___x_3501_);
v___x_3503_ = lean_box(0);
v___x_3504_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v_goal_3478_, v_a_3502_, v___x_3503_);
v___x_3505_ = lean_unsigned_to_nat(0u);
v___x_3506_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__1);
v___x_3507_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3479_, v___x_3504_, v___x_3506_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3528_; 
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3510_ = v___x_3507_;
v_isShared_3511_ = v_isSharedCheck_3528_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3507_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3528_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v_fst_3512_; lean_object* v_snd_3513_; lean_object* v___x_3514_; uint8_t v___x_3515_; 
v_fst_3512_ = lean_ctor_get(v_a_3508_, 0);
lean_inc(v_fst_3512_);
v_snd_3513_ = lean_ctor_get(v_a_3508_, 1);
lean_inc(v_snd_3513_);
lean_dec(v_a_3508_);
v___x_3514_ = lean_array_get_size(v_snd_3513_);
v___x_3515_ = lean_nat_dec_eq(v___x_3514_, v___x_3505_);
if (v___x_3515_ == 0)
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3520_; 
lean_dec(v_fst_3512_);
v___x_3516_ = lean_array_to_list(v_snd_3513_);
v___x_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3516_);
v___x_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 0, v___x_3518_);
v___x_3520_ = v___x_3510_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3518_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
else
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3526_; 
lean_dec(v_snd_3513_);
v___x_3522_ = lean_array_to_list(v_fst_3512_);
v___x_3523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3522_);
v___x_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3523_);
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 0, v___x_3524_);
v___x_3526_ = v___x_3510_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3524_);
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
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3536_; 
v_a_3529_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3531_ = v___x_3507_;
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3507_);
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
else
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3544_; 
lean_dec(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec_ref(v_kp_3479_);
v_a_3537_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3539_ = v___x_3501_;
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3501_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3542_; 
if (v_isShared_3540_ == 0)
{
v___x_3542_ = v___x_3539_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3537_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed(lean_object* v_fvarId_3635_, lean_object* v_mvarId_3636_, lean_object* v_goal_3637_, lean_object* v_kp_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(v_fvarId_3635_, v_mvarId_3636_, v_goal_3637_, v_kp_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
lean_dec_ref(v_goal_3637_);
return v_res_3649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(lean_object* v_goal_3650_, lean_object* v_fvarId_3651_, lean_object* v_kp_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_){
_start:
{
lean_object* v_mvarId_3663_; lean_object* v___f_3664_; lean_object* v___x_3665_; 
v_mvarId_3663_ = lean_ctor_get(v_goal_3650_, 1);
lean_inc(v_mvarId_3663_);
lean_inc(v_mvarId_3663_);
v___f_3664_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed), 14, 4);
lean_closure_set(v___f_3664_, 0, v_fvarId_3651_);
lean_closure_set(v___f_3664_, 1, v_mvarId_3663_);
lean_closure_set(v___f_3664_, 2, v_goal_3650_);
lean_closure_set(v___f_3664_, 3, v_kp_3652_);
v___x_3665_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3663_, v___f_3664_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___boxed(lean_object* v_goal_3666_, lean_object* v_fvarId_3667_, lean_object* v_kp_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_){
_start:
{
lean_object* v_res_3679_; 
v_res_3679_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3666_, v_fvarId_3667_, v_kp_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(lean_object* v_kp_3680_, lean_object* v_as_3681_, lean_object* v_as_x27_3682_, lean_object* v_b_3683_, lean_object* v_a_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_){
_start:
{
lean_object* v___x_3695_; 
v___x_3695_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3680_, v_as_x27_3682_, v_b_3683_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___boxed(lean_object* v_kp_3696_, lean_object* v_as_3697_, lean_object* v_as_x27_3698_, lean_object* v_b_3699_, lean_object* v_a_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(v_kp_3696_, v_as_3697_, v_as_x27_3698_, v_b_3699_, v_a_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_);
lean_dec(v_as_3697_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0(lean_object* v_goal_3712_, lean_object* v_fvarId_3713_, lean_object* v_generation_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_){
_start:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3725_ = lean_st_mk_ref(v_goal_3712_);
lean_inc(v___x_3725_);
v___x_3726_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_3713_, v_generation_3714_, v___x_3725_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3735_; 
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3735_ == 0)
{
lean_object* v_unused_3736_; 
v_unused_3736_ = lean_ctor_get(v___x_3726_, 0);
lean_dec(v_unused_3736_);
v___x_3728_ = v___x_3726_;
v_isShared_3729_ = v_isSharedCheck_3735_;
goto v_resetjp_3727_;
}
else
{
lean_dec(v___x_3726_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3735_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3733_; 
v___x_3730_ = lean_st_ref_get(v___x_3725_);
v___x_3731_ = lean_st_ref_get(v___x_3725_);
lean_dec(v___x_3725_);
lean_dec(v___x_3731_);
if (v_isShared_3729_ == 0)
{
lean_ctor_set(v___x_3728_, 0, v___x_3730_);
v___x_3733_ = v___x_3728_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3730_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
else
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3744_; 
lean_dec(v___x_3725_);
v_a_3737_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3739_ = v___x_3726_;
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3726_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0___boxed(lean_object* v_goal_3745_, lean_object* v_fvarId_3746_, lean_object* v_generation_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v_res_3758_; 
v_res_3758_ = l_Lean_Meta_Grind_Action_intro___lam__0(v_goal_3745_, v_fvarId_3746_, v_generation_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
return v_res_3758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro(lean_object* v_generation_3761_, lean_object* v_goal_3762_, lean_object* v_kna_3763_, lean_object* v_kp_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_){
_start:
{
lean_object* v_toGoalState_3775_; uint8_t v_inconsistent_3776_; 
v_toGoalState_3775_ = lean_ctor_get(v_goal_3762_, 0);
v_inconsistent_3776_ = lean_ctor_get_uint8(v_toGoalState_3775_, sizeof(void*)*18);
if (v_inconsistent_3776_ == 0)
{
lean_object* v_mvarId_3777_; lean_object* v___x_3778_; 
v_mvarId_3777_ = lean_ctor_get(v_goal_3762_, 1);
lean_inc(v_mvarId_3777_);
v___x_3778_ = l_Lean_MVarId_getType(v_mvarId_3777_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_a_3779_; uint8_t v___x_3780_; 
v_a_3779_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3779_);
lean_dec_ref(v___x_3778_);
v___x_3780_ = l_Lean_Expr_isFalse(v_a_3779_);
if (v___x_3780_ == 0)
{
lean_object* v___x_3781_; 
lean_dec_ref(v_kna_3763_);
lean_inc(v_a_3773_);
lean_inc_ref(v_a_3772_);
lean_inc(v_a_3771_);
lean_inc_ref(v_a_3770_);
lean_inc(v_a_3769_);
lean_inc_ref(v_a_3768_);
lean_inc(v_a_3767_);
lean_inc_ref(v_a_3766_);
lean_inc(v_a_3765_);
lean_inc(v_generation_3761_);
v___x_3781_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_3762_, v_generation_3761_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3782_);
lean_dec_ref(v___x_3781_);
switch(lean_obj_tag(v_a_3782_))
{
case 0:
{
lean_object* v_goal_3783_; lean_object* v___x_3784_; 
lean_dec(v_generation_3761_);
v_goal_3783_ = lean_ctor_get(v_a_3782_, 0);
lean_inc_ref(v_goal_3783_);
lean_dec_ref(v_a_3782_);
lean_inc(v_a_3773_);
lean_inc_ref(v_a_3772_);
lean_inc(v_a_3771_);
lean_inc_ref(v_a_3770_);
v___x_3784_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_3783_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; lean_object* v_toGoalState_3786_; lean_object* v_mvarId_3787_; lean_object* v___x_3788_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_a_3785_);
lean_dec_ref(v___x_3784_);
v_toGoalState_3786_ = lean_ctor_get(v_a_3785_, 0);
v_mvarId_3787_ = lean_ctor_get(v_a_3785_, 1);
lean_inc(v_a_3773_);
lean_inc_ref(v_a_3772_);
lean_inc(v_a_3771_);
lean_inc_ref(v_a_3770_);
lean_inc(v_mvarId_3787_);
v___x_3788_ = l_Lean_MVarId_byContra_x3f(v_mvarId_3787_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v_a_3789_; 
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
lean_inc(v_a_3789_);
lean_dec_ref(v___x_3788_);
if (lean_obj_tag(v_a_3789_) == 1)
{
lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3798_; 
lean_inc_ref(v_toGoalState_3786_);
v_isSharedCheck_3798_ = !lean_is_exclusive(v_a_3785_);
if (v_isSharedCheck_3798_ == 0)
{
lean_object* v_unused_3799_; lean_object* v_unused_3800_; 
v_unused_3799_ = lean_ctor_get(v_a_3785_, 1);
lean_dec(v_unused_3799_);
v_unused_3800_ = lean_ctor_get(v_a_3785_, 0);
lean_dec(v_unused_3800_);
v___x_3791_ = v_a_3785_;
v_isShared_3792_ = v_isSharedCheck_3798_;
goto v_resetjp_3790_;
}
else
{
lean_dec(v_a_3785_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3798_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v_val_3793_; lean_object* v___x_3795_; 
v_val_3793_ = lean_ctor_get(v_a_3789_, 0);
lean_inc(v_val_3793_);
lean_dec_ref(v_a_3789_);
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 1, v_val_3793_);
v___x_3795_ = v___x_3791_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_toGoalState_3786_);
lean_ctor_set(v_reuseFailAlloc_3797_, 1, v_val_3793_);
v___x_3795_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
lean_object* v___x_3796_; 
v___x_3796_ = lean_apply_11(v_kp_3764_, v___x_3795_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, lean_box(0));
return v___x_3796_;
}
}
}
else
{
lean_object* v___x_3801_; 
lean_dec(v_a_3789_);
v___x_3801_ = lean_apply_11(v_kp_3764_, v_a_3785_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, lean_box(0));
return v___x_3801_;
}
}
else
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
lean_dec(v_a_3785_);
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec_ref(v_kp_3764_);
v_a_3802_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3804_ = v___x_3788_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3788_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
else
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3817_; 
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec_ref(v_kp_3764_);
v_a_3810_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3812_ = v___x_3784_;
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3784_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3815_; 
if (v_isShared_3813_ == 0)
{
v___x_3815_ = v___x_3812_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3810_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3818_; lean_object* v_goal_3819_; lean_object* v___x_3820_; 
v_fvarId_3818_ = lean_ctor_get(v_a_3782_, 0);
lean_inc(v_fvarId_3818_);
v_goal_3819_ = lean_ctor_get(v_a_3782_, 1);
lean_inc_ref(v_goal_3819_);
lean_dec_ref(v_a_3782_);
lean_inc(v_a_3773_);
lean_inc_ref(v_a_3772_);
lean_inc(v_a_3771_);
lean_inc_ref(v_a_3770_);
lean_inc(v_fvarId_3818_);
lean_inc_ref(v_goal_3819_);
v___x_3820_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_3819_, v_fvarId_3818_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
if (lean_obj_tag(v___x_3820_) == 0)
{
lean_object* v_a_3821_; 
v_a_3821_ = lean_ctor_get(v___x_3820_, 0);
lean_inc(v_a_3821_);
lean_dec_ref(v___x_3820_);
if (lean_obj_tag(v_a_3821_) == 1)
{
lean_object* v_val_3822_; lean_object* v___x_3823_; 
lean_dec_ref(v_goal_3819_);
lean_dec(v_fvarId_3818_);
lean_dec(v_generation_3761_);
v_val_3822_ = lean_ctor_get(v_a_3821_, 0);
lean_inc(v_val_3822_);
lean_dec_ref(v_a_3821_);
v___x_3823_ = lean_apply_11(v_kp_3764_, v_val_3822_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, lean_box(0));
return v___x_3823_;
}
else
{
lean_object* v___x_3824_; 
lean_dec(v_a_3821_);
lean_inc(v_a_3773_);
lean_inc_ref(v_a_3772_);
lean_inc(v_a_3771_);
lean_inc_ref(v_a_3770_);
lean_inc(v_a_3769_);
lean_inc_ref(v_a_3768_);
lean_inc(v_a_3767_);
lean_inc_ref(v_a_3766_);
lean_inc(v_a_3765_);
lean_inc_ref(v_kp_3764_);
lean_inc(v_fvarId_3818_);
lean_inc_ref(v_goal_3819_);
v___x_3824_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3819_, v_fvarId_3818_, v_kp_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3846_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3827_ = v___x_3824_;
v_isShared_3828_ = v_isSharedCheck_3846_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3824_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3846_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
if (lean_obj_tag(v_a_3825_) == 1)
{
lean_object* v_val_3829_; lean_object* v___x_3831_; 
lean_dec_ref(v_goal_3819_);
lean_dec(v_fvarId_3818_);
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec_ref(v_kp_3764_);
lean_dec(v_generation_3761_);
v_val_3829_ = lean_ctor_get(v_a_3825_, 0);
lean_inc(v_val_3829_);
lean_dec_ref(v_a_3825_);
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 0, v_val_3829_);
v___x_3831_ = v___x_3827_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_val_3829_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
else
{
lean_object* v_mvarId_3833_; lean_object* v___f_3834_; lean_object* v___x_3835_; 
lean_del_object(v___x_3827_);
lean_dec(v_a_3825_);
v_mvarId_3833_ = lean_ctor_get(v_goal_3819_, 1);
lean_inc(v_mvarId_3833_);
v___f_3834_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intro___lam__0___boxed), 13, 3);
lean_closure_set(v___f_3834_, 0, v_goal_3819_);
lean_closure_set(v___f_3834_, 1, v_fvarId_3818_);
lean_closure_set(v___f_3834_, 2, v_generation_3761_);
lean_inc(v_a_3773_);
lean_inc_ref(v_a_3772_);
lean_inc(v_a_3771_);
lean_inc_ref(v_a_3770_);
lean_inc(v_a_3769_);
lean_inc_ref(v_a_3768_);
lean_inc(v_a_3767_);
lean_inc_ref(v_a_3766_);
lean_inc(v_a_3765_);
v___x_3835_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3833_, v___f_3834_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_object* v_a_3836_; lean_object* v___x_3837_; 
v_a_3836_ = lean_ctor_get(v___x_3835_, 0);
lean_inc(v_a_3836_);
lean_dec_ref(v___x_3835_);
v___x_3837_ = lean_apply_11(v_kp_3764_, v_a_3836_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, lean_box(0));
return v___x_3837_;
}
else
{
lean_object* v_a_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3845_; 
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec_ref(v_kp_3764_);
v_a_3838_ = lean_ctor_get(v___x_3835_, 0);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3835_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3840_ = v___x_3835_;
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_a_3838_);
lean_dec(v___x_3835_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___x_3843_; 
if (v_isShared_3841_ == 0)
{
v___x_3843_ = v___x_3840_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_a_3838_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
}
}
}
}
else
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3854_; 
lean_dec_ref(v_goal_3819_);
lean_dec(v_fvarId_3818_);
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec_ref(v_kp_3764_);
lean_dec(v_generation_3761_);
v_a_3847_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3849_ = v___x_3824_;
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3824_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3852_; 
if (v_isShared_3850_ == 0)
{
v___x_3852_ = v___x_3849_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_a_3847_);
v___x_3852_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
return v___x_3852_;
}
}
}
}
}
else
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
lean_dec_ref(v_goal_3819_);
lean_dec(v_fvarId_3818_);
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec_ref(v_kp_3764_);
lean_dec(v_generation_3761_);
v_a_3855_ = lean_ctor_get(v___x_3820_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3820_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3857_ = v___x_3820_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3820_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_a_3855_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
}
case 2:
{
lean_object* v_goal_3863_; lean_object* v___x_3864_; 
lean_dec(v_generation_3761_);
v_goal_3863_ = lean_ctor_get(v_a_3782_, 0);
lean_inc_ref(v_goal_3863_);
lean_dec_ref(v_a_3782_);
v___x_3864_ = lean_apply_11(v_kp_3764_, v_goal_3863_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, lean_box(0));
return v___x_3864_;
}
default: 
{
lean_object* v_fvarId_3865_; lean_object* v_goal_3866_; lean_object* v___x_3867_; 
lean_dec(v_generation_3761_);
v_fvarId_3865_ = lean_ctor_get(v_a_3782_, 0);
lean_inc(v_fvarId_3865_);
v_goal_3866_ = lean_ctor_get(v_a_3782_, 1);
lean_inc_ref(v_goal_3866_);
lean_dec_ref(v_a_3782_);
lean_inc(v_a_3773_);
lean_inc_ref(v_a_3772_);
lean_inc(v_a_3771_);
lean_inc_ref(v_a_3770_);
lean_inc(v_a_3769_);
lean_inc_ref(v_a_3768_);
lean_inc(v_a_3767_);
lean_inc_ref(v_a_3766_);
lean_inc(v_a_3765_);
lean_inc_ref(v_kp_3764_);
lean_inc_ref(v_goal_3866_);
v___x_3867_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3866_, v_fvarId_3865_, v_kp_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3877_; 
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3870_ = v___x_3867_;
v_isShared_3871_ = v_isSharedCheck_3877_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3867_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3877_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
if (lean_obj_tag(v_a_3868_) == 1)
{
lean_object* v_val_3872_; lean_object* v___x_3874_; 
lean_dec_ref(v_goal_3866_);
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec_ref(v_kp_3764_);
v_val_3872_ = lean_ctor_get(v_a_3868_, 0);
lean_inc(v_val_3872_);
lean_dec_ref(v_a_3868_);
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 0, v_val_3872_);
v___x_3874_ = v___x_3870_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_val_3872_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
else
{
lean_object* v___x_3876_; 
lean_del_object(v___x_3870_);
lean_dec(v_a_3868_);
v___x_3876_ = lean_apply_11(v_kp_3764_, v_goal_3866_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, lean_box(0));
return v___x_3876_;
}
}
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_dec_ref(v_goal_3866_);
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec_ref(v_kp_3764_);
v_a_3878_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3867_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3867_);
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
else
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3893_; 
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec_ref(v_kp_3764_);
lean_dec(v_generation_3761_);
v_a_3886_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3888_ = v___x_3781_;
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3781_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3891_; 
if (v_isShared_3889_ == 0)
{
v___x_3891_ = v___x_3888_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_a_3886_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
}
}
else
{
lean_object* v___x_3894_; 
lean_dec_ref(v_kp_3764_);
lean_dec(v_generation_3761_);
v___x_3894_ = lean_apply_11(v_kna_3763_, v_goal_3762_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, lean_box(0));
return v___x_3894_;
}
}
else
{
lean_object* v_a_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3902_; 
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec_ref(v_kp_3764_);
lean_dec_ref(v_kna_3763_);
lean_dec_ref(v_goal_3762_);
lean_dec(v_generation_3761_);
v_a_3895_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3902_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3897_ = v___x_3778_;
v_isShared_3898_ = v_isSharedCheck_3902_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_a_3895_);
lean_dec(v___x_3778_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3902_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
lean_object* v___x_3900_; 
if (v_isShared_3898_ == 0)
{
v___x_3900_ = v___x_3897_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v_a_3895_);
v___x_3900_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
return v___x_3900_;
}
}
}
}
else
{
lean_object* v___x_3903_; lean_object* v___x_3904_; 
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec_ref(v_kp_3764_);
lean_dec_ref(v_kna_3763_);
lean_dec_ref(v_goal_3762_);
lean_dec(v_generation_3761_);
v___x_3903_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intro___closed__0));
v___x_3904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3903_);
return v___x_3904_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___boxed(lean_object* v_generation_3905_, lean_object* v_goal_3906_, lean_object* v_kna_3907_, lean_object* v_kp_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_){
_start:
{
lean_object* v_res_3919_; 
v_res_3919_ = l_Lean_Meta_Grind_Action_intro(v_generation_3905_, v_goal_3906_, v_kna_3907_, v_kp_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_);
return v_res_3919_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_hugeNumber(void){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = lean_unsigned_to_nat(1000000u);
return v___x_3920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0(lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_){
_start:
{
lean_object* v___x_3934_; 
v___x_3934_ = l_Lean_Meta_Grind_Action_group___redArg(v___y_3921_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
return v___x_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0___boxed(lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l_Lean_Meta_Grind_Action_intros___lam__0(v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_);
lean_dec_ref(v___y_3936_);
return v_res_3948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1(lean_object* v_generation_3949_, lean_object* v___f_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_){
_start:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; 
v___x_3964_ = lean_unsigned_to_nat(1000000u);
v___x_3965_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intro___boxed), 14, 1);
lean_closure_set(v___x_3965_, 0, v_generation_3949_);
v___x_3966_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_loop___boxed), 15, 2);
lean_closure_set(v___x_3966_, 0, v___x_3964_);
lean_closure_set(v___x_3966_, 1, v___x_3965_);
v___x_3967_ = l_Lean_Meta_Grind_Action_andThen(v___x_3966_, v___f_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
return v___x_3967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1___boxed(lean_object* v_generation_3968_, lean_object* v___f_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l_Lean_Meta_Grind_Action_intros___lam__1(v_generation_3968_, v___f_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros(lean_object* v_generation_3986_, lean_object* v_a_3987_, lean_object* v_kna_3988_, lean_object* v_kp_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_){
_start:
{
lean_object* v___f_4000_; lean_object* v___f_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___f_4000_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intros___closed__0));
v___f_4001_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___lam__1___boxed), 15, 2);
lean_closure_set(v___f_4001_, 0, v_generation_3986_);
lean_closure_set(v___f_4001_, 1, v___f_4000_);
v___x_4002_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intros___closed__1));
v___x_4003_ = l_Lean_Meta_Grind_Action_andThen(v___x_4002_, v___f_4001_, v_a_3987_, v_kna_3988_, v_kp_3989_, v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_);
return v___x_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___boxed(lean_object* v_generation_4004_, lean_object* v_a_4005_, lean_object* v_kna_4006_, lean_object* v_kp_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l_Lean_Meta_Grind_Action_intros(v_generation_4004_, v_a_4005_, v_kna_4006_, v_kp_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_);
return v_res_4018_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4026_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__2));
v___x_4027_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1));
v___x_4028_ = l_Lean_mkConst(v___x_4027_, v___x_4026_);
return v___x_4028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(lean_object* v_goal_4029_, lean_object* v_prop_4030_, lean_object* v_proof_4031_, lean_object* v_generation_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_){
_start:
{
lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4043_ = lean_st_mk_ref(v_goal_4029_);
lean_inc(v___y_4041_);
lean_inc_ref(v___y_4040_);
lean_inc(v___y_4039_);
lean_inc_ref(v___y_4038_);
lean_inc(v___y_4037_);
lean_inc_ref(v___y_4036_);
lean_inc(v___y_4035_);
lean_inc_ref(v___y_4034_);
lean_inc(v___y_4033_);
lean_inc(v___x_4043_);
lean_inc_ref(v_prop_4030_);
v___x_4044_ = lean_grind_preprocess(v_prop_4030_, v___x_4043_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_);
if (lean_obj_tag(v___x_4044_) == 0)
{
lean_object* v_a_4045_; lean_object* v_expr_4046_; lean_object* v___x_4047_; 
v_a_4045_ = lean_ctor_get(v___x_4044_, 0);
lean_inc(v_a_4045_);
lean_dec_ref(v___x_4044_);
v_expr_4046_ = lean_ctor_get(v_a_4045_, 0);
lean_inc_ref(v_expr_4046_);
lean_inc(v___y_4041_);
lean_inc_ref(v___y_4040_);
lean_inc(v___y_4039_);
lean_inc_ref(v___y_4038_);
v___x_4047_ = l_Lean_Meta_Simp_Result_getProof(v_a_4045_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v_a_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; 
v_a_4048_ = lean_ctor_get(v___x_4047_, 0);
lean_inc(v_a_4048_);
lean_dec_ref(v___x_4047_);
v___x_4049_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3);
lean_inc_ref(v_expr_4046_);
v___x_4050_ = l_Lean_mkApp4(v___x_4049_, v_prop_4030_, v_expr_4046_, v_a_4048_, v_proof_4031_);
lean_inc(v___x_4043_);
v___x_4051_ = l_Lean_Meta_Grind_add(v_expr_4046_, v___x_4050_, v_generation_4032_, v___x_4043_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_);
if (lean_obj_tag(v___x_4051_) == 0)
{
lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4060_; 
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4060_ == 0)
{
lean_object* v_unused_4061_; 
v_unused_4061_ = lean_ctor_get(v___x_4051_, 0);
lean_dec(v_unused_4061_);
v___x_4053_ = v___x_4051_;
v_isShared_4054_ = v_isSharedCheck_4060_;
goto v_resetjp_4052_;
}
else
{
lean_dec(v___x_4051_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4060_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4058_; 
v___x_4055_ = lean_st_ref_get(v___x_4043_);
v___x_4056_ = lean_st_ref_get(v___x_4043_);
lean_dec(v___x_4043_);
lean_dec(v___x_4056_);
if (v_isShared_4054_ == 0)
{
lean_ctor_set(v___x_4053_, 0, v___x_4055_);
v___x_4058_ = v___x_4053_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v___x_4055_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
}
else
{
lean_object* v_a_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4069_; 
lean_dec(v___x_4043_);
v_a_4062_ = lean_ctor_get(v___x_4051_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4064_ = v___x_4051_;
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_a_4062_);
lean_dec(v___x_4051_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
lean_object* v___x_4067_; 
if (v_isShared_4065_ == 0)
{
v___x_4067_ = v___x_4064_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_a_4062_);
v___x_4067_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
return v___x_4067_;
}
}
}
}
else
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4077_; 
lean_dec_ref(v_expr_4046_);
lean_dec(v___x_4043_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec_ref(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec(v___y_4033_);
lean_dec(v_generation_4032_);
lean_dec_ref(v_proof_4031_);
lean_dec_ref(v_prop_4030_);
v_a_4070_ = lean_ctor_get(v___x_4047_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4072_ = v___x_4047_;
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_4047_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4075_; 
if (v_isShared_4073_ == 0)
{
v___x_4075_ = v___x_4072_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4070_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
}
}
else
{
lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4085_; 
lean_dec(v___x_4043_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec_ref(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec(v___y_4033_);
lean_dec(v_generation_4032_);
lean_dec_ref(v_proof_4031_);
lean_dec_ref(v_prop_4030_);
v_a_4078_ = lean_ctor_get(v___x_4044_, 0);
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_4044_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4080_ = v___x_4044_;
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_dec(v___x_4044_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4083_; 
if (v_isShared_4081_ == 0)
{
v___x_4083_ = v___x_4080_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4078_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed(lean_object* v_goal_4086_, lean_object* v_prop_4087_, lean_object* v_proof_4088_, lean_object* v_generation_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_){
_start:
{
lean_object* v_res_4100_; 
v_res_4100_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(v_goal_4086_, v_prop_4087_, v_proof_4088_, v_generation_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_);
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(lean_object* v_mvarId_4101_, lean_object* v___f_4102_, lean_object* v_kp_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
lean_object* v___x_4114_; 
lean_inc(v___y_4112_);
lean_inc_ref(v___y_4111_);
lean_inc(v___y_4110_);
lean_inc_ref(v___y_4109_);
lean_inc(v___y_4108_);
lean_inc_ref(v___y_4107_);
lean_inc(v___y_4106_);
lean_inc_ref(v___y_4105_);
lean_inc(v___y_4104_);
v___x_4114_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_4101_, v___f_4102_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
if (lean_obj_tag(v___x_4114_) == 0)
{
lean_object* v_a_4115_; lean_object* v___x_4116_; 
v_a_4115_ = lean_ctor_get(v___x_4114_, 0);
lean_inc(v_a_4115_);
lean_dec_ref(v___x_4114_);
v___x_4116_ = lean_apply_11(v_kp_4103_, v_a_4115_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, lean_box(0));
return v___x_4116_;
}
else
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4124_; 
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v_kp_4103_);
v_a_4117_ = lean_ctor_get(v___x_4114_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4114_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4119_ = v___x_4114_;
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4114_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4122_; 
if (v_isShared_4120_ == 0)
{
v___x_4122_ = v___x_4119_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_a_4117_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed(lean_object* v_mvarId_4125_, lean_object* v___f_4126_, lean_object* v_kp_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_){
_start:
{
lean_object* v_res_4138_; 
v_res_4138_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(v_mvarId_4125_, v___f_4126_, v_kp_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
return v_res_4138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(lean_object* v_proof_4139_, lean_object* v_prop_4140_, lean_object* v_generation_4141_, lean_object* v_goal_4142_, lean_object* v_kna_4143_, lean_object* v_kp_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_){
_start:
{
lean_object* v___x_4155_; 
v___x_4155_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_prop_4140_, v_a_4146_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_a_4156_; uint8_t v___x_4157_; 
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_a_4156_);
lean_dec_ref(v___x_4155_);
v___x_4157_ = lean_unbox(v_a_4156_);
lean_dec(v_a_4156_);
if (v___x_4157_ == 0)
{
lean_object* v_mvarId_4158_; lean_object* v___f_4159_; lean_object* v___f_4160_; lean_object* v___x_4161_; 
lean_dec_ref(v_kna_4143_);
v_mvarId_4158_ = lean_ctor_get(v_goal_4142_, 1);
lean_inc(v_mvarId_4158_);
v___f_4159_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed), 14, 4);
lean_closure_set(v___f_4159_, 0, v_goal_4142_);
lean_closure_set(v___f_4159_, 1, v_prop_4140_);
lean_closure_set(v___f_4159_, 2, v_proof_4139_);
lean_closure_set(v___f_4159_, 3, v_generation_4141_);
lean_inc(v_mvarId_4158_);
v___f_4160_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed), 13, 3);
lean_closure_set(v___f_4160_, 0, v_mvarId_4158_);
lean_closure_set(v___f_4160_, 1, v___f_4159_);
lean_closure_set(v___f_4160_, 2, v_kp_4144_);
v___x_4161_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_4158_, v___f_4160_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_, v_a_4153_);
return v___x_4161_;
}
else
{
lean_object* v___x_4162_; lean_object* v___x_4163_; 
v___x_4162_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
lean_inc(v_a_4153_);
lean_inc_ref(v_a_4152_);
v___x_4163_ = l_Lean_Core_mkFreshUserName(v___x_4162_, v_a_4152_, v_a_4153_);
if (lean_obj_tag(v___x_4163_) == 0)
{
lean_object* v_a_4164_; lean_object* v_toGoalState_4165_; lean_object* v_mvarId_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4184_; 
v_a_4164_ = lean_ctor_get(v___x_4163_, 0);
lean_inc(v_a_4164_);
lean_dec_ref(v___x_4163_);
v_toGoalState_4165_ = lean_ctor_get(v_goal_4142_, 0);
v_mvarId_4166_ = lean_ctor_get(v_goal_4142_, 1);
v_isSharedCheck_4184_ = !lean_is_exclusive(v_goal_4142_);
if (v_isSharedCheck_4184_ == 0)
{
v___x_4168_ = v_goal_4142_;
v_isShared_4169_ = v_isSharedCheck_4184_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_mvarId_4166_);
lean_inc(v_toGoalState_4165_);
lean_dec(v_goal_4142_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4184_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4170_; 
lean_inc(v_a_4153_);
lean_inc_ref(v_a_4152_);
lean_inc(v_a_4151_);
lean_inc_ref(v_a_4150_);
v___x_4170_ = l_Lean_MVarId_assert(v_mvarId_4166_, v_a_4164_, v_prop_4140_, v_proof_4139_, v_a_4150_, v_a_4151_, v_a_4152_, v_a_4153_);
if (lean_obj_tag(v___x_4170_) == 0)
{
lean_object* v_a_4171_; lean_object* v___x_4173_; 
v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
lean_inc(v_a_4171_);
lean_dec_ref(v___x_4170_);
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 1, v_a_4171_);
v___x_4173_ = v___x_4168_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_toGoalState_4165_);
lean_ctor_set(v_reuseFailAlloc_4175_, 1, v_a_4171_);
v___x_4173_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
lean_object* v___x_4174_; 
v___x_4174_ = l_Lean_Meta_Grind_Action_intros(v_generation_4141_, v___x_4173_, v_kna_4143_, v_kp_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_, v_a_4153_);
return v___x_4174_;
}
}
else
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4183_; 
lean_del_object(v___x_4168_);
lean_dec_ref(v_toGoalState_4165_);
lean_dec(v_a_4153_);
lean_dec_ref(v_a_4152_);
lean_dec(v_a_4151_);
lean_dec_ref(v_a_4150_);
lean_dec(v_a_4149_);
lean_dec_ref(v_a_4148_);
lean_dec(v_a_4147_);
lean_dec_ref(v_a_4146_);
lean_dec(v_a_4145_);
lean_dec_ref(v_kp_4144_);
lean_dec_ref(v_kna_4143_);
lean_dec(v_generation_4141_);
v_a_4176_ = lean_ctor_get(v___x_4170_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4170_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4178_ = v___x_4170_;
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4170_);
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
}
}
else
{
lean_object* v_a_4185_; lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4192_; 
lean_dec(v_a_4153_);
lean_dec_ref(v_a_4152_);
lean_dec(v_a_4151_);
lean_dec_ref(v_a_4150_);
lean_dec(v_a_4149_);
lean_dec_ref(v_a_4148_);
lean_dec(v_a_4147_);
lean_dec_ref(v_a_4146_);
lean_dec(v_a_4145_);
lean_dec_ref(v_kp_4144_);
lean_dec_ref(v_kna_4143_);
lean_dec_ref(v_goal_4142_);
lean_dec(v_generation_4141_);
lean_dec_ref(v_prop_4140_);
lean_dec_ref(v_proof_4139_);
v_a_4185_ = lean_ctor_get(v___x_4163_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4163_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4187_ = v___x_4163_;
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
else
{
lean_inc(v_a_4185_);
lean_dec(v___x_4163_);
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
}
else
{
lean_object* v_a_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4200_; 
lean_dec(v_a_4153_);
lean_dec_ref(v_a_4152_);
lean_dec(v_a_4151_);
lean_dec_ref(v_a_4150_);
lean_dec(v_a_4149_);
lean_dec_ref(v_a_4148_);
lean_dec(v_a_4147_);
lean_dec_ref(v_a_4146_);
lean_dec(v_a_4145_);
lean_dec_ref(v_kp_4144_);
lean_dec_ref(v_kna_4143_);
lean_dec_ref(v_goal_4142_);
lean_dec(v_generation_4141_);
lean_dec_ref(v_prop_4140_);
lean_dec_ref(v_proof_4139_);
v_a_4193_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4200_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4200_ == 0)
{
v___x_4195_ = v___x_4155_;
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_a_4193_);
lean_dec(v___x_4155_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___boxed(lean_object* v_proof_4201_, lean_object* v_prop_4202_, lean_object* v_generation_4203_, lean_object* v_goal_4204_, lean_object* v_kna_4205_, lean_object* v_kp_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_){
_start:
{
lean_object* v_res_4217_; 
v_res_4217_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(v_proof_4201_, v_prop_4202_, v_generation_4203_, v_goal_4204_, v_kna_4205_, v_kp_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_withSplitSource___at___00Lean_Meta_Grind_Action_assertNext_spec__0___redArg(lean_object* v_splitSource_4218_, lean_object* v_x_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_){
_start:
{
lean_object* v_simp_4230_; lean_object* v_simpMethods_4231_; lean_object* v_config_4232_; lean_object* v_anchorRefs_x3f_4233_; uint8_t v_cheapCases_4234_; uint8_t v_reportMVarIssue_4235_; lean_object* v_symPrios_4236_; lean_object* v_extensions_4237_; uint8_t v_debug_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4246_; 
v_simp_4230_ = lean_ctor_get(v___y_4221_, 0);
v_simpMethods_4231_ = lean_ctor_get(v___y_4221_, 1);
v_config_4232_ = lean_ctor_get(v___y_4221_, 2);
v_anchorRefs_x3f_4233_ = lean_ctor_get(v___y_4221_, 3);
v_cheapCases_4234_ = lean_ctor_get_uint8(v___y_4221_, sizeof(void*)*7);
v_reportMVarIssue_4235_ = lean_ctor_get_uint8(v___y_4221_, sizeof(void*)*7 + 1);
v_symPrios_4236_ = lean_ctor_get(v___y_4221_, 5);
v_extensions_4237_ = lean_ctor_get(v___y_4221_, 6);
v_debug_4238_ = lean_ctor_get_uint8(v___y_4221_, sizeof(void*)*7 + 2);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___y_4221_);
if (v_isSharedCheck_4246_ == 0)
{
lean_object* v_unused_4247_; 
v_unused_4247_ = lean_ctor_get(v___y_4221_, 4);
lean_dec(v_unused_4247_);
v___x_4240_ = v___y_4221_;
v_isShared_4241_ = v_isSharedCheck_4246_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_extensions_4237_);
lean_inc(v_symPrios_4236_);
lean_inc(v_anchorRefs_x3f_4233_);
lean_inc(v_config_4232_);
lean_inc(v_simpMethods_4231_);
lean_inc(v_simp_4230_);
lean_dec(v___y_4221_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4246_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v___x_4243_; 
if (v_isShared_4241_ == 0)
{
lean_ctor_set(v___x_4240_, 4, v_splitSource_4218_);
v___x_4243_ = v___x_4240_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_simp_4230_);
lean_ctor_set(v_reuseFailAlloc_4245_, 1, v_simpMethods_4231_);
lean_ctor_set(v_reuseFailAlloc_4245_, 2, v_config_4232_);
lean_ctor_set(v_reuseFailAlloc_4245_, 3, v_anchorRefs_x3f_4233_);
lean_ctor_set(v_reuseFailAlloc_4245_, 4, v_splitSource_4218_);
lean_ctor_set(v_reuseFailAlloc_4245_, 5, v_symPrios_4236_);
lean_ctor_set(v_reuseFailAlloc_4245_, 6, v_extensions_4237_);
lean_ctor_set_uint8(v_reuseFailAlloc_4245_, sizeof(void*)*7, v_cheapCases_4234_);
lean_ctor_set_uint8(v_reuseFailAlloc_4245_, sizeof(void*)*7 + 1, v_reportMVarIssue_4235_);
lean_ctor_set_uint8(v_reuseFailAlloc_4245_, sizeof(void*)*7 + 2, v_debug_4238_);
v___x_4243_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
lean_object* v___x_4244_; 
v___x_4244_ = lean_apply_10(v_x_4219_, v___y_4220_, v___x_4243_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, lean_box(0));
return v___x_4244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_withSplitSource___at___00Lean_Meta_Grind_Action_assertNext_spec__0___redArg___boxed(lean_object* v_splitSource_4248_, lean_object* v_x_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v_res_4260_; 
v_res_4260_ = l_Lean_Meta_Grind_withSplitSource___at___00Lean_Meta_Grind_Action_assertNext_spec__0___redArg(v_splitSource_4248_, v_x_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
return v_res_4260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_withSplitSource___at___00Lean_Meta_Grind_Action_assertNext_spec__0(lean_object* v_00_u03b1_4261_, lean_object* v_splitSource_4262_, lean_object* v_x_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_){
_start:
{
lean_object* v___x_4274_; 
v___x_4274_ = l_Lean_Meta_Grind_withSplitSource___at___00Lean_Meta_Grind_Action_assertNext_spec__0___redArg(v_splitSource_4262_, v_x_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_);
return v___x_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_withSplitSource___at___00Lean_Meta_Grind_Action_assertNext_spec__0___boxed(lean_object* v_00_u03b1_4275_, lean_object* v_splitSource_4276_, lean_object* v_x_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_){
_start:
{
lean_object* v_res_4288_; 
v_res_4288_ = l_Lean_Meta_Grind_withSplitSource___at___00Lean_Meta_Grind_Action_assertNext_spec__0(v_00_u03b1_4275_, v_splitSource_4276_, v_x_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
return v_res_4288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext(lean_object* v_goal_4289_, lean_object* v_kna_4290_, lean_object* v_kp_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_){
_start:
{
lean_object* v_toGoalState_4302_; uint8_t v_inconsistent_4303_; 
v_toGoalState_4302_ = lean_ctor_get(v_goal_4289_, 0);
lean_inc_ref(v_toGoalState_4302_);
v_inconsistent_4303_ = lean_ctor_get_uint8(v_toGoalState_4302_, sizeof(void*)*18);
if (v_inconsistent_4303_ == 0)
{
lean_object* v_mvarId_4304_; lean_object* v_nextDeclIdx_4305_; lean_object* v_canon_4306_; lean_object* v_enodeMap_4307_; lean_object* v_exprs_4308_; lean_object* v_parents_4309_; lean_object* v_congrTable_4310_; lean_object* v_appMap_4311_; lean_object* v_indicesFound_4312_; lean_object* v_newFacts_4313_; lean_object* v_nextIdx_4314_; lean_object* v_newRawFacts_4315_; lean_object* v_facts_4316_; lean_object* v_extThms_4317_; lean_object* v_ematch_4318_; lean_object* v_inj_4319_; lean_object* v_split_4320_; lean_object* v_clean_4321_; lean_object* v_sstates_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4349_; 
v_mvarId_4304_ = lean_ctor_get(v_goal_4289_, 1);
v_nextDeclIdx_4305_ = lean_ctor_get(v_toGoalState_4302_, 0);
v_canon_4306_ = lean_ctor_get(v_toGoalState_4302_, 1);
v_enodeMap_4307_ = lean_ctor_get(v_toGoalState_4302_, 2);
v_exprs_4308_ = lean_ctor_get(v_toGoalState_4302_, 3);
v_parents_4309_ = lean_ctor_get(v_toGoalState_4302_, 4);
v_congrTable_4310_ = lean_ctor_get(v_toGoalState_4302_, 5);
v_appMap_4311_ = lean_ctor_get(v_toGoalState_4302_, 6);
v_indicesFound_4312_ = lean_ctor_get(v_toGoalState_4302_, 7);
v_newFacts_4313_ = lean_ctor_get(v_toGoalState_4302_, 8);
v_nextIdx_4314_ = lean_ctor_get(v_toGoalState_4302_, 9);
v_newRawFacts_4315_ = lean_ctor_get(v_toGoalState_4302_, 10);
v_facts_4316_ = lean_ctor_get(v_toGoalState_4302_, 11);
v_extThms_4317_ = lean_ctor_get(v_toGoalState_4302_, 12);
v_ematch_4318_ = lean_ctor_get(v_toGoalState_4302_, 13);
v_inj_4319_ = lean_ctor_get(v_toGoalState_4302_, 14);
v_split_4320_ = lean_ctor_get(v_toGoalState_4302_, 15);
v_clean_4321_ = lean_ctor_get(v_toGoalState_4302_, 16);
v_sstates_4322_ = lean_ctor_get(v_toGoalState_4302_, 17);
v_isSharedCheck_4349_ = !lean_is_exclusive(v_toGoalState_4302_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4324_ = v_toGoalState_4302_;
v_isShared_4325_ = v_isSharedCheck_4349_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_sstates_4322_);
lean_inc(v_clean_4321_);
lean_inc(v_split_4320_);
lean_inc(v_inj_4319_);
lean_inc(v_ematch_4318_);
lean_inc(v_extThms_4317_);
lean_inc(v_facts_4316_);
lean_inc(v_newRawFacts_4315_);
lean_inc(v_nextIdx_4314_);
lean_inc(v_newFacts_4313_);
lean_inc(v_indicesFound_4312_);
lean_inc(v_appMap_4311_);
lean_inc(v_congrTable_4310_);
lean_inc(v_parents_4309_);
lean_inc(v_exprs_4308_);
lean_inc(v_enodeMap_4307_);
lean_inc(v_canon_4306_);
lean_inc(v_nextDeclIdx_4305_);
lean_dec(v_toGoalState_4302_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4349_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v___x_4326_; 
v___x_4326_ = l_Std_Queue_dequeue_x3f___redArg(v_newRawFacts_4315_);
if (lean_obj_tag(v___x_4326_) == 1)
{
lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4345_; 
lean_inc(v_mvarId_4304_);
v_isSharedCheck_4345_ = !lean_is_exclusive(v_goal_4289_);
if (v_isSharedCheck_4345_ == 0)
{
lean_object* v_unused_4346_; lean_object* v_unused_4347_; 
v_unused_4346_ = lean_ctor_get(v_goal_4289_, 1);
lean_dec(v_unused_4346_);
v_unused_4347_ = lean_ctor_get(v_goal_4289_, 0);
lean_dec(v_unused_4347_);
v___x_4328_ = v_goal_4289_;
v_isShared_4329_ = v_isSharedCheck_4345_;
goto v_resetjp_4327_;
}
else
{
lean_dec(v_goal_4289_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4345_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v_val_4330_; lean_object* v_fst_4331_; lean_object* v_snd_4332_; lean_object* v_proof_4333_; lean_object* v_prop_4334_; lean_object* v_generation_4335_; lean_object* v_splitSource_4336_; lean_object* v___x_4338_; 
v_val_4330_ = lean_ctor_get(v___x_4326_, 0);
lean_inc(v_val_4330_);
lean_dec_ref(v___x_4326_);
v_fst_4331_ = lean_ctor_get(v_val_4330_, 0);
lean_inc(v_fst_4331_);
v_snd_4332_ = lean_ctor_get(v_val_4330_, 1);
lean_inc(v_snd_4332_);
lean_dec(v_val_4330_);
v_proof_4333_ = lean_ctor_get(v_fst_4331_, 0);
lean_inc_ref(v_proof_4333_);
v_prop_4334_ = lean_ctor_get(v_fst_4331_, 1);
lean_inc_ref(v_prop_4334_);
v_generation_4335_ = lean_ctor_get(v_fst_4331_, 2);
lean_inc(v_generation_4335_);
v_splitSource_4336_ = lean_ctor_get(v_fst_4331_, 3);
lean_inc(v_splitSource_4336_);
lean_dec(v_fst_4331_);
if (v_isShared_4325_ == 0)
{
lean_ctor_set(v___x_4324_, 10, v_snd_4332_);
v___x_4338_ = v___x_4324_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v_nextDeclIdx_4305_);
lean_ctor_set(v_reuseFailAlloc_4344_, 1, v_canon_4306_);
lean_ctor_set(v_reuseFailAlloc_4344_, 2, v_enodeMap_4307_);
lean_ctor_set(v_reuseFailAlloc_4344_, 3, v_exprs_4308_);
lean_ctor_set(v_reuseFailAlloc_4344_, 4, v_parents_4309_);
lean_ctor_set(v_reuseFailAlloc_4344_, 5, v_congrTable_4310_);
lean_ctor_set(v_reuseFailAlloc_4344_, 6, v_appMap_4311_);
lean_ctor_set(v_reuseFailAlloc_4344_, 7, v_indicesFound_4312_);
lean_ctor_set(v_reuseFailAlloc_4344_, 8, v_newFacts_4313_);
lean_ctor_set(v_reuseFailAlloc_4344_, 9, v_nextIdx_4314_);
lean_ctor_set(v_reuseFailAlloc_4344_, 10, v_snd_4332_);
lean_ctor_set(v_reuseFailAlloc_4344_, 11, v_facts_4316_);
lean_ctor_set(v_reuseFailAlloc_4344_, 12, v_extThms_4317_);
lean_ctor_set(v_reuseFailAlloc_4344_, 13, v_ematch_4318_);
lean_ctor_set(v_reuseFailAlloc_4344_, 14, v_inj_4319_);
lean_ctor_set(v_reuseFailAlloc_4344_, 15, v_split_4320_);
lean_ctor_set(v_reuseFailAlloc_4344_, 16, v_clean_4321_);
lean_ctor_set(v_reuseFailAlloc_4344_, 17, v_sstates_4322_);
lean_ctor_set_uint8(v_reuseFailAlloc_4344_, sizeof(void*)*18, v_inconsistent_4303_);
v___x_4338_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
lean_object* v_goal_4340_; 
if (v_isShared_4329_ == 0)
{
lean_ctor_set(v___x_4328_, 0, v___x_4338_);
v_goal_4340_ = v___x_4328_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v___x_4338_);
lean_ctor_set(v_reuseFailAlloc_4343_, 1, v_mvarId_4304_);
v_goal_4340_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
lean_object* v___x_4341_; lean_object* v___x_4342_; 
v___x_4341_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___boxed), 16, 6);
lean_closure_set(v___x_4341_, 0, v_proof_4333_);
lean_closure_set(v___x_4341_, 1, v_prop_4334_);
lean_closure_set(v___x_4341_, 2, v_generation_4335_);
lean_closure_set(v___x_4341_, 3, v_goal_4340_);
lean_closure_set(v___x_4341_, 4, v_kna_4290_);
lean_closure_set(v___x_4341_, 5, v_kp_4291_);
v___x_4342_ = l_Lean_Meta_Grind_withSplitSource___at___00Lean_Meta_Grind_Action_assertNext_spec__0___redArg(v_splitSource_4336_, v___x_4341_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_, v_a_4299_, v_a_4300_);
return v___x_4342_;
}
}
}
}
else
{
lean_object* v___x_4348_; 
lean_dec(v___x_4326_);
lean_del_object(v___x_4324_);
lean_dec_ref(v_sstates_4322_);
lean_dec_ref(v_clean_4321_);
lean_dec_ref(v_split_4320_);
lean_dec_ref(v_inj_4319_);
lean_dec_ref(v_ematch_4318_);
lean_dec_ref(v_extThms_4317_);
lean_dec_ref(v_facts_4316_);
lean_dec(v_nextIdx_4314_);
lean_dec_ref(v_newFacts_4313_);
lean_dec_ref(v_indicesFound_4312_);
lean_dec_ref(v_appMap_4311_);
lean_dec_ref(v_congrTable_4310_);
lean_dec_ref(v_parents_4309_);
lean_dec_ref(v_exprs_4308_);
lean_dec_ref(v_enodeMap_4307_);
lean_dec_ref(v_canon_4306_);
lean_dec(v_nextDeclIdx_4305_);
lean_dec_ref(v_kp_4291_);
v___x_4348_ = lean_apply_11(v_kna_4290_, v_goal_4289_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_, v_a_4299_, v_a_4300_, lean_box(0));
return v___x_4348_;
}
}
}
else
{
lean_object* v___x_4350_; lean_object* v___x_4351_; 
lean_dec_ref(v_toGoalState_4302_);
lean_dec(v_a_4300_);
lean_dec_ref(v_a_4299_);
lean_dec(v_a_4298_);
lean_dec_ref(v_a_4297_);
lean_dec(v_a_4296_);
lean_dec_ref(v_a_4295_);
lean_dec(v_a_4294_);
lean_dec_ref(v_a_4293_);
lean_dec(v_a_4292_);
lean_dec_ref(v_kp_4291_);
lean_dec_ref(v_kna_4290_);
lean_dec_ref(v_goal_4289_);
v___x_4350_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intro___closed__0));
v___x_4351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4351_, 0, v___x_4350_);
return v___x_4351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext___boxed(lean_object* v_goal_4352_, lean_object* v_kna_4353_, lean_object* v_kp_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l_Lean_Meta_Grind_Action_assertNext(v_goal_4352_, v_kna_4353_, v_kp_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_);
return v_res_4365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg(lean_object* v_a_4366_, lean_object* v_kp_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_){
_start:
{
lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; 
v___x_4378_ = lean_unsigned_to_nat(1000000u);
v___x_4379_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_assertNext___boxed), 13, 0);
v___x_4380_ = l_Lean_Meta_Grind_Action_loop___redArg(v___x_4378_, v___x_4379_, v_a_4366_, v_kp_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg___boxed(lean_object* v_a_4381_, lean_object* v_kp_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_){
_start:
{
lean_object* v_res_4393_; 
v_res_4393_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4381_, v_kp_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_);
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll(lean_object* v_a_4394_, lean_object* v_kna_4395_, lean_object* v_kp_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_){
_start:
{
lean_object* v___x_4407_; 
v___x_4407_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4394_, v_kp_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_);
return v___x_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___boxed(lean_object* v_a_4408_, lean_object* v_kna_4409_, lean_object* v_kp_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_){
_start:
{
lean_object* v_res_4421_; 
v_res_4421_ = l_Lean_Meta_Grind_Action_assertAll(v_a_4408_, v_kna_4409_, v_kp_4410_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_);
lean_dec_ref(v_kna_4409_);
return v_res_4421_;
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
