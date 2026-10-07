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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
lean_object* l_Lean_Meta_expandLet(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
uint8_t l_Lean_Expr_bindingInfo_x21(lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_simpCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_byContra_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
size_t v_x_32928__boxed_287_; uint8_t v_res_288_; lean_object* v_r_289_; 
v_x_32928__boxed_287_ = lean_unbox_usize(v_x_285_);
lean_dec(v_x_285_);
v_res_288_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_284_, v_x_32928__boxed_287_, v_x_286_);
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
v_clean_315_ = lean_ctor_get(v_toGoalState_314_, 15);
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
size_t v_x_33108__boxed_475_; size_t v_x_33109__boxed_476_; lean_object* v_res_477_; 
v_x_33108__boxed_475_ = lean_unbox_usize(v_x_471_);
lean_dec(v_x_471_);
v_x_33109__boxed_476_ = lean_unbox_usize(v_x_472_);
lean_dec(v_x_472_);
v_res_477_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_470_, v_x_33108__boxed_475_, v_x_33109__boxed_476_, v_x_473_, v_x_474_);
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
size_t v_x_33298__boxed_533_; lean_object* v_res_534_; 
v_x_33298__boxed_533_ = lean_unbox_usize(v_x_531_);
lean_dec(v_x_531_);
v_res_534_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_530_, v_x_33298__boxed_533_, v_x_532_);
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
lean_object* v_name_563_; lean_object* v___y_564_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v_name_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___x_716_; 
v___x_716_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_553_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_777_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_777_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_777_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_777_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
uint8_t v_clean_742_; 
v_clean_742_ = lean_ctor_get_uint8(v_a_717_, sizeof(void*)*14 + 16);
lean_dec(v_a_717_);
if (v_clean_742_ == 0)
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Meta_Grind_getOriginalName_x3f(v_name_549_);
if (lean_obj_tag(v___x_743_) == 1)
{
lean_object* v_val_744_; lean_object* v___x_746_; 
lean_dec_ref(v_type_550_);
lean_dec(v_name_549_);
v_val_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_val_744_);
lean_dec_ref_known(v___x_743_, 1);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v_val_744_);
v___x_746_ = v___x_719_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_val_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
else
{
uint8_t v___x_748_; 
lean_dec(v___x_743_);
v___x_748_ = l_Lean_Name_hasMacroScopes(v_name_549_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; 
lean_del_object(v___x_719_);
lean_dec_ref(v_type_550_);
v___x_749_ = l_Lean_Core_mkFreshUserName(v_name_549_, v_a_559_, v_a_560_);
return v___x_749_;
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_750_ = l_Lean_Name_eraseMacroScopes(v_name_549_);
v___x_751_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
v___x_752_ = lean_name_eq(v___x_750_, v___x_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; uint8_t v___x_754_; 
v___x_753_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1));
v___x_754_ = lean_name_eq(v___x_750_, v___x_753_);
lean_dec(v___x_750_);
if (v___x_754_ == 0)
{
lean_object* v___x_756_; 
lean_dec_ref(v_type_550_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v_name_549_);
v___x_756_ = v___x_719_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_name_549_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
else
{
lean_del_object(v___x_719_);
goto v___jp_721_;
}
}
else
{
lean_dec(v___x_750_);
lean_del_object(v___x_719_);
goto v___jp_721_;
}
}
}
}
else
{
uint8_t v___x_758_; 
lean_del_object(v___x_719_);
v___x_758_ = l_Lean_Name_hasMacroScopes(v_name_549_);
if (v___x_758_ == 0)
{
v_name_691_ = v_name_549_;
v___y_692_ = v_a_551_;
v___y_693_ = v_a_552_;
v___y_694_ = v_a_553_;
v___y_695_ = v_a_554_;
v___y_696_ = v_a_555_;
v___y_697_ = v_a_556_;
v___y_698_ = v_a_557_;
v___y_699_ = v_a_558_;
v___y_700_ = v_a_559_;
v___y_701_ = v_a_560_;
goto v___jp_690_;
}
else
{
lean_object* v___x_759_; lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_759_ = l_Lean_Name_eraseMacroScopes(v_name_549_);
lean_dec(v_name_549_);
v___x_773_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
v___x_774_ = lean_name_eq(v___x_759_, v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1));
v___x_776_ = lean_name_eq(v___x_759_, v___x_775_);
if (v___x_776_ == 0)
{
v_name_691_ = v___x_759_;
v___y_692_ = v_a_551_;
v___y_693_ = v_a_552_;
v___y_694_ = v_a_553_;
v___y_695_ = v_a_554_;
v___y_696_ = v_a_555_;
v___y_697_ = v_a_556_;
v___y_698_ = v_a_557_;
v___y_699_ = v_a_558_;
v___y_700_ = v_a_559_;
v___y_701_ = v_a_560_;
goto v___jp_690_;
}
else
{
goto v___jp_760_;
}
}
else
{
goto v___jp_760_;
}
v___jp_760_:
{
lean_object* v___x_761_; 
lean_inc_ref(v_type_550_);
v___x_761_ = l_Lean_Meta_isProp(v_type_550_, v_a_557_, v_a_558_, v_a_559_, v_a_560_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; uint8_t v___x_763_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___x_761_, 1);
v___x_763_ = lean_unbox(v_a_762_);
lean_dec(v_a_762_);
if (v___x_763_ == 0)
{
v_name_691_ = v___x_759_;
v___y_692_ = v_a_551_;
v___y_693_ = v_a_552_;
v___y_694_ = v_a_553_;
v___y_695_ = v_a_554_;
v___y_696_ = v_a_555_;
v___y_697_ = v_a_556_;
v___y_698_ = v_a_557_;
v___y_699_ = v_a_558_;
v___y_700_ = v_a_559_;
v___y_701_ = v_a_560_;
goto v___jp_690_;
}
else
{
lean_object* v___x_764_; 
lean_dec(v___x_759_);
v___x_764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v_name_691_ = v___x_764_;
v___y_692_ = v_a_551_;
v___y_693_ = v_a_552_;
v___y_694_ = v_a_553_;
v___y_695_ = v_a_554_;
v___y_696_ = v_a_555_;
v___y_697_ = v_a_556_;
v___y_698_ = v_a_557_;
v___y_699_ = v_a_558_;
v___y_700_ = v_a_559_;
v___y_701_ = v_a_560_;
goto v___jp_690_;
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec(v___x_759_);
lean_dec_ref(v_type_550_);
v_a_765_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_761_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_761_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
}
v___jp_721_:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_Meta_isProp(v_type_550_, v_a_557_, v_a_558_, v_a_559_, v_a_560_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_733_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_733_ == 0)
{
v___x_725_ = v___x_722_;
v_isShared_726_ = v_isSharedCheck_733_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_733_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
uint8_t v___x_727_; 
v___x_727_ = lean_unbox(v_a_723_);
lean_dec(v_a_723_);
if (v___x_727_ == 0)
{
lean_object* v___x_729_; 
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v_name_549_);
v___x_729_ = v___x_725_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_name_549_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; 
lean_del_object(v___x_725_);
lean_dec(v_name_549_);
v___x_731_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v___x_732_ = l_Lean_Core_mkFreshUserName(v___x_731_, v_a_559_, v_a_560_);
return v___x_732_;
}
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec(v_name_549_);
v_a_734_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_722_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_722_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec_ref(v_type_550_);
lean_dec(v_name_549_);
v_a_778_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_716_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_716_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
v___jp_562_:
{
lean_object* v___x_565_; lean_object* v_toGoalState_566_; lean_object* v_clean_567_; lean_object* v_mvarId_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_613_; 
v___x_565_ = lean_st_ref_take(v___y_564_);
v_toGoalState_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc_ref(v_toGoalState_566_);
v_clean_567_ = lean_ctor_get(v_toGoalState_566_, 15);
lean_inc_ref(v_clean_567_);
v_mvarId_568_ = lean_ctor_get(v___x_565_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; 
v_unused_614_ = lean_ctor_get(v___x_565_, 0);
lean_dec(v_unused_614_);
v___x_570_ = v___x_565_;
v_isShared_571_ = v_isSharedCheck_613_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_mvarId_568_);
lean_dec(v___x_565_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_613_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v_nextDeclIdx_572_; lean_object* v_enodeMap_573_; lean_object* v_exprs_574_; lean_object* v_parents_575_; lean_object* v_congrTable_576_; lean_object* v_appMap_577_; lean_object* v_indicesFound_578_; lean_object* v_newFacts_579_; uint8_t v_inconsistent_580_; lean_object* v_nextIdx_581_; lean_object* v_newRawFacts_582_; lean_object* v_facts_583_; lean_object* v_extThms_584_; lean_object* v_ematch_585_; lean_object* v_inj_586_; lean_object* v_split_587_; lean_object* v_sstates_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_611_; 
v_nextDeclIdx_572_ = lean_ctor_get(v_toGoalState_566_, 0);
v_enodeMap_573_ = lean_ctor_get(v_toGoalState_566_, 1);
v_exprs_574_ = lean_ctor_get(v_toGoalState_566_, 2);
v_parents_575_ = lean_ctor_get(v_toGoalState_566_, 3);
v_congrTable_576_ = lean_ctor_get(v_toGoalState_566_, 4);
v_appMap_577_ = lean_ctor_get(v_toGoalState_566_, 5);
v_indicesFound_578_ = lean_ctor_get(v_toGoalState_566_, 6);
v_newFacts_579_ = lean_ctor_get(v_toGoalState_566_, 7);
v_inconsistent_580_ = lean_ctor_get_uint8(v_toGoalState_566_, sizeof(void*)*17);
v_nextIdx_581_ = lean_ctor_get(v_toGoalState_566_, 8);
v_newRawFacts_582_ = lean_ctor_get(v_toGoalState_566_, 9);
v_facts_583_ = lean_ctor_get(v_toGoalState_566_, 10);
v_extThms_584_ = lean_ctor_get(v_toGoalState_566_, 11);
v_ematch_585_ = lean_ctor_get(v_toGoalState_566_, 12);
v_inj_586_ = lean_ctor_get(v_toGoalState_566_, 13);
v_split_587_ = lean_ctor_get(v_toGoalState_566_, 14);
v_sstates_588_ = lean_ctor_get(v_toGoalState_566_, 16);
v_isSharedCheck_611_ = !lean_is_exclusive(v_toGoalState_566_);
if (v_isSharedCheck_611_ == 0)
{
lean_object* v_unused_612_; 
v_unused_612_ = lean_ctor_get(v_toGoalState_566_, 15);
lean_dec(v_unused_612_);
v___x_590_ = v_toGoalState_566_;
v_isShared_591_ = v_isSharedCheck_611_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_sstates_588_);
lean_inc(v_split_587_);
lean_inc(v_inj_586_);
lean_inc(v_ematch_585_);
lean_inc(v_extThms_584_);
lean_inc(v_facts_583_);
lean_inc(v_newRawFacts_582_);
lean_inc(v_nextIdx_581_);
lean_inc(v_newFacts_579_);
lean_inc(v_indicesFound_578_);
lean_inc(v_appMap_577_);
lean_inc(v_congrTable_576_);
lean_inc(v_parents_575_);
lean_inc(v_exprs_574_);
lean_inc(v_enodeMap_573_);
lean_inc(v_nextDeclIdx_572_);
lean_dec(v_toGoalState_566_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_611_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v_used_592_; lean_object* v_next_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_610_; 
v_used_592_ = lean_ctor_get(v_clean_567_, 0);
v_next_593_ = lean_ctor_get(v_clean_567_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v_clean_567_);
if (v_isSharedCheck_610_ == 0)
{
v___x_595_ = v_clean_567_;
v_isShared_596_ = v_isSharedCheck_610_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_next_593_);
lean_inc(v_used_592_);
lean_dec(v_clean_567_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_610_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_597_ = lean_box(0);
lean_inc(v_name_563_);
v___x_598_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_used_592_, v_name_563_, v___x_597_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_598_);
v___x_600_ = v___x_595_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_next_593_);
v___x_600_ = v_reuseFailAlloc_609_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_602_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 15, v___x_600_);
v___x_602_ = v___x_590_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_nextDeclIdx_572_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_enodeMap_573_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v_exprs_574_);
lean_ctor_set(v_reuseFailAlloc_608_, 3, v_parents_575_);
lean_ctor_set(v_reuseFailAlloc_608_, 4, v_congrTable_576_);
lean_ctor_set(v_reuseFailAlloc_608_, 5, v_appMap_577_);
lean_ctor_set(v_reuseFailAlloc_608_, 6, v_indicesFound_578_);
lean_ctor_set(v_reuseFailAlloc_608_, 7, v_newFacts_579_);
lean_ctor_set(v_reuseFailAlloc_608_, 8, v_nextIdx_581_);
lean_ctor_set(v_reuseFailAlloc_608_, 9, v_newRawFacts_582_);
lean_ctor_set(v_reuseFailAlloc_608_, 10, v_facts_583_);
lean_ctor_set(v_reuseFailAlloc_608_, 11, v_extThms_584_);
lean_ctor_set(v_reuseFailAlloc_608_, 12, v_ematch_585_);
lean_ctor_set(v_reuseFailAlloc_608_, 13, v_inj_586_);
lean_ctor_set(v_reuseFailAlloc_608_, 14, v_split_587_);
lean_ctor_set(v_reuseFailAlloc_608_, 15, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_608_, 16, v_sstates_588_);
lean_ctor_set_uint8(v_reuseFailAlloc_608_, sizeof(void*)*17, v_inconsistent_580_);
v___x_602_ = v_reuseFailAlloc_608_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_604_; 
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_602_);
v___x_604_ = v___x_570_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_mvarId_568_);
v___x_604_ = v_reuseFailAlloc_607_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_st_ref_put(v___y_564_, v___x_604_);
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v_name_563_);
return v___x_606_;
}
}
}
}
}
}
}
v___jp_615_:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v___y_621_);
lean_ctor_set(v___x_629_, 1, v___y_628_);
lean_inc(v___y_625_);
v___x_630_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v___y_625_, v___x_629_, v___y_622_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v_fst_632_; lean_object* v_snd_633_; lean_object* v___x_634_; lean_object* v_toGoalState_635_; lean_object* v_clean_636_; lean_object* v_mvarId_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_680_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref_known(v___x_630_, 1);
v_fst_632_ = lean_ctor_get(v_a_631_, 0);
lean_inc(v_fst_632_);
v_snd_633_ = lean_ctor_get(v_a_631_, 1);
lean_inc(v_snd_633_);
lean_dec(v_a_631_);
v___x_634_ = lean_st_ref_take(v___y_622_);
v_toGoalState_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc_ref(v_toGoalState_635_);
v_clean_636_ = lean_ctor_get(v_toGoalState_635_, 15);
lean_inc_ref(v_clean_636_);
v_mvarId_637_ = lean_ctor_get(v___x_634_, 1);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_680_ == 0)
{
lean_object* v_unused_681_; 
v_unused_681_ = lean_ctor_get(v___x_634_, 0);
lean_dec(v_unused_681_);
v___x_639_ = v___x_634_;
v_isShared_640_ = v_isSharedCheck_680_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_mvarId_637_);
lean_dec(v___x_634_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_680_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v_nextDeclIdx_641_; lean_object* v_enodeMap_642_; lean_object* v_exprs_643_; lean_object* v_parents_644_; lean_object* v_congrTable_645_; lean_object* v_appMap_646_; lean_object* v_indicesFound_647_; lean_object* v_newFacts_648_; uint8_t v_inconsistent_649_; lean_object* v_nextIdx_650_; lean_object* v_newRawFacts_651_; lean_object* v_facts_652_; lean_object* v_extThms_653_; lean_object* v_ematch_654_; lean_object* v_inj_655_; lean_object* v_split_656_; lean_object* v_sstates_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_678_; 
v_nextDeclIdx_641_ = lean_ctor_get(v_toGoalState_635_, 0);
v_enodeMap_642_ = lean_ctor_get(v_toGoalState_635_, 1);
v_exprs_643_ = lean_ctor_get(v_toGoalState_635_, 2);
v_parents_644_ = lean_ctor_get(v_toGoalState_635_, 3);
v_congrTable_645_ = lean_ctor_get(v_toGoalState_635_, 4);
v_appMap_646_ = lean_ctor_get(v_toGoalState_635_, 5);
v_indicesFound_647_ = lean_ctor_get(v_toGoalState_635_, 6);
v_newFacts_648_ = lean_ctor_get(v_toGoalState_635_, 7);
v_inconsistent_649_ = lean_ctor_get_uint8(v_toGoalState_635_, sizeof(void*)*17);
v_nextIdx_650_ = lean_ctor_get(v_toGoalState_635_, 8);
v_newRawFacts_651_ = lean_ctor_get(v_toGoalState_635_, 9);
v_facts_652_ = lean_ctor_get(v_toGoalState_635_, 10);
v_extThms_653_ = lean_ctor_get(v_toGoalState_635_, 11);
v_ematch_654_ = lean_ctor_get(v_toGoalState_635_, 12);
v_inj_655_ = lean_ctor_get(v_toGoalState_635_, 13);
v_split_656_ = lean_ctor_get(v_toGoalState_635_, 14);
v_sstates_657_ = lean_ctor_get(v_toGoalState_635_, 16);
v_isSharedCheck_678_ = !lean_is_exclusive(v_toGoalState_635_);
if (v_isSharedCheck_678_ == 0)
{
lean_object* v_unused_679_; 
v_unused_679_ = lean_ctor_get(v_toGoalState_635_, 15);
lean_dec(v_unused_679_);
v___x_659_ = v_toGoalState_635_;
v_isShared_660_ = v_isSharedCheck_678_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_sstates_657_);
lean_inc(v_split_656_);
lean_inc(v_inj_655_);
lean_inc(v_ematch_654_);
lean_inc(v_extThms_653_);
lean_inc(v_facts_652_);
lean_inc(v_newRawFacts_651_);
lean_inc(v_nextIdx_650_);
lean_inc(v_newFacts_648_);
lean_inc(v_indicesFound_647_);
lean_inc(v_appMap_646_);
lean_inc(v_congrTable_645_);
lean_inc(v_parents_644_);
lean_inc(v_exprs_643_);
lean_inc(v_enodeMap_642_);
lean_inc(v_nextDeclIdx_641_);
lean_dec(v_toGoalState_635_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_678_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v_used_661_; lean_object* v_next_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_677_; 
v_used_661_ = lean_ctor_get(v_clean_636_, 0);
v_next_662_ = lean_ctor_get(v_clean_636_, 1);
v_isSharedCheck_677_ = !lean_is_exclusive(v_clean_636_);
if (v_isSharedCheck_677_ == 0)
{
v___x_664_ = v_clean_636_;
v_isShared_665_ = v_isSharedCheck_677_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_next_662_);
lean_inc(v_used_661_);
lean_dec(v_clean_636_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_677_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_666_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_next_662_, v___y_625_, v_snd_633_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 1, v___x_666_);
v___x_668_ = v___x_664_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_used_661_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v___x_666_);
v___x_668_ = v_reuseFailAlloc_676_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_670_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 15, v___x_668_);
v___x_670_ = v___x_659_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_nextDeclIdx_641_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_enodeMap_642_);
lean_ctor_set(v_reuseFailAlloc_675_, 2, v_exprs_643_);
lean_ctor_set(v_reuseFailAlloc_675_, 3, v_parents_644_);
lean_ctor_set(v_reuseFailAlloc_675_, 4, v_congrTable_645_);
lean_ctor_set(v_reuseFailAlloc_675_, 5, v_appMap_646_);
lean_ctor_set(v_reuseFailAlloc_675_, 6, v_indicesFound_647_);
lean_ctor_set(v_reuseFailAlloc_675_, 7, v_newFacts_648_);
lean_ctor_set(v_reuseFailAlloc_675_, 8, v_nextIdx_650_);
lean_ctor_set(v_reuseFailAlloc_675_, 9, v_newRawFacts_651_);
lean_ctor_set(v_reuseFailAlloc_675_, 10, v_facts_652_);
lean_ctor_set(v_reuseFailAlloc_675_, 11, v_extThms_653_);
lean_ctor_set(v_reuseFailAlloc_675_, 12, v_ematch_654_);
lean_ctor_set(v_reuseFailAlloc_675_, 13, v_inj_655_);
lean_ctor_set(v_reuseFailAlloc_675_, 14, v_split_656_);
lean_ctor_set(v_reuseFailAlloc_675_, 15, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_675_, 16, v_sstates_657_);
lean_ctor_set_uint8(v_reuseFailAlloc_675_, sizeof(void*)*17, v_inconsistent_649_);
v___x_670_ = v_reuseFailAlloc_675_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_672_; 
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_670_);
v___x_672_ = v___x_639_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_mvarId_637_);
v___x_672_ = v_reuseFailAlloc_674_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_673_; 
v___x_673_ = lean_st_ref_put(v___y_622_, v___x_672_);
v_name_563_ = v_fst_632_;
v___y_564_ = v___y_622_;
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
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec(v___y_625_);
v_a_682_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_630_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_630_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
v___jp_690_:
{
lean_object* v___x_702_; lean_object* v_toGoalState_703_; lean_object* v_clean_704_; lean_object* v_used_705_; uint8_t v___x_706_; 
v___x_702_ = lean_st_ref_get(v___y_692_);
v_toGoalState_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc_ref(v_toGoalState_703_);
lean_dec(v___x_702_);
v_clean_704_ = lean_ctor_get(v_toGoalState_703_, 15);
lean_inc_ref(v_clean_704_);
lean_dec_ref(v_toGoalState_703_);
v_used_705_ = lean_ctor_get(v_clean_704_, 0);
lean_inc_ref(v_used_705_);
lean_dec_ref(v_clean_704_);
v___x_706_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_used_705_, v_name_691_);
lean_dec_ref(v_used_705_);
if (v___x_706_ == 0)
{
lean_dec_ref(v_type_550_);
v_name_563_ = v_name_691_;
v___y_564_ = v___y_692_;
goto v___jp_562_;
}
else
{
lean_object* v___x_707_; 
lean_inc(v_name_691_);
v___x_707_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(v_name_691_, v_type_550_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_709_; lean_object* v_toGoalState_710_; lean_object* v_clean_711_; lean_object* v_next_712_; lean_object* v___x_713_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref_known(v___x_707_, 1);
v___x_709_ = lean_st_ref_get(v___y_692_);
v_toGoalState_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc_ref(v_toGoalState_710_);
lean_dec(v___x_709_);
v_clean_711_ = lean_ctor_get(v_toGoalState_710_, 15);
lean_inc_ref(v_clean_711_);
lean_dec_ref(v_toGoalState_710_);
v_next_712_ = lean_ctor_get(v_clean_711_, 1);
lean_inc_ref(v_next_712_);
lean_dec_ref(v_clean_711_);
v___x_713_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_next_712_, v_a_708_);
lean_dec_ref(v_next_712_);
if (lean_obj_tag(v___x_713_) == 1)
{
lean_object* v_val_714_; 
v_val_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_val_714_);
lean_dec_ref_known(v___x_713_, 1);
v___y_616_ = v___y_693_;
v___y_617_ = v___y_696_;
v___y_618_ = v___y_699_;
v___y_619_ = v___y_698_;
v___y_620_ = v___y_700_;
v___y_621_ = v_name_691_;
v___y_622_ = v___y_692_;
v___y_623_ = v___y_697_;
v___y_624_ = v___y_695_;
v___y_625_ = v_a_708_;
v___y_626_ = v___y_694_;
v___y_627_ = v___y_701_;
v___y_628_ = v_val_714_;
goto v___jp_615_;
}
else
{
lean_object* v___x_715_; 
lean_dec(v___x_713_);
v___x_715_ = lean_unsigned_to_nat(1u);
v___y_616_ = v___y_693_;
v___y_617_ = v___y_696_;
v___y_618_ = v___y_699_;
v___y_619_ = v___y_698_;
v___y_620_ = v___y_700_;
v___y_621_ = v_name_691_;
v___y_622_ = v___y_692_;
v___y_623_ = v___y_697_;
v___y_624_ = v___y_695_;
v___y_625_ = v_a_708_;
v___y_626_ = v___y_694_;
v___y_627_ = v___y_701_;
v___y_628_ = v___x_715_;
goto v___jp_615_;
}
}
else
{
lean_dec(v_name_691_);
return v___x_707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___boxed(lean_object* v_name_786_, lean_object* v_type_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v_name_786_, v_type_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec(v_a_788_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0(lean_object* v_00_u03b2_800_, lean_object* v_x_801_, lean_object* v_x_802_, lean_object* v_x_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_x_801_, v_x_802_, v_x_803_);
return v___x_804_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(lean_object* v_00_u03b2_805_, lean_object* v_x_806_, lean_object* v_x_807_){
_start:
{
uint8_t v___x_808_; 
v___x_808_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_x_806_, v_x_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___boxed(lean_object* v_00_u03b2_809_, lean_object* v_x_810_, lean_object* v_x_811_){
_start:
{
uint8_t v_res_812_; lean_object* v_r_813_; 
v_res_812_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(v_00_u03b2_809_, v_x_810_, v_x_811_);
lean_dec(v_x_811_);
lean_dec_ref(v_x_810_);
v_r_813_ = lean_box(v_res_812_);
return v_r_813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(lean_object* v_a_814_, lean_object* v_inst_815_, lean_object* v_a_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v_a_814_, v_a_816_, v___y_817_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___boxed(lean_object* v_a_829_, lean_object* v_inst_830_, lean_object* v_a_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(v_a_829_, v_inst_830_, v_a_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec(v___y_832_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(lean_object* v_00_u03b2_844_, lean_object* v_x_845_, lean_object* v_x_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_x_845_, v_x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___boxed(lean_object* v_00_u03b2_848_, lean_object* v_x_849_, lean_object* v_x_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(v_00_u03b2_848_, v_x_849_, v_x_850_);
lean_dec(v_x_850_);
lean_dec_ref(v_x_849_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(lean_object* v_00_u03b2_852_, lean_object* v_x_853_, size_t v_x_854_, size_t v_x_855_, lean_object* v_x_856_, lean_object* v_x_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_853_, v_x_854_, v_x_855_, v_x_856_, v_x_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___boxed(lean_object* v_00_u03b2_859_, lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_x_862_, lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
size_t v_x_33792__boxed_865_; size_t v_x_33793__boxed_866_; lean_object* v_res_867_; 
v_x_33792__boxed_865_ = lean_unbox_usize(v_x_861_);
lean_dec(v_x_861_);
v_x_33793__boxed_866_ = lean_unbox_usize(v_x_862_);
lean_dec(v_x_862_);
v_res_867_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(v_00_u03b2_859_, v_x_860_, v_x_33792__boxed_865_, v_x_33793__boxed_866_, v_x_863_, v_x_864_);
return v_res_867_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(lean_object* v_00_u03b2_868_, lean_object* v_x_869_, size_t v_x_870_, lean_object* v_x_871_){
_start:
{
uint8_t v___x_872_; 
v___x_872_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_869_, v_x_870_, v_x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___boxed(lean_object* v_00_u03b2_873_, lean_object* v_x_874_, lean_object* v_x_875_, lean_object* v_x_876_){
_start:
{
size_t v_x_33809__boxed_877_; uint8_t v_res_878_; lean_object* v_r_879_; 
v_x_33809__boxed_877_ = lean_unbox_usize(v_x_875_);
lean_dec(v_x_875_);
v_res_878_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(v_00_u03b2_873_, v_x_874_, v_x_33809__boxed_877_, v_x_876_);
lean_dec(v_x_876_);
lean_dec_ref(v_x_874_);
v_r_879_ = lean_box(v_res_878_);
return v_r_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(lean_object* v_00_u03b2_880_, lean_object* v_x_881_, size_t v_x_882_, lean_object* v_x_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_881_, v_x_882_, v_x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___boxed(lean_object* v_00_u03b2_885_, lean_object* v_x_886_, lean_object* v_x_887_, lean_object* v_x_888_){
_start:
{
size_t v_x_33820__boxed_889_; lean_object* v_res_890_; 
v_x_33820__boxed_889_ = lean_unbox_usize(v_x_887_);
lean_dec(v_x_887_);
v_res_890_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(v_00_u03b2_885_, v_x_886_, v_x_33820__boxed_889_, v_x_888_);
lean_dec(v_x_888_);
lean_dec_ref(v_x_886_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_891_, lean_object* v_n_892_, lean_object* v_k_893_, lean_object* v_v_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(v_n_892_, v_k_893_, v_v_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_896_, size_t v_depth_897_, lean_object* v_keys_898_, lean_object* v_vals_899_, lean_object* v_heq_900_, lean_object* v_i_901_, lean_object* v_entries_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_depth_897_, v_keys_898_, v_vals_899_, v_i_901_, v_entries_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_904_, lean_object* v_depth_905_, lean_object* v_keys_906_, lean_object* v_vals_907_, lean_object* v_heq_908_, lean_object* v_i_909_, lean_object* v_entries_910_){
_start:
{
size_t v_depth_boxed_911_; lean_object* v_res_912_; 
v_depth_boxed_911_ = lean_unbox_usize(v_depth_905_);
lean_dec(v_depth_905_);
v_res_912_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(v_00_u03b2_904_, v_depth_boxed_911_, v_keys_906_, v_vals_907_, v_heq_908_, v_i_909_, v_entries_910_);
lean_dec_ref(v_vals_907_);
lean_dec_ref(v_keys_906_);
return v_res_912_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_913_, lean_object* v_keys_914_, lean_object* v_vals_915_, lean_object* v_heq_916_, lean_object* v_i_917_, lean_object* v_k_918_){
_start:
{
uint8_t v___x_919_; 
v___x_919_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_keys_914_, v_i_917_, v_k_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_920_, lean_object* v_keys_921_, lean_object* v_vals_922_, lean_object* v_heq_923_, lean_object* v_i_924_, lean_object* v_k_925_){
_start:
{
uint8_t v_res_926_; lean_object* v_r_927_; 
v_res_926_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(v_00_u03b2_920_, v_keys_921_, v_vals_922_, v_heq_923_, v_i_924_, v_k_925_);
lean_dec(v_k_925_);
lean_dec_ref(v_vals_922_);
lean_dec_ref(v_keys_921_);
v_r_927_ = lean_box(v_res_926_);
return v_r_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_928_, lean_object* v_keys_929_, lean_object* v_vals_930_, lean_object* v_heq_931_, lean_object* v_i_932_, lean_object* v_k_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_keys_929_, v_vals_930_, v_i_932_, v_k_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_935_, lean_object* v_keys_936_, lean_object* v_vals_937_, lean_object* v_heq_938_, lean_object* v_i_939_, lean_object* v_k_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(v_00_u03b2_935_, v_keys_936_, v_vals_937_, v_heq_938_, v_i_939_, v_k_940_);
lean_dec(v_k_940_);
lean_dec_ref(v_vals_937_);
lean_dec_ref(v_keys_936_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_942_, lean_object* v_x_943_, lean_object* v_x_944_, lean_object* v_x_945_, lean_object* v_x_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(v_x_943_, v_x_944_, v_x_945_, v_x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(lean_object* v_msgData_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v___x_954_; lean_object* v_env_955_; uint8_t v___x_956_; lean_object* v_env_957_; lean_object* v___x_958_; lean_object* v_toCold_959_; lean_object* v_mctx_960_; lean_object* v_lctx_961_; lean_object* v_options_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_954_ = lean_st_ref_get(v___y_952_);
v_env_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc_ref(v_env_955_);
lean_dec(v___x_954_);
v___x_956_ = 0;
v_env_957_ = l_Lean_Environment_setRecordingDeps(v_env_955_, v___x_956_);
v___x_958_ = lean_st_ref_get(v___y_950_);
v_toCold_959_ = lean_ctor_get(v___y_951_, 0);
v_mctx_960_ = lean_ctor_get(v___x_958_, 0);
lean_inc_ref(v_mctx_960_);
lean_dec(v___x_958_);
v_lctx_961_ = lean_ctor_get(v___y_949_, 2);
v_options_962_ = lean_ctor_get(v_toCold_959_, 2);
lean_inc_ref(v_options_962_);
lean_inc_ref(v_lctx_961_);
v___x_963_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_963_, 0, v_env_957_);
lean_ctor_set(v___x_963_, 1, v_mctx_960_);
lean_ctor_set(v___x_963_, 2, v_lctx_961_);
lean_ctor_set(v___x_963_, 3, v_options_962_);
v___x_964_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v_msgData_948_);
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
v_ref_979_ = lean_ctor_get(v___y_976_, 2);
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
size_t v_x_151839__boxed_1604_; size_t v_x_151840__boxed_1605_; lean_object* v_res_1606_; 
v_x_151839__boxed_1604_ = lean_unbox_usize(v_x_1600_);
lean_dec(v_x_1600_);
v_x_151840__boxed_1605_ = lean_unbox_usize(v_x_1601_);
lean_dec(v_x_1601_);
v_res_1606_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_1599_, v_x_151839__boxed_1604_, v_x_151840__boxed_1605_, v_x_1602_, v_x_1603_);
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
lean_object* v___x_1618_; lean_object* v_mctx_1619_; lean_object* v_cache_1620_; lean_object* v_zetaDeltaFVarIds_1621_; lean_object* v_postponed_1622_; lean_object* v_diag_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1653_; 
v___x_1618_ = lean_st_ref_take(v___y_1616_);
v_mctx_1619_ = lean_ctor_get(v___x_1618_, 0);
v_cache_1620_ = lean_ctor_get(v___x_1618_, 1);
v_zetaDeltaFVarIds_1621_ = lean_ctor_get(v___x_1618_, 2);
v_postponed_1622_ = lean_ctor_get(v___x_1618_, 3);
v_diag_1623_ = lean_ctor_get(v___x_1618_, 4);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1625_ = v___x_1618_;
v_isShared_1626_ = v_isSharedCheck_1653_;
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
v_isShared_1626_ = v_isSharedCheck_1653_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v_depth_1627_; lean_object* v_levelAssignDepth_1628_; lean_object* v_lmvarCounter_1629_; lean_object* v_mvarCounter_1630_; lean_object* v_lDecls_1631_; lean_object* v_decls_1632_; lean_object* v_userNames_1633_; lean_object* v_lAssignment_1634_; lean_object* v_eAssignment_1635_; lean_object* v_dAssignment_1636_; lean_object* v_instanceTypedMVars_1637_; lean_object* v_synthNormMemo_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1652_; 
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
v_synthNormMemo_1638_ = lean_ctor_get(v_mctx_1619_, 11);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_mctx_1619_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1640_ = v_mctx_1619_;
v_isShared_1641_ = v_isSharedCheck_1652_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_synthNormMemo_1638_);
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
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1652_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1642_ = lean_box(0);
v___x_1643_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_eAssignment_1635_, v_mvarId_1614_, v_val_1615_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 8, v___x_1643_);
v___x_1645_ = v___x_1640_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_depth_1627_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_levelAssignDepth_1628_);
lean_ctor_set(v_reuseFailAlloc_1651_, 2, v_lmvarCounter_1629_);
lean_ctor_set(v_reuseFailAlloc_1651_, 3, v_mvarCounter_1630_);
lean_ctor_set(v_reuseFailAlloc_1651_, 4, v_lDecls_1631_);
lean_ctor_set(v_reuseFailAlloc_1651_, 5, v_decls_1632_);
lean_ctor_set(v_reuseFailAlloc_1651_, 6, v_userNames_1633_);
lean_ctor_set(v_reuseFailAlloc_1651_, 7, v_lAssignment_1634_);
lean_ctor_set(v_reuseFailAlloc_1651_, 8, v___x_1643_);
lean_ctor_set(v_reuseFailAlloc_1651_, 9, v_dAssignment_1636_);
lean_ctor_set(v_reuseFailAlloc_1651_, 10, v_instanceTypedMVars_1637_);
lean_ctor_set(v_reuseFailAlloc_1651_, 11, v_synthNormMemo_1638_);
v___x_1645_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
lean_object* v___x_1647_; 
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1645_);
v___x_1647_ = v___x_1625_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1645_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_cache_1620_);
lean_ctor_set(v_reuseFailAlloc_1650_, 2, v_zetaDeltaFVarIds_1621_);
lean_ctor_set(v_reuseFailAlloc_1650_, 3, v_postponed_1622_);
lean_ctor_set(v_reuseFailAlloc_1650_, 4, v_diag_1623_);
v___x_1647_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = lean_st_ref_put(v___y_1616_, v___x_1647_);
v___x_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1642_);
return v___x_1649_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg___boxed(lean_object* v_mvarId_1654_, lean_object* v_val_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1654_, v_val_1655_, v___y_1656_);
lean_dec(v___y_1656_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(lean_object* v___y_1659_){
_start:
{
lean_object* v___x_1661_; lean_object* v_ngen_1662_; lean_object* v_namePrefix_1663_; lean_object* v_idx_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1694_; 
v___x_1661_ = lean_st_ref_get(v___y_1659_);
v_ngen_1662_ = lean_ctor_get(v___x_1661_, 2);
lean_inc_ref(v_ngen_1662_);
lean_dec(v___x_1661_);
v_namePrefix_1663_ = lean_ctor_get(v_ngen_1662_, 0);
v_idx_1664_ = lean_ctor_get(v_ngen_1662_, 1);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_ngen_1662_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1666_ = v_ngen_1662_;
v_isShared_1667_ = v_isSharedCheck_1694_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_idx_1664_);
lean_inc(v_namePrefix_1663_);
lean_dec(v_ngen_1662_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1694_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v_r_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1672_; 
lean_inc(v_idx_1664_);
lean_inc(v_namePrefix_1663_);
v_r_1668_ = l_Lean_Name_num___override(v_namePrefix_1663_, v_idx_1664_);
v___x_1669_ = lean_unsigned_to_nat(1u);
v___x_1670_ = lean_nat_add(v_idx_1664_, v___x_1669_);
lean_dec(v_idx_1664_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 1, v___x_1670_);
v___x_1672_ = v___x_1666_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_namePrefix_1663_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1673_; lean_object* v_env_1674_; lean_object* v_nextMacroScope_1675_; lean_object* v_auxDeclNGen_1676_; lean_object* v_traceState_1677_; lean_object* v_cache_1678_; lean_object* v_recordedDeps_1679_; lean_object* v_messages_1680_; lean_object* v_infoState_1681_; lean_object* v_snapshotTasks_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1691_; 
v___x_1673_ = lean_st_ref_take(v___y_1659_);
v_env_1674_ = lean_ctor_get(v___x_1673_, 0);
v_nextMacroScope_1675_ = lean_ctor_get(v___x_1673_, 1);
v_auxDeclNGen_1676_ = lean_ctor_get(v___x_1673_, 3);
v_traceState_1677_ = lean_ctor_get(v___x_1673_, 4);
v_cache_1678_ = lean_ctor_get(v___x_1673_, 5);
v_recordedDeps_1679_ = lean_ctor_get(v___x_1673_, 6);
v_messages_1680_ = lean_ctor_get(v___x_1673_, 7);
v_infoState_1681_ = lean_ctor_get(v___x_1673_, 8);
v_snapshotTasks_1682_ = lean_ctor_get(v___x_1673_, 9);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1691_ == 0)
{
lean_object* v_unused_1692_; 
v_unused_1692_ = lean_ctor_get(v___x_1673_, 2);
lean_dec(v_unused_1692_);
v___x_1684_ = v___x_1673_;
v_isShared_1685_ = v_isSharedCheck_1691_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_snapshotTasks_1682_);
lean_inc(v_infoState_1681_);
lean_inc(v_messages_1680_);
lean_inc(v_recordedDeps_1679_);
lean_inc(v_cache_1678_);
lean_inc(v_traceState_1677_);
lean_inc(v_auxDeclNGen_1676_);
lean_inc(v_nextMacroScope_1675_);
lean_inc(v_env_1674_);
lean_dec(v___x_1673_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1691_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 2, v___x_1672_);
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_env_1674_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_nextMacroScope_1675_);
lean_ctor_set(v_reuseFailAlloc_1690_, 2, v___x_1672_);
lean_ctor_set(v_reuseFailAlloc_1690_, 3, v_auxDeclNGen_1676_);
lean_ctor_set(v_reuseFailAlloc_1690_, 4, v_traceState_1677_);
lean_ctor_set(v_reuseFailAlloc_1690_, 5, v_cache_1678_);
lean_ctor_set(v_reuseFailAlloc_1690_, 6, v_recordedDeps_1679_);
lean_ctor_set(v_reuseFailAlloc_1690_, 7, v_messages_1680_);
lean_ctor_set(v_reuseFailAlloc_1690_, 8, v_infoState_1681_);
lean_ctor_set(v_reuseFailAlloc_1690_, 9, v_snapshotTasks_1682_);
v___x_1687_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = lean_st_ref_put(v___y_1659_, v___x_1687_);
v___x_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1689_, 0, v_r_1668_);
return v___x_1689_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg___boxed(lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_1695_);
lean_dec(v___y_1695_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v___x_1709_; lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
v___x_1709_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_1707_);
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1709_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1709_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2___boxed(lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec(v___y_1718_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(lean_object* v___x_1735_, lean_object* v_a_1736_, uint8_t v___y_1737_, uint8_t v___x_1738_, uint8_t v___x_1739_, lean_object* v_a_1740_, lean_object* v___x_1741_, lean_object* v_expr_1742_, lean_object* v___x_1743_, lean_object* v_val_1744_, lean_object* v_mvarId_1745_, lean_object* v___x_1746_, lean_object* v_a_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Lean_Meta_mkLambdaFVars(v___x_1735_, v_a_1736_, v___y_1737_, v___x_1738_, v___y_1737_, v___x_1738_, v___x_1739_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1760_);
lean_dec_ref_known(v___x_1759_, 1);
v___x_1761_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1));
v___x_1762_ = lean_box(0);
v___x_1763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1763_, 0, v_a_1740_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = l_Lean_mkConst(v___x_1761_, v___x_1763_);
v___x_1765_ = lean_unsigned_to_nat(5u);
v___x_1766_ = lean_mk_empty_array_with_capacity(v___x_1765_);
v___x_1767_ = lean_array_push(v___x_1766_, v___x_1741_);
v___x_1768_ = lean_array_push(v___x_1767_, v_expr_1742_);
v___x_1769_ = lean_array_push(v___x_1768_, v___x_1743_);
v___x_1770_ = lean_array_push(v___x_1769_, v_val_1744_);
v___x_1771_ = lean_array_push(v___x_1770_, v_a_1760_);
v___x_1772_ = l_Lean_mkAppN(v___x_1764_, v___x_1771_);
lean_dec_ref(v___x_1771_);
v___x_1773_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1745_, v___x_1772_, v___y_1755_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1791_; 
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1791_ == 0)
{
lean_object* v_unused_1792_; 
v_unused_1792_ = lean_ctor_get(v___x_1773_, 0);
lean_dec(v_unused_1792_);
v___x_1775_ = v___x_1773_;
v_isShared_1776_ = v_isSharedCheck_1791_;
goto v_resetjp_1774_;
}
else
{
lean_dec(v___x_1773_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1791_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; lean_object* v_toGoalState_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1789_; 
v___x_1777_ = lean_st_ref_get(v___y_1748_);
v_toGoalState_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1789_ == 0)
{
lean_object* v_unused_1790_; 
v_unused_1790_ = lean_ctor_get(v___x_1777_, 1);
lean_dec(v_unused_1790_);
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1789_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_toGoalState_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1789_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 1, v___x_1746_);
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_toGoalState_1778_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v___x_1746_);
v___x_1783_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
lean_object* v___x_1784_; lean_object* v___x_1786_; 
v___x_1784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1784_, 0, v_a_1747_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v___x_1784_);
v___x_1786_ = v___x_1775_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec(v_a_1747_);
lean_dec(v___x_1746_);
v_a_1793_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1773_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1773_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec(v_a_1747_);
lean_dec(v___x_1746_);
lean_dec(v_mvarId_1745_);
lean_dec_ref(v_val_1744_);
lean_dec_ref(v___x_1743_);
lean_dec_ref(v_expr_1742_);
lean_dec_ref(v___x_1741_);
lean_dec(v_a_1740_);
v_a_1801_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1759_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1759_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed(lean_object** _args){
lean_object* v___x_1809_ = _args[0];
lean_object* v_a_1810_ = _args[1];
lean_object* v___y_1811_ = _args[2];
lean_object* v___x_1812_ = _args[3];
lean_object* v___x_1813_ = _args[4];
lean_object* v_a_1814_ = _args[5];
lean_object* v___x_1815_ = _args[6];
lean_object* v_expr_1816_ = _args[7];
lean_object* v___x_1817_ = _args[8];
lean_object* v_val_1818_ = _args[9];
lean_object* v_mvarId_1819_ = _args[10];
lean_object* v___x_1820_ = _args[11];
lean_object* v_a_1821_ = _args[12];
lean_object* v___y_1822_ = _args[13];
lean_object* v___y_1823_ = _args[14];
lean_object* v___y_1824_ = _args[15];
lean_object* v___y_1825_ = _args[16];
lean_object* v___y_1826_ = _args[17];
lean_object* v___y_1827_ = _args[18];
lean_object* v___y_1828_ = _args[19];
lean_object* v___y_1829_ = _args[20];
lean_object* v___y_1830_ = _args[21];
lean_object* v___y_1831_ = _args[22];
lean_object* v___y_1832_ = _args[23];
_start:
{
uint8_t v___y_152161__boxed_1833_; uint8_t v___x_152162__boxed_1834_; uint8_t v___x_152163__boxed_1835_; lean_object* v_res_1836_; 
v___y_152161__boxed_1833_ = lean_unbox(v___y_1811_);
v___x_152162__boxed_1834_ = lean_unbox(v___x_1812_);
v___x_152163__boxed_1835_ = lean_unbox(v___x_1813_);
v_res_1836_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(v___x_1809_, v_a_1810_, v___y_152161__boxed_1833_, v___x_152162__boxed_1834_, v___x_152163__boxed_1835_, v_a_1814_, v___x_1815_, v_expr_1816_, v___x_1817_, v_val_1818_, v_mvarId_1819_, v___x_1820_, v_a_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___x_1809_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(lean_object* v___x_1842_, lean_object* v_a_1843_, uint8_t v___x_1844_, uint8_t v___x_1845_, uint8_t v___x_1846_, lean_object* v_a_1847_, lean_object* v___x_1848_, lean_object* v___x_1849_, lean_object* v_expr_1850_, lean_object* v___x_1851_, lean_object* v_val_1852_, lean_object* v_mvarId_1853_, lean_object* v___x_1854_, lean_object* v_a_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lean_Meta_mkLambdaFVars(v___x_1842_, v_a_1843_, v___x_1844_, v___x_1845_, v___x_1844_, v___x_1845_, v___x_1846_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1868_);
lean_dec_ref_known(v___x_1867_, 1);
v___x_1869_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1));
v___x_1870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1870_, 0, v_a_1847_);
lean_ctor_set(v___x_1870_, 1, v___x_1848_);
v___x_1871_ = l_Lean_mkConst(v___x_1869_, v___x_1870_);
v___x_1872_ = lean_unsigned_to_nat(5u);
v___x_1873_ = lean_mk_empty_array_with_capacity(v___x_1872_);
v___x_1874_ = lean_array_push(v___x_1873_, v___x_1849_);
v___x_1875_ = lean_array_push(v___x_1874_, v_expr_1850_);
v___x_1876_ = lean_array_push(v___x_1875_, v___x_1851_);
v___x_1877_ = lean_array_push(v___x_1876_, v_val_1852_);
v___x_1878_ = lean_array_push(v___x_1877_, v_a_1868_);
v___x_1879_ = l_Lean_mkAppN(v___x_1871_, v___x_1878_);
lean_dec_ref(v___x_1878_);
v___x_1880_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1853_, v___x_1879_, v___y_1863_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1898_; 
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1898_ == 0)
{
lean_object* v_unused_1899_; 
v_unused_1899_ = lean_ctor_get(v___x_1880_, 0);
lean_dec(v_unused_1899_);
v___x_1882_ = v___x_1880_;
v_isShared_1883_ = v_isSharedCheck_1898_;
goto v_resetjp_1881_;
}
else
{
lean_dec(v___x_1880_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1898_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1884_; lean_object* v_toGoalState_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1896_; 
v___x_1884_ = lean_st_ref_get(v___y_1856_);
v_toGoalState_1885_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1896_ == 0)
{
lean_object* v_unused_1897_; 
v_unused_1897_ = lean_ctor_get(v___x_1884_, 1);
lean_dec(v_unused_1897_);
v___x_1887_ = v___x_1884_;
v_isShared_1888_ = v_isSharedCheck_1896_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_toGoalState_1885_);
lean_dec(v___x_1884_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1896_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 1, v___x_1854_);
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_toGoalState_1885_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v___x_1854_);
v___x_1890_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; lean_object* v___x_1893_; 
v___x_1891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1891_, 0, v_a_1855_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v___x_1891_);
v___x_1893_ = v___x_1882_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
lean_dec(v_a_1855_);
lean_dec(v___x_1854_);
v_a_1900_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1902_ = v___x_1880_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1880_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1900_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_dec(v_a_1855_);
lean_dec(v___x_1854_);
lean_dec(v_mvarId_1853_);
lean_dec_ref(v_val_1852_);
lean_dec_ref(v___x_1851_);
lean_dec_ref(v_expr_1850_);
lean_dec_ref(v___x_1849_);
lean_dec(v___x_1848_);
lean_dec(v_a_1847_);
v_a_1908_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1867_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1867_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed(lean_object** _args){
lean_object* v___x_1916_ = _args[0];
lean_object* v_a_1917_ = _args[1];
lean_object* v___x_1918_ = _args[2];
lean_object* v___x_1919_ = _args[3];
lean_object* v___x_1920_ = _args[4];
lean_object* v_a_1921_ = _args[5];
lean_object* v___x_1922_ = _args[6];
lean_object* v___x_1923_ = _args[7];
lean_object* v_expr_1924_ = _args[8];
lean_object* v___x_1925_ = _args[9];
lean_object* v_val_1926_ = _args[10];
lean_object* v_mvarId_1927_ = _args[11];
lean_object* v___x_1928_ = _args[12];
lean_object* v_a_1929_ = _args[13];
lean_object* v___y_1930_ = _args[14];
lean_object* v___y_1931_ = _args[15];
lean_object* v___y_1932_ = _args[16];
lean_object* v___y_1933_ = _args[17];
lean_object* v___y_1934_ = _args[18];
lean_object* v___y_1935_ = _args[19];
lean_object* v___y_1936_ = _args[20];
lean_object* v___y_1937_ = _args[21];
lean_object* v___y_1938_ = _args[22];
lean_object* v___y_1939_ = _args[23];
lean_object* v___y_1940_ = _args[24];
_start:
{
uint8_t v___x_152343__boxed_1941_; uint8_t v___x_152344__boxed_1942_; uint8_t v___x_152345__boxed_1943_; lean_object* v_res_1944_; 
v___x_152343__boxed_1941_ = lean_unbox(v___x_1918_);
v___x_152344__boxed_1942_ = lean_unbox(v___x_1919_);
v___x_152345__boxed_1943_ = lean_unbox(v___x_1920_);
v_res_1944_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(v___x_1916_, v_a_1917_, v___x_152343__boxed_1941_, v___x_152344__boxed_1942_, v___x_152345__boxed_1943_, v_a_1921_, v___x_1922_, v___x_1923_, v_expr_1924_, v___x_1925_, v_val_1926_, v_mvarId_1927_, v___x_1928_, v_a_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___x_1916_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(lean_object* v___x_1945_, lean_object* v_a_1946_, uint8_t v___y_1947_, uint8_t v___x_1948_, uint8_t v___x_1949_, lean_object* v_mvarId_1950_, lean_object* v___x_1951_, lean_object* v_a_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Lean_Meta_mkLambdaFVars(v___x_1945_, v_a_1946_, v___y_1947_, v___x_1948_, v___y_1947_, v___x_1948_, v___x_1949_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; lean_object* v___x_1966_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1965_);
lean_dec_ref_known(v___x_1964_, 1);
v___x_1966_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1950_, v_a_1965_, v___y_1960_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1984_; 
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1984_ == 0)
{
lean_object* v_unused_1985_; 
v_unused_1985_ = lean_ctor_get(v___x_1966_, 0);
lean_dec(v_unused_1985_);
v___x_1968_ = v___x_1966_;
v_isShared_1969_ = v_isSharedCheck_1984_;
goto v_resetjp_1967_;
}
else
{
lean_dec(v___x_1966_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1984_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1970_; lean_object* v_toGoalState_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1982_; 
v___x_1970_ = lean_st_ref_get(v___y_1953_);
v_toGoalState_1971_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; 
v_unused_1983_ = lean_ctor_get(v___x_1970_, 1);
lean_dec(v_unused_1983_);
v___x_1973_ = v___x_1970_;
v_isShared_1974_ = v_isSharedCheck_1982_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_toGoalState_1971_);
lean_dec(v___x_1970_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1982_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 1, v___x_1951_);
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_toGoalState_1971_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v___x_1951_);
v___x_1976_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1977_, 0, v_a_1952_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v___x_1977_);
v___x_1979_ = v___x_1968_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1977_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
lean_dec(v_a_1952_);
lean_dec(v___x_1951_);
v_a_1986_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1966_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1966_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec(v_a_1952_);
lean_dec(v___x_1951_);
lean_dec(v_mvarId_1950_);
v_a_1994_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1964_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1964_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed(lean_object** _args){
lean_object* v___x_2002_ = _args[0];
lean_object* v_a_2003_ = _args[1];
lean_object* v___y_2004_ = _args[2];
lean_object* v___x_2005_ = _args[3];
lean_object* v___x_2006_ = _args[4];
lean_object* v_mvarId_2007_ = _args[5];
lean_object* v___x_2008_ = _args[6];
lean_object* v_a_2009_ = _args[7];
lean_object* v___y_2010_ = _args[8];
lean_object* v___y_2011_ = _args[9];
lean_object* v___y_2012_ = _args[10];
lean_object* v___y_2013_ = _args[11];
lean_object* v___y_2014_ = _args[12];
lean_object* v___y_2015_ = _args[13];
lean_object* v___y_2016_ = _args[14];
lean_object* v___y_2017_ = _args[15];
lean_object* v___y_2018_ = _args[16];
lean_object* v___y_2019_ = _args[17];
lean_object* v___y_2020_ = _args[18];
_start:
{
uint8_t v___y_152514__boxed_2021_; uint8_t v___x_152515__boxed_2022_; uint8_t v___x_152516__boxed_2023_; lean_object* v_res_2024_; 
v___y_152514__boxed_2021_ = lean_unbox(v___y_2004_);
v___x_152515__boxed_2022_ = lean_unbox(v___x_2005_);
v___x_152516__boxed_2023_ = lean_unbox(v___x_2006_);
v_res_2024_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(v___x_2002_, v_a_2003_, v___y_152514__boxed_2021_, v___x_152515__boxed_2022_, v___x_152516__boxed_2023_, v_mvarId_2007_, v___x_2008_, v_a_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___x_2002_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(lean_object* v_mvarId_2027_, lean_object* v___x_2028_, lean_object* v_generation_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v___x_2041_; 
lean_inc(v_mvarId_2027_);
v___x_2041_ = l_Lean_MVarId_getTag(v_mvarId_2027_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2043_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref_known(v___x_2041_, 1);
v___x_2043_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2028_, v_a_2042_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___x_2045_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc_n(v_a_2044_, 2);
lean_dec_ref_known(v___x_2043_, 1);
v___x_2045_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2027_, v_a_2044_, v___y_2037_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v___x_2046_; lean_object* v_toGoalState_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2056_; 
lean_dec_ref_known(v___x_2045_, 1);
v___x_2046_ = lean_st_ref_get(v___y_2030_);
v_toGoalState_2047_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2056_ == 0)
{
lean_object* v_unused_2057_; 
v_unused_2057_ = lean_ctor_get(v___x_2046_, 1);
lean_dec(v_unused_2057_);
v___x_2049_ = v___x_2046_;
v_isShared_2050_ = v_isSharedCheck_2056_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_toGoalState_2047_);
lean_dec(v___x_2046_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2056_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2051_; lean_object* v___x_2053_; 
v___x_2051_ = l_Lean_Expr_mvarId_x21(v_a_2044_);
lean_dec(v_a_2044_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 1, v___x_2051_);
v___x_2053_ = v___x_2049_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_toGoalState_2047_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v___x_2051_);
v___x_2053_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
lean_object* v___x_2054_; 
v___x_2054_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v___x_2053_, v_generation_2029_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
return v___x_2054_;
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec(v_a_2044_);
lean_dec(v_generation_2029_);
v_a_2058_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2045_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2045_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec(v_generation_2029_);
lean_dec(v_mvarId_2027_);
v_a_2066_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2043_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2043_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec(v_generation_2029_);
lean_dec_ref(v___x_2028_);
lean_dec(v_mvarId_2027_);
v_a_2074_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2041_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2041_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed(lean_object* v_mvarId_2082_, lean_object* v___x_2083_, lean_object* v_generation_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(v_mvarId_2082_, v___x_2083_, v_generation_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec(v___y_2085_);
return v_res_2096_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2102_ = lean_box(0);
v___x_2103_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3));
v___x_2104_ = l_Lean_mkConst(v___x_2103_, v___x_2102_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(lean_object* v_goal_2105_, lean_object* v_generation_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v___x_2117_; lean_object* v_a_2119_; lean_object* v___y_2124_; lean_object* v___x_2134_; lean_object* v_mvarId_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2423_; 
lean_inc_ref(v_goal_2105_);
v___x_2117_ = lean_st_mk_ref(v_goal_2105_);
v___x_2134_ = lean_st_ref_get(v___x_2117_);
v_mvarId_2135_ = lean_ctor_get(v___x_2134_, 1);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2423_ == 0)
{
lean_object* v_unused_2424_; 
v_unused_2424_ = lean_ctor_get(v___x_2134_, 0);
lean_dec(v_unused_2424_);
v___x_2137_ = v___x_2134_;
v_isShared_2138_ = v_isSharedCheck_2423_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_mvarId_2135_);
lean_dec(v___x_2134_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2423_;
goto v_resetjp_2136_;
}
v___jp_2118_:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2120_ = lean_st_ref_get(v___x_2117_);
lean_dec(v___x_2117_);
v___x_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2121_, 0, v_a_2119_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___x_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
return v___x_2122_;
}
v___jp_2123_:
{
if (lean_obj_tag(v___y_2124_) == 0)
{
lean_object* v_a_2125_; 
v_a_2125_ = lean_ctor_get(v___y_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref_known(v___y_2124_, 1);
v_a_2119_ = v_a_2125_;
goto v___jp_2118_;
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
lean_dec(v___x_2117_);
v_a_2126_ = lean_ctor_get(v___y_2124_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___y_2124_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___y_2124_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___y_2124_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
v_resetjp_2136_:
{
lean_object* v___x_2139_; 
v___x_2139_ = l_Lean_MVarId_getType(v_mvarId_2135_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; uint8_t v___x_2141_; uint8_t v___x_2142_; lean_object* v___y_2144_; uint8_t v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2139_, 1);
v___x_2141_ = l_Lean_Expr_isForall(v_a_2140_);
v___x_2142_ = 1;
if (v___x_2141_ == 0)
{
uint8_t v___x_2184_; 
lean_del_object(v___x_2137_);
v___x_2184_ = l_Lean_Expr_isLet(v_a_2140_);
if (v___x_2184_ == 0)
{
lean_object* v___x_2185_; 
lean_dec(v_a_2140_);
lean_dec_ref(v___y_2112_);
lean_dec(v_generation_2106_);
v___x_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2185_, 0, v_goal_2105_);
v_a_2119_ = v___x_2185_;
goto v___jp_2118_;
}
else
{
lean_object* v___x_2186_; 
lean_dec_ref(v_goal_2105_);
v___x_2186_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_2108_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; uint8_t v_zetaDelta_2188_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
lean_dec_ref_known(v___x_2186_, 1);
v_zetaDelta_2188_ = lean_ctor_get_uint8(v_a_2187_, sizeof(void*)*14 + 19);
lean_dec(v_a_2187_);
if (v_zetaDelta_2188_ == 0)
{
lean_object* v___x_2189_; 
lean_dec(v_a_2140_);
v___x_2189_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_2117_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v___f_2191_; lean_object* v___x_2192_; lean_object* v_mvarId_2193_; lean_object* v___x_2194_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
lean_dec_ref_known(v___x_2189_, 1);
v___f_2191_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed), 13, 2);
lean_closure_set(v___f_2191_, 0, v_a_2190_);
lean_closure_set(v___f_2191_, 1, v_generation_2106_);
v___x_2192_ = lean_st_ref_get(v___x_2117_);
v_mvarId_2193_ = lean_ctor_get(v___x_2192_, 1);
lean_inc(v_mvarId_2193_);
lean_dec(v___x_2192_);
v___x_2194_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_2193_, v___f_2191_, v___x_2117_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec_ref(v___y_2112_);
v___y_2124_ = v___x_2194_;
goto v___jp_2123_;
}
else
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2202_; 
lean_dec(v___x_2117_);
lean_dec_ref(v___y_2112_);
lean_dec(v_generation_2106_);
v_a_2195_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2197_ = v___x_2189_;
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2189_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2200_; 
if (v_isShared_2198_ == 0)
{
v___x_2200_ = v___x_2197_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2195_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v_mvarId_2206_; lean_object* v___f_2207_; lean_object* v___x_2208_; 
v___x_2203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__0));
v___x_2204_ = l_Lean_Meta_expandLet(v_a_2140_, v___x_2203_, v___x_2142_);
lean_dec(v_a_2140_);
v___x_2205_ = lean_st_ref_get(v___x_2117_);
v_mvarId_2206_ = lean_ctor_get(v___x_2205_, 1);
lean_inc_n(v_mvarId_2206_, 2);
lean_dec(v___x_2205_);
v___f_2207_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed), 14, 3);
lean_closure_set(v___f_2207_, 0, v_mvarId_2206_);
lean_closure_set(v___f_2207_, 1, v___x_2204_);
lean_closure_set(v___f_2207_, 2, v_generation_2106_);
v___x_2208_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_2206_, v___f_2207_, v___x_2117_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec_ref(v___y_2112_);
v___y_2124_ = v___x_2208_;
goto v___jp_2123_;
}
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_dec(v_a_2140_);
lean_dec(v___x_2117_);
lean_dec_ref(v___y_2112_);
lean_dec(v_generation_2106_);
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
}
else
{
lean_object* v___x_2217_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; uint8_t v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; uint8_t v___y_2229_; lean_object* v___y_2230_; lean_object* v_localInsts_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___x_2315_; 
lean_dec(v_generation_2106_);
lean_dec_ref(v_goal_2105_);
v___x_2217_ = l_Lean_Expr_bindingDomain_x21(v_a_2140_);
lean_inc_ref(v___x_2217_);
v___x_2315_ = l_Lean_Meta_isProp(v___x_2217_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; uint8_t v___y_2318_; uint8_t v___x_2391_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v___x_2391_ = lean_unbox(v_a_2316_);
lean_dec(v_a_2316_);
if (v___x_2391_ == 0)
{
if (v___x_2141_ == 0)
{
lean_del_object(v___x_2137_);
v___y_2318_ = v___x_2141_;
goto v___jp_2317_;
}
else
{
lean_object* v___x_2392_; 
lean_dec_ref(v___x_2217_);
lean_dec(v_a_2140_);
v___x_2392_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_2117_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec_ref(v___y_2112_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; lean_object* v___x_2394_; lean_object* v___x_2396_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_a_2393_);
lean_dec_ref_known(v___x_2392_, 1);
v___x_2394_ = lean_st_ref_get(v___x_2117_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set_tag(v___x_2137_, 3);
lean_ctor_set(v___x_2137_, 1, v___x_2394_);
lean_ctor_set(v___x_2137_, 0, v_a_2393_);
v___x_2396_ = v___x_2137_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2393_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v___x_2394_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
v_a_2119_ = v___x_2396_;
goto v___jp_2118_;
}
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
lean_del_object(v___x_2137_);
lean_dec(v___x_2117_);
v_a_2398_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2392_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2392_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
}
else
{
uint8_t v___x_2406_; 
lean_del_object(v___x_2137_);
v___x_2406_ = 0;
v___y_2318_ = v___x_2406_;
goto v___jp_2317_;
}
v___jp_2317_:
{
lean_object* v___x_2319_; lean_object* v_mvarId_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2389_; 
v___x_2319_ = lean_st_ref_get(v___x_2117_);
v_mvarId_2320_ = lean_ctor_get(v___x_2319_, 1);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2389_ == 0)
{
lean_object* v_unused_2390_; 
v_unused_2390_ = lean_ctor_get(v___x_2319_, 0);
lean_dec(v_unused_2390_);
v___x_2322_ = v___x_2319_;
v_isShared_2323_ = v_isSharedCheck_2389_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_mvarId_2320_);
lean_dec(v___x_2319_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2389_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2324_; 
lean_inc(v_mvarId_2320_);
v___x_2324_ = l_Lean_MVarId_getTag(v_mvarId_2320_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2325_);
lean_dec_ref_known(v___x_2324_, 1);
v___x_2326_ = l_Lean_Expr_bindingBody_x21(v_a_2140_);
v___x_2327_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___x_2117_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc_n(v_a_2328_, 2);
lean_dec_ref_known(v___x_2327_, 1);
v___x_2329_ = l_Lean_mkFVar(v_a_2328_);
lean_inc_ref(v___x_2217_);
v___x_2330_ = l_Lean_Meta_Grind_preprocessHypothesis(v___x_2217_, v___x_2117_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v_lctx_2332_; lean_object* v_localInstances_2333_; lean_object* v_expr_2334_; lean_object* v_proof_x3f_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2331_);
lean_dec_ref_known(v___x_2330_, 1);
v_lctx_2332_ = lean_ctor_get(v___y_2112_, 2);
v_localInstances_2333_ = lean_ctor_get(v___y_2112_, 3);
v_expr_2334_ = lean_ctor_get(v_a_2331_, 0);
lean_inc_ref_n(v_expr_2334_, 2);
v_proof_x3f_2335_ = lean_ctor_get(v_a_2331_, 1);
lean_inc(v_proof_x3f_2335_);
lean_dec(v_a_2331_);
v___x_2336_ = l_Lean_Expr_bindingName_x21(v_a_2140_);
lean_inc(v___x_2336_);
v___x_2337_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v___x_2336_, v_expr_2334_, v___x_2117_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; uint8_t v___x_2339_; uint8_t v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v___x_2339_ = l_Lean_Expr_bindingInfo_x21(v_a_2140_);
v___x_2340_ = 0;
lean_inc_ref_n(v_expr_2334_, 2);
lean_inc(v_a_2328_);
lean_inc_ref(v_lctx_2332_);
v___x_2341_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_2332_, v_a_2328_, v_a_2338_, v_expr_2334_, v___x_2339_, v___x_2340_);
v___x_2342_ = l_Lean_Meta_isClass_x3f(v_expr_2334_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref_known(v___x_2342_, 1);
if (lean_obj_tag(v_a_2343_) == 1)
{
lean_object* v_val_2344_; lean_object* v___x_2346_; 
v_val_2344_ = lean_ctor_get(v_a_2343_, 0);
lean_inc(v_val_2344_);
lean_dec_ref_known(v_a_2343_, 1);
lean_inc_ref(v___x_2329_);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 1, v___x_2329_);
lean_ctor_set(v___x_2322_, 0, v_val_2344_);
v___x_2346_ = v___x_2322_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_val_2344_);
lean_ctor_set(v_reuseFailAlloc_2348_, 1, v___x_2329_);
v___x_2346_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
lean_object* v___x_2347_; 
lean_inc_ref(v_localInstances_2333_);
v___x_2347_ = lean_array_push(v_localInstances_2333_, v___x_2346_);
lean_inc(v___x_2117_);
lean_inc_ref(v___x_2326_);
v___y_2219_ = v_mvarId_2320_;
v___y_2220_ = v___x_2336_;
v___y_2221_ = v_proof_x3f_2335_;
v___y_2222_ = v___y_2318_;
v___y_2223_ = v___x_2326_;
v___y_2224_ = v_a_2328_;
v___y_2225_ = v_expr_2334_;
v___y_2226_ = v___x_2326_;
v___y_2227_ = v___x_2341_;
v___y_2228_ = v___x_2329_;
v___y_2229_ = v___x_2339_;
v___y_2230_ = v_a_2325_;
v_localInsts_2231_ = v___x_2347_;
v___y_2232_ = v___x_2117_;
v___y_2233_ = v___y_2107_;
v___y_2234_ = v___y_2108_;
v___y_2235_ = v___y_2109_;
v___y_2236_ = v___y_2110_;
v___y_2237_ = v___y_2111_;
v___y_2238_ = v___y_2112_;
v___y_2239_ = v___y_2113_;
v___y_2240_ = v___y_2114_;
v___y_2241_ = v___y_2115_;
goto v___jp_2218_;
}
}
else
{
lean_inc_ref(v_localInstances_2333_);
lean_dec(v_a_2343_);
lean_del_object(v___x_2322_);
lean_inc(v___x_2117_);
lean_inc_ref(v___x_2326_);
v___y_2219_ = v_mvarId_2320_;
v___y_2220_ = v___x_2336_;
v___y_2221_ = v_proof_x3f_2335_;
v___y_2222_ = v___y_2318_;
v___y_2223_ = v___x_2326_;
v___y_2224_ = v_a_2328_;
v___y_2225_ = v_expr_2334_;
v___y_2226_ = v___x_2326_;
v___y_2227_ = v___x_2341_;
v___y_2228_ = v___x_2329_;
v___y_2229_ = v___x_2339_;
v___y_2230_ = v_a_2325_;
v_localInsts_2231_ = v_localInstances_2333_;
v___y_2232_ = v___x_2117_;
v___y_2233_ = v___y_2107_;
v___y_2234_ = v___y_2108_;
v___y_2235_ = v___y_2109_;
v___y_2236_ = v___y_2110_;
v___y_2237_ = v___y_2111_;
v___y_2238_ = v___y_2112_;
v___y_2239_ = v___y_2113_;
v___y_2240_ = v___y_2114_;
v___y_2241_ = v___y_2115_;
goto v___jp_2218_;
}
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec_ref(v___x_2341_);
lean_dec(v___x_2336_);
lean_dec(v_proof_x3f_2335_);
lean_dec_ref(v_expr_2334_);
lean_dec_ref(v___x_2329_);
lean_dec(v_a_2328_);
lean_dec_ref(v___x_2326_);
lean_dec(v_a_2325_);
lean_del_object(v___x_2322_);
lean_dec(v_mvarId_2320_);
lean_dec_ref(v___x_2217_);
lean_dec(v_a_2140_);
lean_dec(v___x_2117_);
lean_dec_ref(v___y_2112_);
v_a_2349_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2342_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2342_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec(v___x_2336_);
lean_dec(v_proof_x3f_2335_);
lean_dec_ref(v_expr_2334_);
lean_dec_ref(v___x_2329_);
lean_dec(v_a_2328_);
lean_dec_ref(v___x_2326_);
lean_dec(v_a_2325_);
lean_del_object(v___x_2322_);
lean_dec(v_mvarId_2320_);
lean_dec_ref(v___x_2217_);
lean_dec(v_a_2140_);
lean_dec(v___x_2117_);
lean_dec_ref(v___y_2112_);
v_a_2357_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2337_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2337_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec_ref(v___x_2329_);
lean_dec(v_a_2328_);
lean_dec_ref(v___x_2326_);
lean_dec(v_a_2325_);
lean_del_object(v___x_2322_);
lean_dec(v_mvarId_2320_);
lean_dec_ref(v___x_2217_);
lean_dec(v_a_2140_);
lean_dec(v___x_2117_);
lean_dec_ref(v___y_2112_);
v_a_2365_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2330_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2330_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_dec_ref(v___x_2326_);
lean_dec(v_a_2325_);
lean_del_object(v___x_2322_);
lean_dec(v_mvarId_2320_);
lean_dec_ref(v___x_2217_);
lean_dec(v_a_2140_);
lean_dec(v___x_2117_);
lean_dec_ref(v___y_2112_);
v_a_2373_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2327_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2327_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_del_object(v___x_2322_);
lean_dec(v_mvarId_2320_);
lean_dec_ref(v___x_2217_);
lean_dec(v_a_2140_);
lean_dec(v___x_2117_);
lean_dec_ref(v___y_2112_);
v_a_2381_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2324_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2324_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
}
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
lean_dec_ref(v___x_2217_);
lean_dec(v_a_2140_);
lean_del_object(v___x_2137_);
lean_dec(v___x_2117_);
lean_dec_ref(v___y_2112_);
v_a_2407_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2409_ = v___x_2315_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2315_);
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
v___jp_2218_:
{
if (lean_obj_tag(v___y_2221_) == 0)
{
uint8_t v___x_2242_; 
lean_dec_ref(v___y_2225_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2220_);
lean_dec_ref(v___x_2217_);
v___x_2242_ = l_Lean_Expr_isArrow(v_a_2140_);
lean_dec(v_a_2140_);
if (v___x_2242_ == 0)
{
lean_object* v___x_2243_; 
v___x_2243_ = lean_expr_instantiate1(v___y_2226_, v___y_2228_);
lean_dec_ref(v___y_2226_);
v___y_2144_ = v___y_2219_;
v___y_2145_ = v___y_2222_;
v___y_2146_ = v___y_2224_;
v___y_2147_ = v___y_2237_;
v___y_2148_ = v___y_2236_;
v___y_2149_ = v___y_2230_;
v___y_2150_ = v___y_2240_;
v___y_2151_ = v___y_2232_;
v___y_2152_ = v___y_2238_;
v___y_2153_ = v_localInsts_2231_;
v___y_2154_ = v___y_2233_;
v___y_2155_ = v___y_2227_;
v___y_2156_ = v___y_2239_;
v___y_2157_ = v___y_2228_;
v___y_2158_ = v___y_2241_;
v___y_2159_ = v___y_2234_;
v___y_2160_ = v___y_2235_;
v___y_2161_ = v___x_2243_;
goto v___jp_2143_;
}
else
{
v___y_2144_ = v___y_2219_;
v___y_2145_ = v___y_2222_;
v___y_2146_ = v___y_2224_;
v___y_2147_ = v___y_2237_;
v___y_2148_ = v___y_2236_;
v___y_2149_ = v___y_2230_;
v___y_2150_ = v___y_2240_;
v___y_2151_ = v___y_2232_;
v___y_2152_ = v___y_2238_;
v___y_2153_ = v_localInsts_2231_;
v___y_2154_ = v___y_2233_;
v___y_2155_ = v___y_2227_;
v___y_2156_ = v___y_2239_;
v___y_2157_ = v___y_2228_;
v___y_2158_ = v___y_2241_;
v___y_2159_ = v___y_2234_;
v___y_2160_ = v___y_2235_;
v___y_2161_ = v___y_2226_;
goto v___jp_2143_;
}
}
else
{
lean_object* v_val_2244_; uint8_t v___x_2245_; 
v_val_2244_ = lean_ctor_get(v___y_2221_, 0);
lean_inc(v_val_2244_);
lean_dec_ref_known(v___y_2221_, 1);
v___x_2245_ = l_Lean_Expr_isArrow(v_a_2140_);
lean_dec(v_a_2140_);
if (v___x_2245_ == 0)
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
lean_dec_ref(v___y_2223_);
lean_inc_ref(v___y_2226_);
lean_inc_ref_n(v___x_2217_, 2);
v___x_2246_ = l_Lean_mkLambda(v___y_2220_, v___y_2229_, v___x_2217_, v___y_2226_);
v___x_2247_ = lean_box(0);
v___x_2248_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4);
lean_inc_ref(v___y_2228_);
lean_inc(v_val_2244_);
lean_inc_ref(v___y_2225_);
v___x_2249_ = l_Lean_mkApp4(v___x_2248_, v___x_2217_, v___y_2225_, v_val_2244_, v___y_2228_);
v___x_2250_ = lean_expr_instantiate1(v___y_2226_, v___x_2249_);
lean_dec_ref(v___x_2249_);
lean_dec_ref(v___y_2226_);
lean_inc_ref(v___x_2250_);
v___x_2251_ = l_Lean_Meta_getLevel(v___x_2250_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; uint8_t v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2252_);
lean_dec_ref_known(v___x_2251_, 1);
v___x_2253_ = 2;
v___x_2254_ = lean_unsigned_to_nat(0u);
v___x_2255_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_2227_, v_localInsts_2231_, v___x_2250_, v___x_2253_, v___y_2230_, v___x_2254_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; uint8_t v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___f_2265_; lean_object* v___x_2266_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
lean_inc(v_a_2256_);
lean_dec_ref_known(v___x_2255_, 1);
v___x_2257_ = l_Lean_Expr_mvarId_x21(v_a_2256_);
v___x_2258_ = lean_unsigned_to_nat(1u);
v___x_2259_ = lean_mk_empty_array_with_capacity(v___x_2258_);
v___x_2260_ = lean_array_push(v___x_2259_, v___y_2228_);
v___x_2261_ = 1;
v___x_2262_ = lean_box(v___x_2245_);
v___x_2263_ = lean_box(v___x_2142_);
v___x_2264_ = lean_box(v___x_2261_);
lean_inc(v___x_2257_);
v___f_2265_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed), 25, 14);
lean_closure_set(v___f_2265_, 0, v___x_2260_);
lean_closure_set(v___f_2265_, 1, v_a_2256_);
lean_closure_set(v___f_2265_, 2, v___x_2262_);
lean_closure_set(v___f_2265_, 3, v___x_2263_);
lean_closure_set(v___f_2265_, 4, v___x_2264_);
lean_closure_set(v___f_2265_, 5, v_a_2252_);
lean_closure_set(v___f_2265_, 6, v___x_2247_);
lean_closure_set(v___f_2265_, 7, v___x_2217_);
lean_closure_set(v___f_2265_, 8, v___y_2225_);
lean_closure_set(v___f_2265_, 9, v___x_2246_);
lean_closure_set(v___f_2265_, 10, v_val_2244_);
lean_closure_set(v___f_2265_, 11, v___y_2219_);
lean_closure_set(v___f_2265_, 12, v___x_2257_);
lean_closure_set(v___f_2265_, 13, v___y_2224_);
v___x_2266_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2257_, v___f_2265_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2232_);
v___y_2124_ = v___x_2266_;
goto v___jp_2123_;
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_dec(v_a_2252_);
lean_dec_ref(v___x_2246_);
lean_dec(v_val_2244_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec(v___y_2219_);
lean_dec_ref(v___x_2217_);
lean_dec(v___x_2117_);
v_a_2267_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2255_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2255_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
else
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
lean_dec_ref(v___x_2250_);
lean_dec_ref(v___x_2246_);
lean_dec(v_val_2244_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2232_);
lean_dec_ref(v_localInsts_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec(v___y_2219_);
lean_dec_ref(v___x_2217_);
lean_dec(v___x_2117_);
v_a_2275_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v___x_2251_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2251_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
else
{
lean_object* v___x_2283_; 
lean_dec(v___y_2220_);
lean_inc_ref(v___y_2226_);
v___x_2283_ = l_Lean_Meta_getLevel(v___y_2226_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; uint8_t v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_a_2284_);
lean_dec_ref_known(v___x_2283_, 1);
v___x_2285_ = 2;
v___x_2286_ = lean_unsigned_to_nat(0u);
v___x_2287_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_2227_, v_localInsts_2231_, v___y_2226_, v___x_2285_, v___y_2230_, v___x_2286_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; uint8_t v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___f_2297_; lean_object* v___x_2298_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref_known(v___x_2287_, 1);
v___x_2289_ = l_Lean_Expr_mvarId_x21(v_a_2288_);
v___x_2290_ = lean_unsigned_to_nat(1u);
v___x_2291_ = lean_mk_empty_array_with_capacity(v___x_2290_);
v___x_2292_ = lean_array_push(v___x_2291_, v___y_2228_);
v___x_2293_ = 1;
v___x_2294_ = lean_box(v___y_2222_);
v___x_2295_ = lean_box(v___x_2142_);
v___x_2296_ = lean_box(v___x_2293_);
lean_inc(v___x_2289_);
v___f_2297_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed), 24, 13);
lean_closure_set(v___f_2297_, 0, v___x_2292_);
lean_closure_set(v___f_2297_, 1, v_a_2288_);
lean_closure_set(v___f_2297_, 2, v___x_2294_);
lean_closure_set(v___f_2297_, 3, v___x_2295_);
lean_closure_set(v___f_2297_, 4, v___x_2296_);
lean_closure_set(v___f_2297_, 5, v_a_2284_);
lean_closure_set(v___f_2297_, 6, v___x_2217_);
lean_closure_set(v___f_2297_, 7, v___y_2225_);
lean_closure_set(v___f_2297_, 8, v___y_2223_);
lean_closure_set(v___f_2297_, 9, v_val_2244_);
lean_closure_set(v___f_2297_, 10, v___y_2219_);
lean_closure_set(v___f_2297_, 11, v___x_2289_);
lean_closure_set(v___f_2297_, 12, v___y_2224_);
v___x_2298_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2289_, v___f_2297_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2232_);
v___y_2124_ = v___x_2298_;
goto v___jp_2123_;
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec(v_a_2284_);
lean_dec(v_val_2244_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2219_);
lean_dec_ref(v___x_2217_);
lean_dec(v___x_2117_);
v_a_2299_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2287_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2287_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec(v_val_2244_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2232_);
lean_dec_ref(v_localInsts_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2219_);
lean_dec_ref(v___x_2217_);
lean_dec(v___x_2117_);
v_a_2307_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2283_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2283_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
}
}
}
v___jp_2143_:
{
uint8_t v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2162_ = 2;
v___x_2163_ = lean_unsigned_to_nat(0u);
v___x_2164_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_2155_, v___y_2153_, v___y_2161_, v___x_2162_, v___y_2149_, v___x_2163_, v___y_2152_, v___y_2156_, v___y_2150_, v___y_2158_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; uint8_t v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___f_2174_; lean_object* v___x_2175_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2165_);
lean_dec_ref_known(v___x_2164_, 1);
v___x_2166_ = l_Lean_Expr_mvarId_x21(v_a_2165_);
v___x_2167_ = lean_unsigned_to_nat(1u);
v___x_2168_ = lean_mk_empty_array_with_capacity(v___x_2167_);
v___x_2169_ = lean_array_push(v___x_2168_, v___y_2157_);
v___x_2170_ = 1;
v___x_2171_ = lean_box(v___y_2145_);
v___x_2172_ = lean_box(v___x_2142_);
v___x_2173_ = lean_box(v___x_2170_);
lean_inc(v___x_2166_);
v___f_2174_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed), 19, 8);
lean_closure_set(v___f_2174_, 0, v___x_2169_);
lean_closure_set(v___f_2174_, 1, v_a_2165_);
lean_closure_set(v___f_2174_, 2, v___x_2171_);
lean_closure_set(v___f_2174_, 3, v___x_2172_);
lean_closure_set(v___f_2174_, 4, v___x_2173_);
lean_closure_set(v___f_2174_, 5, v___y_2144_);
lean_closure_set(v___f_2174_, 6, v___x_2166_);
lean_closure_set(v___f_2174_, 7, v___y_2146_);
v___x_2175_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2166_, v___f_2174_, v___y_2151_, v___y_2154_, v___y_2159_, v___y_2160_, v___y_2148_, v___y_2147_, v___y_2152_, v___y_2156_, v___y_2150_, v___y_2158_);
lean_dec_ref(v___y_2152_);
lean_dec(v___y_2151_);
v___y_2124_ = v___x_2175_;
goto v___jp_2123_;
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_dec_ref(v___y_2157_);
lean_dec_ref(v___y_2152_);
lean_dec(v___y_2151_);
lean_dec(v___y_2146_);
lean_dec(v___y_2144_);
lean_dec(v___x_2117_);
v_a_2176_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2164_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2164_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
lean_del_object(v___x_2137_);
lean_dec(v___x_2117_);
lean_dec_ref(v___y_2112_);
lean_dec(v_generation_2106_);
lean_dec_ref(v_goal_2105_);
v_a_2415_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2139_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2139_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed(lean_object* v_goal_2425_, lean_object* v_generation_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(v_goal_2425_, v_generation_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v___y_2433_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(lean_object* v_goal_2438_, lean_object* v_generation_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v_mvarId_2450_; lean_object* v___f_2451_; lean_object* v___x_2452_; 
v_mvarId_2450_ = lean_ctor_get(v_goal_2438_, 1);
lean_inc(v_mvarId_2450_);
v___f_2451_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed), 12, 2);
lean_closure_set(v___f_2451_, 0, v_goal_2438_);
lean_closure_set(v___f_2451_, 1, v_generation_2439_);
v___x_2452_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_2450_, v___f_2451_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2461_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2455_ = v___x_2452_;
v_isShared_2456_ = v_isSharedCheck_2461_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2461_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v_fst_2457_; lean_object* v___x_2459_; 
v_fst_2457_ = lean_ctor_get(v_a_2453_, 0);
lean_inc(v_fst_2457_);
lean_dec(v_a_2453_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v_fst_2457_);
v___x_2459_ = v___x_2455_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_fst_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
v_a_2462_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2452_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2452_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___boxed(lean_object* v_goal_2470_, lean_object* v_generation_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_2470_, v_generation_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_);
lean_dec(v_a_2480_);
lean_dec_ref(v_a_2479_);
lean_dec(v_a_2478_);
lean_dec_ref(v_a_2477_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
lean_dec(v_a_2472_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(lean_object* v_mvarId_2483_, lean_object* v_val_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v___x_2496_; 
v___x_2496_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2483_, v_val_2484_, v___y_2492_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___boxed(lean_object* v_mvarId_2497_, lean_object* v_val_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(v_mvarId_2497_, v_val_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec(v___y_2499_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v___x_2522_; 
v___x_2522_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_2520_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___boxed(lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec(v___y_2523_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1(lean_object* v_00_u03b2_2535_, lean_object* v_x_2536_, lean_object* v_x_2537_, lean_object* v_x_2538_){
_start:
{
lean_object* v___x_2539_; 
v___x_2539_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_x_2536_, v_x_2537_, v_x_2538_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2540_, lean_object* v_x_2541_, size_t v_x_2542_, size_t v_x_2543_, lean_object* v_x_2544_, lean_object* v_x_2545_){
_start:
{
lean_object* v___x_2546_; 
v___x_2546_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_2541_, v_x_2542_, v_x_2543_, v_x_2544_, v_x_2545_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2547_, lean_object* v_x_2548_, lean_object* v_x_2549_, lean_object* v_x_2550_, lean_object* v_x_2551_, lean_object* v_x_2552_){
_start:
{
size_t v_x_153542__boxed_2553_; size_t v_x_153543__boxed_2554_; lean_object* v_res_2555_; 
v_x_153542__boxed_2553_ = lean_unbox_usize(v_x_2549_);
lean_dec(v_x_2549_);
v_x_153543__boxed_2554_ = lean_unbox_usize(v_x_2550_);
lean_dec(v_x_2550_);
v_res_2555_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(v_00_u03b2_2547_, v_x_2548_, v_x_153542__boxed_2553_, v_x_153543__boxed_2554_, v_x_2551_, v_x_2552_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_2556_, lean_object* v_n_2557_, lean_object* v_k_2558_, lean_object* v_v_2559_){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(v_n_2557_, v_k_2558_, v_v_2559_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2561_, size_t v_depth_2562_, lean_object* v_keys_2563_, lean_object* v_vals_2564_, lean_object* v_heq_2565_, lean_object* v_i_2566_, lean_object* v_entries_2567_){
_start:
{
lean_object* v___x_2568_; 
v___x_2568_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_2562_, v_keys_2563_, v_vals_2564_, v_i_2566_, v_entries_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2569_, lean_object* v_depth_2570_, lean_object* v_keys_2571_, lean_object* v_vals_2572_, lean_object* v_heq_2573_, lean_object* v_i_2574_, lean_object* v_entries_2575_){
_start:
{
size_t v_depth_boxed_2576_; lean_object* v_res_2577_; 
v_depth_boxed_2576_ = lean_unbox_usize(v_depth_2570_);
lean_dec(v_depth_2570_);
v_res_2577_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(v_00_u03b2_2569_, v_depth_boxed_2576_, v_keys_2571_, v_vals_2572_, v_heq_2573_, v_i_2574_, v_entries_2575_);
lean_dec_ref(v_vals_2572_);
lean_dec_ref(v_keys_2571_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_2578_, lean_object* v_x_2579_, lean_object* v_x_2580_, lean_object* v_x_2581_, lean_object* v_x_2582_){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_x_2579_, v_x_2580_, v_x_2581_, v_x_2582_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(lean_object* v_type_2584_, lean_object* v_a_2585_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = l_Lean_Expr_getAppFn(v_type_2584_);
if (lean_obj_tag(v___x_2587_) == 4)
{
lean_object* v_declName_2588_; lean_object* v___x_2589_; 
v_declName_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_declName_2588_);
lean_dec_ref_known(v___x_2587_, 2);
v___x_2589_ = l_Lean_Meta_Grind_isEagerSplit___redArg(v_declName_2588_, v_a_2585_);
lean_dec(v_declName_2588_);
return v___x_2589_;
}
else
{
uint8_t v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
lean_dec_ref(v___x_2587_);
v___x_2590_ = 0;
v___x_2591_ = lean_box(v___x_2590_);
v___x_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
return v___x_2592_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg___boxed(lean_object* v_type_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_2593_, v_a_2594_);
lean_dec_ref(v_a_2594_);
lean_dec_ref(v_type_2593_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(lean_object* v_type_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_){
_start:
{
lean_object* v___x_2608_; 
v___x_2608_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_2597_, v_a_2599_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___boxed(lean_object* v_type_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(v_type_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_);
lean_dec(v_a_2618_);
lean_dec_ref(v_a_2617_);
lean_dec(v_a_2616_);
lean_dec_ref(v_a_2615_);
lean_dec(v_a_2614_);
lean_dec_ref(v_a_2613_);
lean_dec(v_a_2612_);
lean_dec_ref(v_a_2611_);
lean_dec(v_a_2610_);
lean_dec_ref(v_type_2609_);
return v_res_2620_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2621_; 
v___x_2621_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2621_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2622_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
return v___x_2623_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2624_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2625_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_2626_ = lean_unsigned_to_nat(0u);
v___x_2627_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
lean_ctor_set(v___x_2627_, 2, v___x_2626_);
lean_ctor_set(v___x_2627_, 3, v___x_2626_);
lean_ctor_set(v___x_2627_, 4, v___x_2625_);
lean_ctor_set(v___x_2627_, 5, v___x_2625_);
lean_ctor_set(v___x_2627_, 6, v___x_2625_);
lean_ctor_set(v___x_2627_, 7, v___x_2625_);
lean_ctor_set(v___x_2627_, 8, v___x_2625_);
lean_ctor_set(v___x_2627_, 9, v___x_2625_);
lean_ctor_set(v___x_2627_, 10, v___x_2625_);
lean_ctor_set(v___x_2627_, 11, v___x_2624_);
return v___x_2627_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2628_ = lean_unsigned_to_nat(32u);
v___x_2629_ = lean_mk_empty_array_with_capacity(v___x_2628_);
v___x_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2629_);
return v___x_2630_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2631_ = ((size_t)5ULL);
v___x_2632_ = lean_unsigned_to_nat(0u);
v___x_2633_ = lean_unsigned_to_nat(32u);
v___x_2634_ = lean_mk_empty_array_with_capacity(v___x_2633_);
v___x_2635_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_2636_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
lean_ctor_set(v___x_2636_, 1, v___x_2634_);
lean_ctor_set(v___x_2636_, 2, v___x_2632_);
lean_ctor_set(v___x_2636_, 3, v___x_2632_);
lean_ctor_set_usize(v___x_2636_, 4, v___x_2631_);
return v___x_2636_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2637_ = lean_box(1);
v___x_2638_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_2639_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_2640_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2639_);
lean_ctor_set(v___x_2640_, 1, v___x_2638_);
lean_ctor_set(v___x_2640_, 2, v___x_2637_);
return v___x_2640_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2642_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_2643_ = l_Lean_stringToMessageData(v___x_2642_);
return v___x_2643_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2645_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_2646_ = l_Lean_stringToMessageData(v___x_2645_);
return v___x_2646_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2648_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_2649_ = l_Lean_stringToMessageData(v___x_2648_);
return v___x_2649_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_2652_ = l_Lean_stringToMessageData(v___x_2651_);
return v___x_2652_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_2655_ = l_Lean_stringToMessageData(v___x_2654_);
return v___x_2655_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_2658_ = l_Lean_stringToMessageData(v___x_2657_);
return v___x_2658_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_2661_ = l_Lean_stringToMessageData(v___x_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_2662_, lean_object* v_declHint_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v_env_2668_; uint8_t v___x_2669_; 
v___x_2666_ = lean_box(0);
v___x_2667_ = lean_st_ref_get(v___y_2664_);
v_env_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc_ref(v_env_2668_);
lean_dec(v___x_2667_);
v___x_2669_ = l_Lean_Name_isAnonymous(v_declHint_2663_);
if (v___x_2669_ == 0)
{
uint8_t v_isExporting_2670_; 
v_isExporting_2670_ = lean_ctor_get_uint8(v_env_2668_, sizeof(void*)*13);
if (v_isExporting_2670_ == 0)
{
lean_object* v___x_2671_; 
lean_dec_ref(v_env_2668_);
lean_dec(v_declHint_2663_);
v___x_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2671_, 0, v_msg_2662_);
return v___x_2671_;
}
else
{
lean_object* v___x_2672_; uint8_t v___x_2673_; 
lean_inc_ref(v_env_2668_);
v___x_2672_ = l_Lean_Environment_setExporting(v_env_2668_, v___x_2669_);
lean_inc(v_declHint_2663_);
lean_inc_ref(v___x_2672_);
v___x_2673_ = l_Lean_Environment_contains(v___x_2672_, v_declHint_2663_, v_isExporting_2670_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2674_; 
lean_dec_ref(v___x_2672_);
lean_dec_ref(v_env_2668_);
lean_dec(v_declHint_2663_);
v___x_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2674_, 0, v_msg_2662_);
return v___x_2674_;
}
else
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v_c_2680_; lean_object* v___x_2681_; 
v___x_2675_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_2676_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_2677_ = l_Lean_Options_empty;
v___x_2678_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2672_);
lean_ctor_set(v___x_2678_, 1, v___x_2675_);
lean_ctor_set(v___x_2678_, 2, v___x_2676_);
lean_ctor_set(v___x_2678_, 3, v___x_2677_);
lean_inc(v_declHint_2663_);
v___x_2679_ = l_Lean_MessageData_ofConstName(v_declHint_2663_, v___x_2669_);
v_c_2680_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2680_, 0, v___x_2678_);
lean_ctor_set(v_c_2680_, 1, v___x_2679_);
v___x_2681_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2668_, v_declHint_2663_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
lean_dec_ref(v_env_2668_);
lean_dec(v_declHint_2663_);
v___x_2682_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_2683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2682_);
lean_ctor_set(v___x_2683_, 1, v_c_2680_);
v___x_2684_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_2685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2683_);
lean_ctor_set(v___x_2685_, 1, v___x_2684_);
v___x_2686_ = l_Lean_MessageData_note(v___x_2685_);
v___x_2687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2687_, 0, v_msg_2662_);
lean_ctor_set(v___x_2687_, 1, v___x_2686_);
v___x_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2687_);
return v___x_2688_;
}
else
{
lean_object* v_val_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2723_; 
v_val_2689_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2691_ = v___x_2681_;
v_isShared_2692_ = v_isSharedCheck_2723_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_val_2689_);
lean_dec(v___x_2681_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2723_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v_mod_2695_; uint8_t v___x_2696_; 
v___x_2693_ = l_Lean_Environment_header(v_env_2668_);
lean_dec_ref(v_env_2668_);
v___x_2694_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2693_);
v_mod_2695_ = lean_array_get(v___x_2666_, v___x_2694_, v_val_2689_);
lean_dec(v_val_2689_);
lean_dec_ref(v___x_2694_);
v___x_2696_ = l_Lean_isPrivateName(v_declHint_2663_);
lean_dec(v_declHint_2663_);
if (v___x_2696_ == 0)
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2708_; 
v___x_2697_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_2698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
lean_ctor_set(v___x_2698_, 1, v_c_2680_);
v___x_2699_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_2700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2698_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = l_Lean_MessageData_ofName(v_mod_2695_);
v___x_2702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2700_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
v___x_2703_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_2704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2702_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___x_2705_ = l_Lean_MessageData_note(v___x_2704_);
v___x_2706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2706_, 0, v_msg_2662_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
if (v_isShared_2692_ == 0)
{
lean_ctor_set_tag(v___x_2691_, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2706_);
v___x_2708_ = v___x_2691_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2706_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
else
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2721_; 
v___x_2710_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_2711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
lean_ctor_set(v___x_2711_, 1, v_c_2680_);
v___x_2712_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_2713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2711_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
v___x_2714_ = l_Lean_MessageData_ofName(v_mod_2695_);
v___x_2715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2713_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_2717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2715_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
v___x_2718_ = l_Lean_MessageData_note(v___x_2717_);
v___x_2719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2719_, 0, v_msg_2662_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
if (v_isShared_2692_ == 0)
{
lean_ctor_set_tag(v___x_2691_, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2719_);
v___x_2721_ = v___x_2691_;
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
}
}
}
}
}
else
{
lean_object* v___x_2724_; 
lean_dec_ref(v_env_2668_);
lean_dec(v_declHint_2663_);
v___x_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2724_, 0, v_msg_2662_);
return v___x_2724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_2725_, lean_object* v_declHint_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2725_, v_declHint_2726_, v___y_2727_);
lean_dec(v___y_2727_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_2730_, lean_object* v_declHint_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v___x_2735_; lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2745_; 
v___x_2735_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2730_, v_declHint_2731_, v___y_2733_);
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2738_ = v___x_2735_;
v_isShared_2739_ = v_isSharedCheck_2745_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2735_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2745_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2743_; 
v___x_2740_ = l_Lean_unknownIdentifierMessageTag;
v___x_2741_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2740_);
lean_ctor_set(v___x_2741_, 1, v_a_2736_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 0, v___x_2741_);
v___x_2743_ = v___x_2738_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2741_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_2746_, lean_object* v_declHint_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2746_, v_declHint_2747_, v___y_2748_, v___y_2749_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msgData_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v___x_2756_; lean_object* v_toCold_2757_; lean_object* v_env_2758_; lean_object* v_options_2759_; uint8_t v___x_2760_; lean_object* v_env_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2756_ = lean_st_ref_get(v___y_2754_);
v_toCold_2757_ = lean_ctor_get(v___y_2753_, 0);
v_env_2758_ = lean_ctor_get(v___x_2756_, 0);
lean_inc_ref(v_env_2758_);
lean_dec(v___x_2756_);
v_options_2759_ = lean_ctor_get(v_toCold_2757_, 2);
v___x_2760_ = 0;
v_env_2761_ = l_Lean_Environment_setRecordingDeps(v_env_2758_, v___x_2760_);
v___x_2762_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_2763_ = lean_unsigned_to_nat(32u);
v___x_2764_ = lean_mk_empty_array_with_capacity(v___x_2763_);
lean_dec_ref(v___x_2764_);
v___x_2765_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
lean_inc_ref(v_options_2759_);
v___x_2766_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2766_, 0, v_env_2761_);
lean_ctor_set(v___x_2766_, 1, v___x_2762_);
lean_ctor_set(v___x_2766_, 2, v___x_2765_);
lean_ctor_set(v___x_2766_, 3, v_options_2759_);
v___x_2767_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
lean_ctor_set(v___x_2767_, 1, v_msgData_2752_);
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
v_ref_2778_ = lean_ctor_get(v___y_2775_, 2);
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
lean_object* v_toCold_2799_; lean_object* v_currRecDepth_2800_; lean_object* v_ref_2801_; uint16_t v_optionFlags_2802_; uint8_t v_suppressElabErrors_2803_; uint8_t v_isRecordingDeps_2804_; lean_object* v_ref_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v_toCold_2799_ = lean_ctor_get(v___y_2796_, 0);
v_currRecDepth_2800_ = lean_ctor_get(v___y_2796_, 1);
v_ref_2801_ = lean_ctor_get(v___y_2796_, 2);
v_optionFlags_2802_ = lean_ctor_get_uint16(v___y_2796_, sizeof(void*)*3);
v_suppressElabErrors_2803_ = lean_ctor_get_uint8(v___y_2796_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2804_ = lean_ctor_get_uint8(v___y_2796_, sizeof(void*)*3 + 3);
v_ref_2805_ = l_Lean_replaceRef(v_ref_2794_, v_ref_2801_);
lean_inc(v_currRecDepth_2800_);
lean_inc_ref(v_toCold_2799_);
v___x_2806_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2806_, 0, v_toCold_2799_);
lean_ctor_set(v___x_2806_, 1, v_currRecDepth_2800_);
lean_ctor_set(v___x_2806_, 2, v_ref_2805_);
lean_ctor_set_uint16(v___x_2806_, sizeof(void*)*3, v_optionFlags_2802_);
lean_ctor_set_uint8(v___x_2806_, sizeof(void*)*3 + 2, v_suppressElabErrors_2803_);
lean_ctor_set_uint8(v___x_2806_, sizeof(void*)*3 + 3, v_isRecordingDeps_2804_);
v___x_2807_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2795_, v___x_2806_, v___y_2797_);
lean_dec_ref_known(v___x_2806_, 3);
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
v_ref_2858_ = lean_ctor_get(v___y_2855_, 2);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___lam__0(lean_object* v_toGoalState_3191_, lean_object* v_mvarId_3192_, lean_object* v_goal_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v_mvarId_3205_; lean_object* v___x_3208_; 
lean_inc(v_mvarId_3192_);
v___x_3208_ = l_Lean_MVarId_getType(v_mvarId_3192_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; lean_object* v___x_3210_; 
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
lean_inc_n(v_a_3209_, 2);
lean_dec_ref_known(v___x_3208_, 1);
v___x_3210_ = l_Lean_Meta_Grind_simpCore(v_a_3209_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3242_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3213_ = v___x_3210_;
v_isShared_3214_ = v_isSharedCheck_3242_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3210_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3242_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v_expr_3215_; lean_object* v_proof_x3f_3216_; uint8_t v___x_3217_; 
v_expr_3215_ = lean_ctor_get(v_a_3211_, 0);
lean_inc_ref(v_expr_3215_);
v_proof_x3f_3216_ = lean_ctor_get(v_a_3211_, 1);
lean_inc(v_proof_x3f_3216_);
lean_dec(v_a_3211_);
v___x_3217_ = lean_expr_eqv(v_expr_3215_, v_a_3209_);
lean_dec(v_a_3209_);
if (v___x_3217_ == 0)
{
lean_del_object(v___x_3213_);
lean_dec_ref(v_goal_3193_);
if (lean_obj_tag(v_proof_x3f_3216_) == 0)
{
lean_object* v___x_3218_; 
v___x_3218_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_3192_, v_expr_3215_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_a_3219_; 
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_a_3219_);
lean_dec_ref_known(v___x_3218_, 1);
v_mvarId_3205_ = v_a_3219_;
goto v___jp_3204_;
}
else
{
lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3227_; 
lean_dec_ref(v_toGoalState_3191_);
v_a_3220_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3222_ = v___x_3218_;
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3218_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3225_; 
if (v_isShared_3223_ == 0)
{
v___x_3225_ = v___x_3222_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_a_3220_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
else
{
lean_object* v_val_3228_; lean_object* v___x_3229_; 
v_val_3228_ = lean_ctor_get(v_proof_x3f_3216_, 0);
lean_inc(v_val_3228_);
lean_dec_ref_known(v_proof_x3f_3216_, 1);
v___x_3229_ = l_Lean_MVarId_replaceTargetEq(v_mvarId_3192_, v_expr_3215_, v_val_3228_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_a_3230_; 
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
lean_inc(v_a_3230_);
lean_dec_ref_known(v___x_3229_, 1);
v_mvarId_3205_ = v_a_3230_;
goto v___jp_3204_;
}
else
{
lean_object* v_a_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3238_; 
lean_dec_ref(v_toGoalState_3191_);
v_a_3231_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3233_ = v___x_3229_;
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_a_3231_);
lean_dec(v___x_3229_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3236_; 
if (v_isShared_3234_ == 0)
{
v___x_3236_ = v___x_3233_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_a_3231_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
}
}
else
{
lean_object* v___x_3240_; 
lean_dec(v_proof_x3f_3216_);
lean_dec_ref(v_expr_3215_);
lean_dec(v_mvarId_3192_);
lean_dec_ref(v_toGoalState_3191_);
if (v_isShared_3214_ == 0)
{
lean_ctor_set(v___x_3213_, 0, v_goal_3193_);
v___x_3240_ = v___x_3213_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_goal_3193_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
else
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3250_; 
lean_dec(v_a_3209_);
lean_dec_ref(v_goal_3193_);
lean_dec(v_mvarId_3192_);
lean_dec_ref(v_toGoalState_3191_);
v_a_3243_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3245_ = v___x_3210_;
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3210_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3248_; 
if (v_isShared_3246_ == 0)
{
v___x_3248_ = v___x_3245_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_a_3243_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
}
}
else
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
lean_dec_ref(v_goal_3193_);
lean_dec(v_mvarId_3192_);
lean_dec_ref(v_toGoalState_3191_);
v_a_3251_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3253_ = v___x_3208_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3208_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3256_; 
if (v_isShared_3254_ == 0)
{
v___x_3256_ = v___x_3253_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3251_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
v___jp_3204_:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3206_, 0, v_toGoalState_3191_);
lean_ctor_set(v___x_3206_, 1, v_mvarId_3205_);
v___x_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3206_);
return v___x_3207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___lam__0___boxed(lean_object* v_toGoalState_3259_, lean_object* v_mvarId_3260_, lean_object* v_goal_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___lam__0(v_toGoalState_3259_, v_mvarId_3260_, v_goal_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec(v___y_3262_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget(lean_object* v_goal_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_){
_start:
{
lean_object* v_toGoalState_3284_; lean_object* v_mvarId_3285_; lean_object* v___f_3286_; lean_object* v___x_3287_; 
v_toGoalState_3284_ = lean_ctor_get(v_goal_3273_, 0);
lean_inc_ref(v_toGoalState_3284_);
v_mvarId_3285_ = lean_ctor_get(v_goal_3273_, 1);
lean_inc_n(v_mvarId_3285_, 2);
v___f_3286_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___lam__0___boxed), 13, 3);
lean_closure_set(v___f_3286_, 0, v_toGoalState_3284_);
lean_closure_set(v___f_3286_, 1, v_mvarId_3285_);
lean_closure_set(v___f_3286_, 2, v_goal_3273_);
v___x_3287_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3285_, v___f_3286_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___boxed(lean_object* v_goal_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget(v_goal_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
lean_dec(v_a_3297_);
lean_dec_ref(v_a_3296_);
lean_dec(v_a_3295_);
lean_dec_ref(v_a_3294_);
lean_dec(v_a_3293_);
lean_dec_ref(v_a_3292_);
lean_dec(v_a_3291_);
lean_dec_ref(v_a_3290_);
lean_dec(v_a_3289_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f(lean_object* v_goal_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_){
_start:
{
lean_object* v_mvarId_3306_; lean_object* v___x_3307_; 
v_mvarId_3306_ = lean_ctor_get(v_goal_3300_, 1);
lean_inc(v_mvarId_3306_);
lean_dec_ref(v_goal_3300_);
v___x_3307_ = l_Lean_MVarId_getDecl(v_mvarId_3306_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3317_; 
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3310_ = v___x_3307_;
v_isShared_3311_ = v_isSharedCheck_3317_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3307_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3317_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v_lctx_3312_; lean_object* v___x_3313_; lean_object* v___x_3315_; 
v_lctx_3312_ = lean_ctor_get(v_a_3308_, 1);
lean_inc_ref(v_lctx_3312_);
lean_dec(v_a_3308_);
v___x_3313_ = l_Lean_LocalContext_lastDecl(v_lctx_3312_);
lean_dec_ref(v_lctx_3312_);
if (v_isShared_3311_ == 0)
{
lean_ctor_set(v___x_3310_, 0, v___x_3313_);
v___x_3315_ = v___x_3310_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3313_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
else
{
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3325_; 
v_a_3318_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3320_ = v___x_3307_;
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3307_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_a_3318_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f___boxed(lean_object* v_goal_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l_Lean_Meta_Grind_Goal_lastDecl_x3f(v_goal_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_);
lean_dec(v_a_3330_);
lean_dec_ref(v_a_3329_);
lean_dec(v_a_3328_);
lean_dec_ref(v_a_3327_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(lean_object* v_goal_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_){
_start:
{
if (lean_obj_tag(v_a_3334_) == 0)
{
lean_object* v___x_3336_; 
v___x_3336_ = l_List_reverse___redArg(v_a_3335_);
return v___x_3336_;
}
else
{
lean_object* v_head_3337_; lean_object* v_tail_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3348_; 
v_head_3337_ = lean_ctor_get(v_a_3334_, 0);
v_tail_3338_ = lean_ctor_get(v_a_3334_, 1);
v_isSharedCheck_3348_ = !lean_is_exclusive(v_a_3334_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3340_ = v_a_3334_;
v_isShared_3341_ = v_isSharedCheck_3348_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_tail_3338_);
lean_inc(v_head_3337_);
lean_dec(v_a_3334_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3348_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v_toGoalState_3342_; lean_object* v___x_3343_; lean_object* v___x_3345_; 
v_toGoalState_3342_ = lean_ctor_get(v_goal_3333_, 0);
lean_inc_ref(v_toGoalState_3342_);
v___x_3343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3343_, 0, v_toGoalState_3342_);
lean_ctor_set(v___x_3343_, 1, v_head_3337_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 1, v_a_3335_);
lean_ctor_set(v___x_3340_, 0, v___x_3343_);
v___x_3345_ = v___x_3340_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v___x_3343_);
lean_ctor_set(v_reuseFailAlloc_3347_, 1, v_a_3335_);
v___x_3345_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
v_a_3334_ = v_tail_3338_;
v_a_3335_ = v___x_3345_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0___boxed(lean_object* v_goal_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v_goal_3349_, v_a_3350_, v_a_3351_);
lean_dec_ref(v_goal_3349_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(lean_object* v_kp_3353_, lean_object* v_as_x27_3354_, lean_object* v_b_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
if (lean_obj_tag(v_as_x27_3354_) == 0)
{
lean_object* v___x_3366_; 
lean_dec_ref(v_kp_3353_);
v___x_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3366_, 0, v_b_3355_);
return v___x_3366_;
}
else
{
lean_object* v_head_3367_; lean_object* v_tail_3368_; lean_object* v_fst_3369_; lean_object* v_snd_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3396_; 
v_head_3367_ = lean_ctor_get(v_as_x27_3354_, 0);
v_tail_3368_ = lean_ctor_get(v_as_x27_3354_, 1);
v_fst_3369_ = lean_ctor_get(v_b_3355_, 0);
v_snd_3370_ = lean_ctor_get(v_b_3355_, 1);
v_isSharedCheck_3396_ = !lean_is_exclusive(v_b_3355_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3372_ = v_b_3355_;
v_isShared_3373_ = v_isSharedCheck_3396_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_snd_3370_);
lean_inc(v_fst_3369_);
lean_dec(v_b_3355_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3396_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3374_; 
lean_inc_ref(v_kp_3353_);
lean_inc(v___y_3364_);
lean_inc_ref(v___y_3363_);
lean_inc(v___y_3362_);
lean_inc_ref(v___y_3361_);
lean_inc(v___y_3360_);
lean_inc_ref(v___y_3359_);
lean_inc(v___y_3358_);
lean_inc_ref(v___y_3357_);
lean_inc(v___y_3356_);
lean_inc(v_head_3367_);
v___x_3374_ = lean_apply_11(v_kp_3353_, v_head_3367_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, lean_box(0));
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v_a_3375_; 
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_a_3375_);
lean_dec_ref_known(v___x_3374_, 1);
if (lean_obj_tag(v_a_3375_) == 0)
{
lean_object* v_seq_3376_; lean_object* v___x_3377_; lean_object* v___x_3379_; 
v_seq_3376_ = lean_ctor_get(v_a_3375_, 0);
lean_inc(v_seq_3376_);
lean_dec_ref_known(v_a_3375_, 1);
v___x_3377_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_fst_3369_, v_seq_3376_);
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 0, v___x_3377_);
v___x_3379_ = v___x_3372_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3377_);
lean_ctor_set(v_reuseFailAlloc_3381_, 1, v_snd_3370_);
v___x_3379_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
v_as_x27_3354_ = v_tail_3368_;
v_b_3355_ = v___x_3379_;
goto _start;
}
}
else
{
lean_object* v_gs_3382_; lean_object* v___x_3383_; lean_object* v___x_3385_; 
v_gs_3382_ = lean_ctor_get(v_a_3375_, 0);
lean_inc(v_gs_3382_);
lean_dec_ref_known(v_a_3375_, 1);
v___x_3383_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_snd_3370_, v_gs_3382_);
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 1, v___x_3383_);
v___x_3385_ = v___x_3372_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_fst_3369_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v___x_3383_);
v___x_3385_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
v_as_x27_3354_ = v_tail_3368_;
v_b_3355_ = v___x_3385_;
goto _start;
}
}
}
else
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
lean_del_object(v___x_3372_);
lean_dec(v_snd_3370_);
lean_dec(v_fst_3369_);
lean_dec_ref(v_kp_3353_);
v_a_3388_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v___x_3374_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3374_);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg___boxed(lean_object* v_kp_3397_, lean_object* v_as_x27_3398_, lean_object* v_b_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_){
_start:
{
lean_object* v_res_3410_; 
v_res_3410_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3397_, v_as_x27_3398_, v_b_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec(v_as_x27_3398_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(lean_object* v_fvarId_3415_, lean_object* v_mvarId_3416_, lean_object* v_goal_3417_, lean_object* v_kp_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___x_3484_; 
lean_inc(v_fvarId_3415_);
v___x_3484_ = l_Lean_FVarId_getType___redArg(v_fvarId_3415_, v___y_3424_, v___y_3426_, v___y_3427_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v_a_3485_; lean_object* v___x_3486_; 
v_a_3485_ = lean_ctor_get(v___x_3484_, 0);
lean_inc(v_a_3485_);
lean_dec_ref_known(v___x_3484_, 1);
lean_inc(v___y_3427_);
lean_inc_ref(v___y_3426_);
lean_inc(v___y_3425_);
lean_inc_ref(v___y_3424_);
v___x_3486_ = lean_whnf(v_a_3485_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___x_3509_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3487_);
lean_dec_ref_known(v___x_3486_, 1);
v___x_3509_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_a_3487_, v___y_3420_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3549_; 
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3512_ = v___x_3509_;
v_isShared_3513_ = v_isSharedCheck_3549_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3509_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3549_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
uint8_t v___x_3514_; 
v___x_3514_ = lean_unbox(v_a_3510_);
lean_dec(v_a_3510_);
if (v___x_3514_ == 0)
{
lean_object* v___x_3515_; lean_object* v___x_3517_; 
lean_dec(v_a_3487_);
lean_dec_ref(v_kp_3418_);
lean_dec(v_mvarId_3416_);
lean_dec(v_fvarId_3415_);
v___x_3515_ = lean_box(0);
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 0, v___x_3515_);
v___x_3517_ = v___x_3512_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3515_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
else
{
lean_object* v___x_3519_; 
lean_del_object(v___x_3512_);
v___x_3519_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3420_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; uint8_t v___x_3521_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3520_);
lean_dec_ref_known(v___x_3519_, 1);
v___x_3521_ = lean_unbox(v_a_3520_);
lean_dec(v_a_3520_);
if (v___x_3521_ == 0)
{
v___y_3489_ = v___y_3419_;
v___y_3490_ = v___y_3420_;
v___y_3491_ = v___y_3421_;
v___y_3492_ = v___y_3422_;
v___y_3493_ = v___y_3423_;
v___y_3494_ = v___y_3424_;
v___y_3495_ = v___y_3425_;
v___y_3496_ = v___y_3426_;
v___y_3497_ = v___y_3427_;
goto v___jp_3488_;
}
else
{
lean_object* v___x_3522_; 
v___x_3522_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_a_3487_, v___y_3426_, v___y_3427_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3532_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3525_ = v___x_3522_;
v_isShared_3526_ = v_isSharedCheck_3532_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3522_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3532_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
uint8_t v___x_3527_; 
v___x_3527_ = lean_unbox(v_a_3523_);
lean_dec(v_a_3523_);
if (v___x_3527_ == 0)
{
lean_object* v___x_3528_; lean_object* v___x_3530_; 
lean_dec(v_a_3487_);
lean_dec_ref(v_kp_3418_);
lean_dec(v_mvarId_3416_);
lean_dec(v_fvarId_3415_);
v___x_3528_ = lean_box(0);
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 0, v___x_3528_);
v___x_3530_ = v___x_3525_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3528_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
else
{
lean_del_object(v___x_3525_);
v___y_3489_ = v___y_3419_;
v___y_3490_ = v___y_3420_;
v___y_3491_ = v___y_3421_;
v___y_3492_ = v___y_3422_;
v___y_3493_ = v___y_3423_;
v___y_3494_ = v___y_3424_;
v___y_3495_ = v___y_3425_;
v___y_3496_ = v___y_3426_;
v___y_3497_ = v___y_3427_;
goto v___jp_3488_;
}
}
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_dec(v_a_3487_);
lean_dec_ref(v_kp_3418_);
lean_dec(v_mvarId_3416_);
lean_dec(v_fvarId_3415_);
v_a_3533_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3522_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3522_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
}
else
{
lean_object* v_a_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3548_; 
lean_dec(v_a_3487_);
lean_dec_ref(v_kp_3418_);
lean_dec(v_mvarId_3416_);
lean_dec(v_fvarId_3415_);
v_a_3541_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3543_ = v___x_3519_;
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3519_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3546_; 
if (v_isShared_3544_ == 0)
{
v___x_3546_ = v___x_3543_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3541_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
}
}
else
{
lean_object* v_a_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3557_; 
lean_dec(v_a_3487_);
lean_dec_ref(v_kp_3418_);
lean_dec(v_mvarId_3416_);
lean_dec(v_fvarId_3415_);
v_a_3550_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3552_ = v___x_3509_;
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_a_3550_);
lean_dec(v___x_3509_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3555_; 
if (v_isShared_3553_ == 0)
{
v___x_3555_ = v___x_3552_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_a_3550_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
}
v___jp_3488_:
{
lean_object* v___x_3498_; 
v___x_3498_ = l_Lean_Expr_getAppFn(v_a_3487_);
lean_dec(v_a_3487_);
if (lean_obj_tag(v___x_3498_) == 4)
{
lean_object* v_declName_3499_; lean_object* v___x_3500_; 
v_declName_3499_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_declName_3499_);
lean_dec_ref_known(v___x_3498_, 2);
v___x_3500_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3499_, v___y_3491_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_dec_ref_known(v___x_3500_, 1);
v___y_3430_ = v___y_3489_;
v___y_3431_ = v___y_3490_;
v___y_3432_ = v___y_3491_;
v___y_3433_ = v___y_3492_;
v___y_3434_ = v___y_3493_;
v___y_3435_ = v___y_3494_;
v___y_3436_ = v___y_3495_;
v___y_3437_ = v___y_3496_;
v___y_3438_ = v___y_3497_;
goto v___jp_3429_;
}
else
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
lean_dec_ref(v_kp_3418_);
lean_dec(v_mvarId_3416_);
lean_dec(v_fvarId_3415_);
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3503_ = v___x_3500_;
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3500_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
if (v_isShared_3504_ == 0)
{
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
else
{
lean_dec_ref(v___x_3498_);
v___y_3430_ = v___y_3489_;
v___y_3431_ = v___y_3490_;
v___y_3432_ = v___y_3491_;
v___y_3433_ = v___y_3492_;
v___y_3434_ = v___y_3493_;
v___y_3435_ = v___y_3494_;
v___y_3436_ = v___y_3495_;
v___y_3437_ = v___y_3496_;
v___y_3438_ = v___y_3497_;
goto v___jp_3429_;
}
}
}
else
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3565_; 
lean_dec_ref(v_kp_3418_);
lean_dec(v_mvarId_3416_);
lean_dec(v_fvarId_3415_);
v_a_3558_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3560_ = v___x_3486_;
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3486_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3558_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
}
else
{
lean_object* v_a_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3573_; 
lean_dec_ref(v_kp_3418_);
lean_dec(v_mvarId_3416_);
lean_dec(v_fvarId_3415_);
v_a_3566_ = lean_ctor_get(v___x_3484_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3568_ = v___x_3484_;
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_a_3566_);
lean_dec(v___x_3484_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3571_; 
if (v_isShared_3569_ == 0)
{
v___x_3571_ = v___x_3568_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_a_3566_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
v___jp_3429_:
{
lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3439_ = l_Lean_mkFVar(v_fvarId_3415_);
v___x_3440_ = l_Lean_Meta_Grind_cases(v_mvarId_3416_, v___x_3439_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
lean_inc(v_a_3441_);
lean_dec_ref_known(v___x_3440_, 1);
v___x_3442_ = lean_box(0);
v___x_3443_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v_goal_3417_, v_a_3441_, v___x_3442_);
v___x_3444_ = lean_unsigned_to_nat(0u);
v___x_3445_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__1));
v___x_3446_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3418_, v___x_3443_, v___x_3445_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
lean_dec(v___x_3443_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3467_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3449_ = v___x_3446_;
v_isShared_3450_ = v_isSharedCheck_3467_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3446_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3467_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v_fst_3451_; lean_object* v_snd_3452_; lean_object* v___x_3453_; uint8_t v___x_3454_; 
v_fst_3451_ = lean_ctor_get(v_a_3447_, 0);
lean_inc(v_fst_3451_);
v_snd_3452_ = lean_ctor_get(v_a_3447_, 1);
lean_inc(v_snd_3452_);
lean_dec(v_a_3447_);
v___x_3453_ = lean_array_get_size(v_snd_3452_);
v___x_3454_ = lean_nat_dec_eq(v___x_3453_, v___x_3444_);
if (v___x_3454_ == 0)
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3459_; 
lean_dec(v_fst_3451_);
v___x_3455_ = lean_array_to_list(v_snd_3452_);
v___x_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3455_);
v___x_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 0, v___x_3457_);
v___x_3459_ = v___x_3449_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v___x_3457_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
return v___x_3459_;
}
}
else
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3465_; 
lean_dec(v_snd_3452_);
v___x_3461_ = lean_array_to_list(v_fst_3451_);
v___x_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3461_);
v___x_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3462_);
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 0, v___x_3463_);
v___x_3465_ = v___x_3449_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3463_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
else
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3475_; 
v_a_3468_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3470_ = v___x_3446_;
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3446_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3473_; 
if (v_isShared_3471_ == 0)
{
v___x_3473_ = v___x_3470_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3468_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
else
{
lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3483_; 
lean_dec_ref(v_kp_3418_);
v_a_3476_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3478_ = v___x_3440_;
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3440_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3481_; 
if (v_isShared_3479_ == 0)
{
v___x_3481_ = v___x_3478_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_a_3476_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed(lean_object* v_fvarId_3574_, lean_object* v_mvarId_3575_, lean_object* v_goal_3576_, lean_object* v_kp_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
lean_object* v_res_3588_; 
v_res_3588_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(v_fvarId_3574_, v_mvarId_3575_, v_goal_3576_, v_kp_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec(v___y_3578_);
lean_dec_ref(v_goal_3576_);
return v_res_3588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(lean_object* v_goal_3589_, lean_object* v_fvarId_3590_, lean_object* v_kp_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_){
_start:
{
lean_object* v_mvarId_3602_; lean_object* v___f_3603_; lean_object* v___x_3604_; 
v_mvarId_3602_ = lean_ctor_get(v_goal_3589_, 1);
lean_inc_n(v_mvarId_3602_, 2);
v___f_3603_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed), 14, 4);
lean_closure_set(v___f_3603_, 0, v_fvarId_3590_);
lean_closure_set(v___f_3603_, 1, v_mvarId_3602_);
lean_closure_set(v___f_3603_, 2, v_goal_3589_);
lean_closure_set(v___f_3603_, 3, v_kp_3591_);
v___x_3604_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3602_, v___f_3603_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___boxed(lean_object* v_goal_3605_, lean_object* v_fvarId_3606_, lean_object* v_kp_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3605_, v_fvarId_3606_, v_kp_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_);
lean_dec(v_a_3616_);
lean_dec_ref(v_a_3615_);
lean_dec(v_a_3614_);
lean_dec_ref(v_a_3613_);
lean_dec(v_a_3612_);
lean_dec_ref(v_a_3611_);
lean_dec(v_a_3610_);
lean_dec_ref(v_a_3609_);
lean_dec(v_a_3608_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(lean_object* v_kp_3619_, lean_object* v_as_3620_, lean_object* v_as_x27_3621_, lean_object* v_b_3622_, lean_object* v_a_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
lean_object* v___x_3634_; 
v___x_3634_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3619_, v_as_x27_3621_, v_b_3622_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___boxed(lean_object* v_kp_3635_, lean_object* v_as_3636_, lean_object* v_as_x27_3637_, lean_object* v_b_3638_, lean_object* v_a_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(v_kp_3635_, v_as_3636_, v_as_x27_3637_, v_b_3638_, v_a_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec(v___y_3644_);
lean_dec_ref(v___y_3643_);
lean_dec(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec(v___y_3640_);
lean_dec(v_as_x27_3637_);
lean_dec(v_as_3636_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0(lean_object* v_goal_3651_, lean_object* v_fvarId_3652_, lean_object* v_generation_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3664_ = lean_st_mk_ref(v_goal_3651_);
v___x_3665_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_3652_, v_generation_3653_, v___x_3664_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3674_; 
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3674_ == 0)
{
lean_object* v_unused_3675_; 
v_unused_3675_ = lean_ctor_get(v___x_3665_, 0);
lean_dec(v_unused_3675_);
v___x_3667_ = v___x_3665_;
v_isShared_3668_ = v_isSharedCheck_3674_;
goto v_resetjp_3666_;
}
else
{
lean_dec(v___x_3665_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3674_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3672_; 
v___x_3669_ = lean_st_ref_get(v___x_3664_);
v___x_3670_ = lean_st_ref_get(v___x_3664_);
lean_dec(v___x_3664_);
lean_dec(v___x_3670_);
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 0, v___x_3669_);
v___x_3672_ = v___x_3667_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3669_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
else
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3683_; 
lean_dec(v___x_3664_);
v_a_3676_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3678_ = v___x_3665_;
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3665_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3681_; 
if (v_isShared_3679_ == 0)
{
v___x_3681_ = v___x_3678_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3676_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0___boxed(lean_object* v_goal_3684_, lean_object* v_fvarId_3685_, lean_object* v_generation_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v_res_3697_; 
v_res_3697_ = l_Lean_Meta_Grind_Action_intro___lam__0(v_goal_3684_, v_fvarId_3685_, v_generation_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
lean_dec(v___y_3687_);
return v_res_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro(lean_object* v_generation_3700_, lean_object* v_goal_3701_, lean_object* v_kna_3702_, lean_object* v_kp_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_){
_start:
{
lean_object* v_toGoalState_3714_; uint8_t v_inconsistent_3715_; 
v_toGoalState_3714_ = lean_ctor_get(v_goal_3701_, 0);
v_inconsistent_3715_ = lean_ctor_get_uint8(v_toGoalState_3714_, sizeof(void*)*17);
if (v_inconsistent_3715_ == 0)
{
lean_object* v_mvarId_3716_; lean_object* v___x_3717_; 
v_mvarId_3716_ = lean_ctor_get(v_goal_3701_, 1);
lean_inc(v_mvarId_3716_);
v___x_3717_ = l_Lean_MVarId_getType(v_mvarId_3716_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; uint8_t v___x_3719_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref_known(v___x_3717_, 1);
v___x_3719_ = l_Lean_Expr_isFalse(v_a_3718_);
if (v___x_3719_ == 0)
{
lean_object* v___x_3720_; 
lean_dec_ref(v_kna_3702_);
lean_inc(v_generation_3700_);
v___x_3720_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_3701_, v_generation_3700_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
lean_inc(v_a_3721_);
lean_dec_ref_known(v___x_3720_, 1);
switch(lean_obj_tag(v_a_3721_))
{
case 0:
{
lean_object* v_goal_3722_; lean_object* v___x_3723_; 
lean_dec(v_generation_3700_);
v_goal_3722_ = lean_ctor_get(v_a_3721_, 0);
lean_inc_ref(v_goal_3722_);
lean_dec_ref_known(v_a_3721_, 1);
v___x_3723_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_3722_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_);
if (lean_obj_tag(v___x_3723_) == 0)
{
lean_object* v_a_3724_; lean_object* v___x_3725_; 
v_a_3724_ = lean_ctor_get(v___x_3723_, 0);
lean_inc(v_a_3724_);
lean_dec_ref_known(v___x_3723_, 1);
v___x_3725_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget(v_a_3724_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_);
if (lean_obj_tag(v___x_3725_) == 0)
{
lean_object* v_a_3726_; lean_object* v_toGoalState_3727_; lean_object* v_mvarId_3728_; lean_object* v___x_3729_; 
v_a_3726_ = lean_ctor_get(v___x_3725_, 0);
lean_inc(v_a_3726_);
lean_dec_ref_known(v___x_3725_, 1);
v_toGoalState_3727_ = lean_ctor_get(v_a_3726_, 0);
v_mvarId_3728_ = lean_ctor_get(v_a_3726_, 1);
lean_inc(v_mvarId_3728_);
v___x_3729_ = l_Lean_MVarId_getType(v_mvarId_3728_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v_a_3730_; uint8_t v___x_3731_; 
v_a_3730_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_a_3730_);
lean_dec_ref_known(v___x_3729_, 1);
v___x_3731_ = l_Lean_Expr_isForall(v_a_3730_);
if (v___x_3731_ == 0)
{
uint8_t v___x_3732_; 
v___x_3732_ = l_Lean_Expr_isLet(v_a_3730_);
lean_dec(v_a_3730_);
if (v___x_3732_ == 0)
{
lean_object* v___x_3733_; 
lean_inc(v_mvarId_3728_);
v___x_3733_ = l_Lean_MVarId_byContra_x3f(v_mvarId_3728_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
lean_inc(v_a_3734_);
lean_dec_ref_known(v___x_3733_, 1);
if (lean_obj_tag(v_a_3734_) == 1)
{
lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3743_; 
lean_inc_ref(v_toGoalState_3727_);
v_isSharedCheck_3743_ = !lean_is_exclusive(v_a_3726_);
if (v_isSharedCheck_3743_ == 0)
{
lean_object* v_unused_3744_; lean_object* v_unused_3745_; 
v_unused_3744_ = lean_ctor_get(v_a_3726_, 1);
lean_dec(v_unused_3744_);
v_unused_3745_ = lean_ctor_get(v_a_3726_, 0);
lean_dec(v_unused_3745_);
v___x_3736_ = v_a_3726_;
v_isShared_3737_ = v_isSharedCheck_3743_;
goto v_resetjp_3735_;
}
else
{
lean_dec(v_a_3726_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3743_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v_val_3738_; lean_object* v___x_3740_; 
v_val_3738_ = lean_ctor_get(v_a_3734_, 0);
lean_inc(v_val_3738_);
lean_dec_ref_known(v_a_3734_, 1);
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 1, v_val_3738_);
v___x_3740_ = v___x_3736_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_toGoalState_3727_);
lean_ctor_set(v_reuseFailAlloc_3742_, 1, v_val_3738_);
v___x_3740_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
lean_object* v___x_3741_; 
lean_inc(v_a_3712_);
lean_inc_ref(v_a_3711_);
lean_inc(v_a_3710_);
lean_inc_ref(v_a_3709_);
lean_inc(v_a_3708_);
lean_inc_ref(v_a_3707_);
lean_inc(v_a_3706_);
lean_inc_ref(v_a_3705_);
lean_inc(v_a_3704_);
v___x_3741_ = lean_apply_11(v_kp_3703_, v___x_3740_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_, lean_box(0));
return v___x_3741_;
}
}
}
else
{
lean_object* v___x_3746_; 
lean_dec(v_a_3734_);
lean_inc(v_a_3712_);
lean_inc_ref(v_a_3711_);
lean_inc(v_a_3710_);
lean_inc_ref(v_a_3709_);
lean_inc(v_a_3708_);
lean_inc_ref(v_a_3707_);
lean_inc(v_a_3706_);
lean_inc_ref(v_a_3705_);
lean_inc(v_a_3704_);
v___x_3746_ = lean_apply_11(v_kp_3703_, v_a_3726_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_, lean_box(0));
return v___x_3746_;
}
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
lean_dec(v_a_3726_);
lean_dec_ref(v_kp_3703_);
v_a_3747_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___x_3733_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3733_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
else
{
lean_object* v___x_3755_; 
lean_inc(v_a_3712_);
lean_inc_ref(v_a_3711_);
lean_inc(v_a_3710_);
lean_inc_ref(v_a_3709_);
lean_inc(v_a_3708_);
lean_inc_ref(v_a_3707_);
lean_inc(v_a_3706_);
lean_inc_ref(v_a_3705_);
lean_inc(v_a_3704_);
v___x_3755_ = lean_apply_11(v_kp_3703_, v_a_3726_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_, lean_box(0));
return v___x_3755_;
}
}
else
{
lean_object* v___x_3756_; 
lean_dec(v_a_3730_);
lean_inc(v_a_3712_);
lean_inc_ref(v_a_3711_);
lean_inc(v_a_3710_);
lean_inc_ref(v_a_3709_);
lean_inc(v_a_3708_);
lean_inc_ref(v_a_3707_);
lean_inc(v_a_3706_);
lean_inc_ref(v_a_3705_);
lean_inc(v_a_3704_);
v___x_3756_ = lean_apply_11(v_kp_3703_, v_a_3726_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_, lean_box(0));
return v___x_3756_;
}
}
else
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3764_; 
lean_dec(v_a_3726_);
lean_dec_ref(v_kp_3703_);
v_a_3757_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3759_ = v___x_3729_;
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3729_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3757_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
}
else
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3772_; 
lean_dec_ref(v_kp_3703_);
v_a_3765_ = lean_ctor_get(v___x_3725_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3767_ = v___x_3725_;
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3725_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3770_; 
if (v_isShared_3768_ == 0)
{
v___x_3770_ = v___x_3767_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_a_3765_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
else
{
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3780_; 
lean_dec_ref(v_kp_3703_);
v_a_3773_ = lean_ctor_get(v___x_3723_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3775_ = v___x_3723_;
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3723_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___x_3778_; 
if (v_isShared_3776_ == 0)
{
v___x_3778_ = v___x_3775_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_a_3773_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3781_; lean_object* v_goal_3782_; lean_object* v___f_3783_; lean_object* v___x_3784_; 
v_fvarId_3781_ = lean_ctor_get(v_a_3721_, 0);
lean_inc_n(v_fvarId_3781_, 3);
v_goal_3782_ = lean_ctor_get(v_a_3721_, 1);
lean_inc_ref_n(v_goal_3782_, 3);
lean_dec_ref_known(v_a_3721_, 2);
v___f_3783_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intro___lam__0___boxed), 13, 3);
lean_closure_set(v___f_3783_, 0, v_goal_3782_);
lean_closure_set(v___f_3783_, 1, v_fvarId_3781_);
lean_closure_set(v___f_3783_, 2, v_generation_3700_);
v___x_3784_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_3782_, v_fvarId_3781_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_a_3785_);
lean_dec_ref_known(v___x_3784_, 1);
if (lean_obj_tag(v_a_3785_) == 1)
{
lean_object* v_val_3786_; lean_object* v___x_3787_; 
lean_dec_ref(v___f_3783_);
lean_dec_ref(v_goal_3782_);
lean_dec(v_fvarId_3781_);
v_val_3786_ = lean_ctor_get(v_a_3785_, 0);
lean_inc(v_val_3786_);
lean_dec_ref_known(v_a_3785_, 1);
lean_inc(v_a_3712_);
lean_inc_ref(v_a_3711_);
lean_inc(v_a_3710_);
lean_inc_ref(v_a_3709_);
lean_inc(v_a_3708_);
lean_inc_ref(v_a_3707_);
lean_inc(v_a_3706_);
lean_inc_ref(v_a_3705_);
lean_inc(v_a_3704_);
v___x_3787_ = lean_apply_11(v_kp_3703_, v_val_3786_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_, lean_box(0));
return v___x_3787_;
}
else
{
lean_object* v___x_3788_; 
lean_dec(v_a_3785_);
lean_inc_ref(v_kp_3703_);
lean_inc_ref(v_goal_3782_);
v___x_3788_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3782_, v_fvarId_3781_, v_kp_3703_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3809_; 
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3791_ = v___x_3788_;
v_isShared_3792_ = v_isSharedCheck_3809_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3788_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3809_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
if (lean_obj_tag(v_a_3789_) == 1)
{
lean_object* v_val_3793_; lean_object* v___x_3795_; 
lean_dec_ref(v___f_3783_);
lean_dec_ref(v_goal_3782_);
lean_dec_ref(v_kp_3703_);
v_val_3793_ = lean_ctor_get(v_a_3789_, 0);
lean_inc(v_val_3793_);
lean_dec_ref_known(v_a_3789_, 1);
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 0, v_val_3793_);
v___x_3795_ = v___x_3791_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_val_3793_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
else
{
lean_object* v_mvarId_3797_; lean_object* v___x_3798_; 
lean_del_object(v___x_3791_);
lean_dec(v_a_3789_);
v_mvarId_3797_ = lean_ctor_get(v_goal_3782_, 1);
lean_inc(v_mvarId_3797_);
lean_dec_ref(v_goal_3782_);
v___x_3798_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3797_, v___f_3783_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_);
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_object* v_a_3799_; lean_object* v___x_3800_; 
v_a_3799_ = lean_ctor_get(v___x_3798_, 0);
lean_inc(v_a_3799_);
lean_dec_ref_known(v___x_3798_, 1);
lean_inc(v_a_3712_);
lean_inc_ref(v_a_3711_);
lean_inc(v_a_3710_);
lean_inc_ref(v_a_3709_);
lean_inc(v_a_3708_);
lean_inc_ref(v_a_3707_);
lean_inc(v_a_3706_);
lean_inc_ref(v_a_3705_);
lean_inc(v_a_3704_);
v___x_3800_ = lean_apply_11(v_kp_3703_, v_a_3799_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_, lean_box(0));
return v___x_3800_;
}
else
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3808_; 
lean_dec_ref(v_kp_3703_);
v_a_3801_ = lean_ctor_get(v___x_3798_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3798_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3803_ = v___x_3798_;
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v___x_3798_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3806_; 
if (v_isShared_3804_ == 0)
{
v___x_3806_ = v___x_3803_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_a_3801_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
}
}
}
}
else
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3817_; 
lean_dec_ref(v___f_3783_);
lean_dec_ref(v_goal_3782_);
lean_dec_ref(v_kp_3703_);
v_a_3810_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3812_ = v___x_3788_;
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3788_);
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
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_dec_ref(v___f_3783_);
lean_dec_ref(v_goal_3782_);
lean_dec(v_fvarId_3781_);
lean_dec_ref(v_kp_3703_);
v_a_3818_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3784_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3784_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
case 2:
{
lean_object* v_goal_3826_; lean_object* v___x_3827_; 
lean_dec(v_generation_3700_);
v_goal_3826_ = lean_ctor_get(v_a_3721_, 0);
lean_inc_ref(v_goal_3826_);
lean_dec_ref_known(v_a_3721_, 1);
lean_inc(v_a_3712_);
lean_inc_ref(v_a_3711_);
lean_inc(v_a_3710_);
lean_inc_ref(v_a_3709_);
lean_inc(v_a_3708_);
lean_inc_ref(v_a_3707_);
lean_inc(v_a_3706_);
lean_inc_ref(v_a_3705_);
lean_inc(v_a_3704_);
v___x_3827_ = lean_apply_11(v_kp_3703_, v_goal_3826_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_, lean_box(0));
return v___x_3827_;
}
default: 
{
lean_object* v_fvarId_3828_; lean_object* v_goal_3829_; lean_object* v___x_3830_; 
lean_dec(v_generation_3700_);
v_fvarId_3828_ = lean_ctor_get(v_a_3721_, 0);
lean_inc(v_fvarId_3828_);
v_goal_3829_ = lean_ctor_get(v_a_3721_, 1);
lean_inc_ref_n(v_goal_3829_, 2);
lean_dec_ref_known(v_a_3721_, 2);
lean_inc_ref(v_kp_3703_);
v___x_3830_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3829_, v_fvarId_3828_, v_kp_3703_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3840_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3833_ = v___x_3830_;
v_isShared_3834_ = v_isSharedCheck_3840_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v___x_3830_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3840_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
if (lean_obj_tag(v_a_3831_) == 1)
{
lean_object* v_val_3835_; lean_object* v___x_3837_; 
lean_dec_ref(v_goal_3829_);
lean_dec_ref(v_kp_3703_);
v_val_3835_ = lean_ctor_get(v_a_3831_, 0);
lean_inc(v_val_3835_);
lean_dec_ref_known(v_a_3831_, 1);
if (v_isShared_3834_ == 0)
{
lean_ctor_set(v___x_3833_, 0, v_val_3835_);
v___x_3837_ = v___x_3833_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_val_3835_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
else
{
lean_object* v___x_3839_; 
lean_del_object(v___x_3833_);
lean_dec(v_a_3831_);
lean_inc(v_a_3712_);
lean_inc_ref(v_a_3711_);
lean_inc(v_a_3710_);
lean_inc_ref(v_a_3709_);
lean_inc(v_a_3708_);
lean_inc_ref(v_a_3707_);
lean_inc(v_a_3706_);
lean_inc_ref(v_a_3705_);
lean_inc(v_a_3704_);
v___x_3839_ = lean_apply_11(v_kp_3703_, v_goal_3829_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_, lean_box(0));
return v___x_3839_;
}
}
}
else
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3848_; 
lean_dec_ref(v_goal_3829_);
lean_dec_ref(v_kp_3703_);
v_a_3841_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3843_ = v___x_3830_;
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3830_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3844_ == 0)
{
v___x_3846_ = v___x_3843_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_a_3841_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
}
}
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
lean_dec_ref(v_kp_3703_);
lean_dec(v_generation_3700_);
v_a_3849_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___x_3720_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3720_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_a_3849_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
else
{
lean_object* v___x_3857_; 
lean_dec_ref(v_kp_3703_);
lean_dec(v_generation_3700_);
lean_inc(v_a_3712_);
lean_inc_ref(v_a_3711_);
lean_inc(v_a_3710_);
lean_inc_ref(v_a_3709_);
lean_inc(v_a_3708_);
lean_inc_ref(v_a_3707_);
lean_inc(v_a_3706_);
lean_inc_ref(v_a_3705_);
lean_inc(v_a_3704_);
v___x_3857_ = lean_apply_11(v_kna_3702_, v_goal_3701_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_, lean_box(0));
return v___x_3857_;
}
}
else
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3865_; 
lean_dec_ref(v_kp_3703_);
lean_dec_ref(v_kna_3702_);
lean_dec_ref(v_goal_3701_);
lean_dec(v_generation_3700_);
v_a_3858_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3860_ = v___x_3717_;
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3717_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3863_; 
if (v_isShared_3861_ == 0)
{
v___x_3863_ = v___x_3860_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_a_3858_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
else
{
lean_object* v___x_3866_; lean_object* v___x_3867_; 
lean_dec_ref(v_kp_3703_);
lean_dec_ref(v_kna_3702_);
lean_dec_ref(v_goal_3701_);
lean_dec(v_generation_3700_);
v___x_3866_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intro___closed__0));
v___x_3867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3866_);
return v___x_3867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___boxed(lean_object* v_generation_3868_, lean_object* v_goal_3869_, lean_object* v_kna_3870_, lean_object* v_kp_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_){
_start:
{
lean_object* v_res_3882_; 
v_res_3882_ = l_Lean_Meta_Grind_Action_intro(v_generation_3868_, v_goal_3869_, v_kna_3870_, v_kp_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_);
lean_dec(v_a_3880_);
lean_dec_ref(v_a_3879_);
lean_dec(v_a_3878_);
lean_dec_ref(v_a_3877_);
lean_dec(v_a_3876_);
lean_dec_ref(v_a_3875_);
lean_dec(v_a_3874_);
lean_dec_ref(v_a_3873_);
lean_dec(v_a_3872_);
return v_res_3882_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_hugeNumber(void){
_start:
{
lean_object* v___x_3883_; 
v___x_3883_ = lean_unsigned_to_nat(1000000u);
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0(lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_){
_start:
{
lean_object* v___x_3897_; 
v___x_3897_ = l_Lean_Meta_Grind_Action_group___redArg(v___y_3884_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_);
return v___x_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0___boxed(lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l_Lean_Meta_Grind_Action_intros___lam__0(v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_);
lean_dec(v___y_3909_);
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
lean_dec(v___y_3903_);
lean_dec_ref(v___y_3902_);
lean_dec(v___y_3901_);
lean_dec_ref(v___y_3899_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1(lean_object* v_generation_3912_, lean_object* v___f_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_){
_start:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3927_ = lean_unsigned_to_nat(1000000u);
v___x_3928_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intro___boxed), 14, 1);
lean_closure_set(v___x_3928_, 0, v_generation_3912_);
v___x_3929_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_loop___boxed), 15, 2);
lean_closure_set(v___x_3929_, 0, v___x_3927_);
lean_closure_set(v___x_3929_, 1, v___x_3928_);
v___x_3930_ = l_Lean_Meta_Grind_Action_andThen(v___x_3929_, v___f_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1___boxed(lean_object* v_generation_3931_, lean_object* v___f_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l_Lean_Meta_Grind_Action_intros___lam__1(v_generation_3931_, v___f_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros(lean_object* v_generation_3949_, lean_object* v_a_3950_, lean_object* v_kna_3951_, lean_object* v_kp_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_){
_start:
{
lean_object* v___f_3963_; lean_object* v___f_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
v___f_3963_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intros___closed__0));
v___f_3964_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___lam__1___boxed), 15, 2);
lean_closure_set(v___f_3964_, 0, v_generation_3949_);
lean_closure_set(v___f_3964_, 1, v___f_3963_);
v___x_3965_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intros___closed__1));
v___x_3966_ = l_Lean_Meta_Grind_Action_andThen(v___x_3965_, v___f_3964_, v_a_3950_, v_kna_3951_, v_kp_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_);
return v___x_3966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___boxed(lean_object* v_generation_3967_, lean_object* v_a_3968_, lean_object* v_kna_3969_, lean_object* v_kp_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l_Lean_Meta_Grind_Action_intros(v_generation_3967_, v_a_3968_, v_kna_3969_, v_kp_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
lean_dec(v_a_3979_);
lean_dec_ref(v_a_3978_);
lean_dec(v_a_3977_);
lean_dec_ref(v_a_3976_);
lean_dec(v_a_3975_);
lean_dec_ref(v_a_3974_);
lean_dec(v_a_3973_);
lean_dec_ref(v_a_3972_);
lean_dec(v_a_3971_);
return v_res_3981_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3989_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__2));
v___x_3990_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1));
v___x_3991_ = l_Lean_mkConst(v___x_3990_, v___x_3989_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(lean_object* v_goal_3992_, lean_object* v_prop_3993_, lean_object* v_proof_3994_, lean_object* v_generation_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4006_ = lean_st_mk_ref(v_goal_3992_);
lean_inc(v___y_4004_);
lean_inc_ref(v___y_4003_);
lean_inc(v___y_4002_);
lean_inc_ref(v___y_4001_);
lean_inc(v___y_4000_);
lean_inc_ref(v___y_3999_);
lean_inc(v___y_3998_);
lean_inc_ref(v___y_3997_);
lean_inc(v___y_3996_);
lean_inc(v___x_4006_);
lean_inc_ref(v_prop_3993_);
v___x_4007_ = lean_grind_preprocess(v_prop_3993_, v___x_4006_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v_a_4008_; lean_object* v_expr_4009_; lean_object* v___x_4010_; 
v_a_4008_ = lean_ctor_get(v___x_4007_, 0);
lean_inc(v_a_4008_);
lean_dec_ref_known(v___x_4007_, 1);
v_expr_4009_ = lean_ctor_get(v_a_4008_, 0);
lean_inc_ref(v_expr_4009_);
v___x_4010_ = l_Lean_Meta_Simp_Result_getProof(v_a_4008_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
if (lean_obj_tag(v___x_4010_) == 0)
{
lean_object* v_a_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; 
v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
lean_inc(v_a_4011_);
lean_dec_ref_known(v___x_4010_, 1);
v___x_4012_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3);
lean_inc_ref(v_expr_4009_);
v___x_4013_ = l_Lean_mkApp4(v___x_4012_, v_prop_3993_, v_expr_4009_, v_a_4011_, v_proof_3994_);
v___x_4014_ = l_Lean_Meta_Grind_add(v_expr_4009_, v___x_4013_, v_generation_3995_, v___x_4006_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4023_; 
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4023_ == 0)
{
lean_object* v_unused_4024_; 
v_unused_4024_ = lean_ctor_get(v___x_4014_, 0);
lean_dec(v_unused_4024_);
v___x_4016_ = v___x_4014_;
v_isShared_4017_ = v_isSharedCheck_4023_;
goto v_resetjp_4015_;
}
else
{
lean_dec(v___x_4014_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4023_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4021_; 
v___x_4018_ = lean_st_ref_get(v___x_4006_);
v___x_4019_ = lean_st_ref_get(v___x_4006_);
lean_dec(v___x_4006_);
lean_dec(v___x_4019_);
if (v_isShared_4017_ == 0)
{
lean_ctor_set(v___x_4016_, 0, v___x_4018_);
v___x_4021_ = v___x_4016_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v___x_4018_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
else
{
lean_object* v_a_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4032_; 
lean_dec(v___x_4006_);
v_a_4025_ = lean_ctor_get(v___x_4014_, 0);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4027_ = v___x_4014_;
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_a_4025_);
lean_dec(v___x_4014_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4030_; 
if (v_isShared_4028_ == 0)
{
v___x_4030_ = v___x_4027_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_a_4025_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
}
else
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4040_; 
lean_dec_ref(v_expr_4009_);
lean_dec(v___x_4006_);
lean_dec(v_generation_3995_);
lean_dec_ref(v_proof_3994_);
lean_dec_ref(v_prop_3993_);
v_a_4033_ = lean_ctor_get(v___x_4010_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_4010_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4035_ = v___x_4010_;
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4010_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4038_; 
if (v_isShared_4036_ == 0)
{
v___x_4038_ = v___x_4035_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_a_4033_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
}
}
else
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
lean_dec(v___x_4006_);
lean_dec(v_generation_3995_);
lean_dec_ref(v_proof_3994_);
lean_dec_ref(v_prop_3993_);
v_a_4041_ = lean_ctor_get(v___x_4007_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___x_4007_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_4007_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed(lean_object* v_goal_4049_, lean_object* v_prop_4050_, lean_object* v_proof_4051_, lean_object* v_generation_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(v_goal_4049_, v_prop_4050_, v_proof_4051_, v_generation_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
lean_dec(v___y_4057_);
lean_dec_ref(v___y_4056_);
lean_dec(v___y_4055_);
lean_dec_ref(v___y_4054_);
lean_dec(v___y_4053_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(lean_object* v_goal_4064_, lean_object* v___f_4065_, lean_object* v_kp_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
lean_object* v_mvarId_4077_; lean_object* v___x_4078_; 
v_mvarId_4077_ = lean_ctor_get(v_goal_4064_, 1);
lean_inc(v_mvarId_4077_);
lean_dec_ref(v_goal_4064_);
v___x_4078_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_4077_, v___f_4065_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_);
if (lean_obj_tag(v___x_4078_) == 0)
{
lean_object* v_a_4079_; lean_object* v___x_4080_; 
v_a_4079_ = lean_ctor_get(v___x_4078_, 0);
lean_inc(v_a_4079_);
lean_dec_ref_known(v___x_4078_, 1);
lean_inc(v___y_4075_);
lean_inc_ref(v___y_4074_);
lean_inc(v___y_4073_);
lean_inc_ref(v___y_4072_);
lean_inc(v___y_4071_);
lean_inc_ref(v___y_4070_);
lean_inc(v___y_4069_);
lean_inc_ref(v___y_4068_);
lean_inc(v___y_4067_);
v___x_4080_ = lean_apply_11(v_kp_4066_, v_a_4079_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, lean_box(0));
return v___x_4080_;
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
lean_dec_ref(v_kp_4066_);
v_a_4081_ = lean_ctor_get(v___x_4078_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4078_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4078_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed(lean_object* v_goal_4089_, lean_object* v___f_4090_, lean_object* v_kp_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
lean_object* v_res_4102_; 
v_res_4102_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(v_goal_4089_, v___f_4090_, v_kp_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
lean_dec(v___y_4096_);
lean_dec_ref(v___y_4095_);
lean_dec(v___y_4094_);
lean_dec_ref(v___y_4093_);
lean_dec(v___y_4092_);
return v_res_4102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(lean_object* v_proof_4103_, lean_object* v_prop_4104_, lean_object* v_generation_4105_, lean_object* v_goal_4106_, lean_object* v_kna_4107_, lean_object* v_kp_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_){
_start:
{
lean_object* v___f_4119_; lean_object* v___f_4120_; lean_object* v___x_4121_; 
lean_inc(v_generation_4105_);
lean_inc_ref(v_proof_4103_);
lean_inc_ref(v_prop_4104_);
lean_inc_ref_n(v_goal_4106_, 2);
v___f_4119_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed), 14, 4);
lean_closure_set(v___f_4119_, 0, v_goal_4106_);
lean_closure_set(v___f_4119_, 1, v_prop_4104_);
lean_closure_set(v___f_4119_, 2, v_proof_4103_);
lean_closure_set(v___f_4119_, 3, v_generation_4105_);
lean_inc_ref(v_kp_4108_);
v___f_4120_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed), 13, 3);
lean_closure_set(v___f_4120_, 0, v_goal_4106_);
lean_closure_set(v___f_4120_, 1, v___f_4119_);
lean_closure_set(v___f_4120_, 2, v_kp_4108_);
v___x_4121_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_prop_4104_, v_a_4110_);
if (lean_obj_tag(v___x_4121_) == 0)
{
lean_object* v_a_4122_; uint8_t v___x_4123_; 
v_a_4122_ = lean_ctor_get(v___x_4121_, 0);
lean_inc(v_a_4122_);
lean_dec_ref_known(v___x_4121_, 1);
v___x_4123_ = lean_unbox(v_a_4122_);
lean_dec(v_a_4122_);
if (v___x_4123_ == 0)
{
lean_object* v_mvarId_4124_; lean_object* v___x_4125_; 
lean_dec_ref(v_kp_4108_);
lean_dec_ref(v_kna_4107_);
lean_dec(v_generation_4105_);
lean_dec_ref(v_prop_4104_);
lean_dec_ref(v_proof_4103_);
v_mvarId_4124_ = lean_ctor_get(v_goal_4106_, 1);
lean_inc(v_mvarId_4124_);
lean_dec_ref(v_goal_4106_);
v___x_4125_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_4124_, v___f_4120_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
return v___x_4125_;
}
else
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
lean_dec_ref(v___f_4120_);
v___x_4126_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v___x_4127_ = l_Lean_Core_mkFreshUserName(v___x_4126_, v_a_4116_, v_a_4117_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4128_; lean_object* v_toGoalState_4129_; lean_object* v_mvarId_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4148_; 
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_a_4128_);
lean_dec_ref_known(v___x_4127_, 1);
v_toGoalState_4129_ = lean_ctor_get(v_goal_4106_, 0);
v_mvarId_4130_ = lean_ctor_get(v_goal_4106_, 1);
v_isSharedCheck_4148_ = !lean_is_exclusive(v_goal_4106_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4132_ = v_goal_4106_;
v_isShared_4133_ = v_isSharedCheck_4148_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_mvarId_4130_);
lean_inc(v_toGoalState_4129_);
lean_dec(v_goal_4106_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4148_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4134_; 
v___x_4134_ = l_Lean_MVarId_assert(v_mvarId_4130_, v_a_4128_, v_prop_4104_, v_proof_4103_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v_a_4135_; lean_object* v___x_4137_; 
v_a_4135_ = lean_ctor_get(v___x_4134_, 0);
lean_inc(v_a_4135_);
lean_dec_ref_known(v___x_4134_, 1);
if (v_isShared_4133_ == 0)
{
lean_ctor_set(v___x_4132_, 1, v_a_4135_);
v___x_4137_ = v___x_4132_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_toGoalState_4129_);
lean_ctor_set(v_reuseFailAlloc_4139_, 1, v_a_4135_);
v___x_4137_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
lean_object* v___x_4138_; 
v___x_4138_ = l_Lean_Meta_Grind_Action_intros(v_generation_4105_, v___x_4137_, v_kna_4107_, v_kp_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
return v___x_4138_;
}
}
else
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
lean_del_object(v___x_4132_);
lean_dec_ref(v_toGoalState_4129_);
lean_dec_ref(v_kp_4108_);
lean_dec_ref(v_kna_4107_);
lean_dec(v_generation_4105_);
v_a_4140_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4142_ = v___x_4134_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_4134_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4145_; 
if (v_isShared_4143_ == 0)
{
v___x_4145_ = v___x_4142_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4140_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
}
else
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4156_; 
lean_dec_ref(v_kp_4108_);
lean_dec_ref(v_kna_4107_);
lean_dec_ref(v_goal_4106_);
lean_dec(v_generation_4105_);
lean_dec_ref(v_prop_4104_);
lean_dec_ref(v_proof_4103_);
v_a_4149_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4151_ = v___x_4127_;
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v___x_4127_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4154_; 
if (v_isShared_4152_ == 0)
{
v___x_4154_ = v___x_4151_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
return v___x_4154_;
}
}
}
}
}
else
{
lean_object* v_a_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4164_; 
lean_dec_ref(v___f_4120_);
lean_dec_ref(v_kp_4108_);
lean_dec_ref(v_kna_4107_);
lean_dec_ref(v_goal_4106_);
lean_dec(v_generation_4105_);
lean_dec_ref(v_prop_4104_);
lean_dec_ref(v_proof_4103_);
v_a_4157_ = lean_ctor_get(v___x_4121_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4121_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4159_ = v___x_4121_;
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_a_4157_);
lean_dec(v___x_4121_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4162_; 
if (v_isShared_4160_ == 0)
{
v___x_4162_ = v___x_4159_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
return v___x_4162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___boxed(lean_object* v_proof_4165_, lean_object* v_prop_4166_, lean_object* v_generation_4167_, lean_object* v_goal_4168_, lean_object* v_kna_4169_, lean_object* v_kp_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(v_proof_4165_, v_prop_4166_, v_generation_4167_, v_goal_4168_, v_kna_4169_, v_kp_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_);
lean_dec(v_a_4179_);
lean_dec_ref(v_a_4178_);
lean_dec(v_a_4177_);
lean_dec_ref(v_a_4176_);
lean_dec(v_a_4175_);
lean_dec_ref(v_a_4174_);
lean_dec(v_a_4173_);
lean_dec_ref(v_a_4172_);
lean_dec(v_a_4171_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext(lean_object* v_goal_4182_, lean_object* v_kna_4183_, lean_object* v_kp_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_){
_start:
{
lean_object* v_toGoalState_4195_; uint8_t v_inconsistent_4196_; 
v_toGoalState_4195_ = lean_ctor_get(v_goal_4182_, 0);
lean_inc_ref(v_toGoalState_4195_);
v_inconsistent_4196_ = lean_ctor_get_uint8(v_toGoalState_4195_, sizeof(void*)*17);
if (v_inconsistent_4196_ == 0)
{
lean_object* v_mvarId_4197_; lean_object* v_nextDeclIdx_4198_; lean_object* v_enodeMap_4199_; lean_object* v_exprs_4200_; lean_object* v_parents_4201_; lean_object* v_congrTable_4202_; lean_object* v_appMap_4203_; lean_object* v_indicesFound_4204_; lean_object* v_newFacts_4205_; lean_object* v_nextIdx_4206_; lean_object* v_newRawFacts_4207_; lean_object* v_facts_4208_; lean_object* v_extThms_4209_; lean_object* v_ematch_4210_; lean_object* v_inj_4211_; lean_object* v_split_4212_; lean_object* v_clean_4213_; lean_object* v_sstates_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4254_; 
v_mvarId_4197_ = lean_ctor_get(v_goal_4182_, 1);
v_nextDeclIdx_4198_ = lean_ctor_get(v_toGoalState_4195_, 0);
v_enodeMap_4199_ = lean_ctor_get(v_toGoalState_4195_, 1);
v_exprs_4200_ = lean_ctor_get(v_toGoalState_4195_, 2);
v_parents_4201_ = lean_ctor_get(v_toGoalState_4195_, 3);
v_congrTable_4202_ = lean_ctor_get(v_toGoalState_4195_, 4);
v_appMap_4203_ = lean_ctor_get(v_toGoalState_4195_, 5);
v_indicesFound_4204_ = lean_ctor_get(v_toGoalState_4195_, 6);
v_newFacts_4205_ = lean_ctor_get(v_toGoalState_4195_, 7);
v_nextIdx_4206_ = lean_ctor_get(v_toGoalState_4195_, 8);
v_newRawFacts_4207_ = lean_ctor_get(v_toGoalState_4195_, 9);
v_facts_4208_ = lean_ctor_get(v_toGoalState_4195_, 10);
v_extThms_4209_ = lean_ctor_get(v_toGoalState_4195_, 11);
v_ematch_4210_ = lean_ctor_get(v_toGoalState_4195_, 12);
v_inj_4211_ = lean_ctor_get(v_toGoalState_4195_, 13);
v_split_4212_ = lean_ctor_get(v_toGoalState_4195_, 14);
v_clean_4213_ = lean_ctor_get(v_toGoalState_4195_, 15);
v_sstates_4214_ = lean_ctor_get(v_toGoalState_4195_, 16);
v_isSharedCheck_4254_ = !lean_is_exclusive(v_toGoalState_4195_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4216_ = v_toGoalState_4195_;
v_isShared_4217_ = v_isSharedCheck_4254_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_sstates_4214_);
lean_inc(v_clean_4213_);
lean_inc(v_split_4212_);
lean_inc(v_inj_4211_);
lean_inc(v_ematch_4210_);
lean_inc(v_extThms_4209_);
lean_inc(v_facts_4208_);
lean_inc(v_newRawFacts_4207_);
lean_inc(v_nextIdx_4206_);
lean_inc(v_newFacts_4205_);
lean_inc(v_indicesFound_4204_);
lean_inc(v_appMap_4203_);
lean_inc(v_congrTable_4202_);
lean_inc(v_parents_4201_);
lean_inc(v_exprs_4200_);
lean_inc(v_enodeMap_4199_);
lean_inc(v_nextDeclIdx_4198_);
lean_dec(v_toGoalState_4195_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4254_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4218_; 
v___x_4218_ = l_Std_Queue_dequeue_x3f___redArg(v_newRawFacts_4207_);
if (lean_obj_tag(v___x_4218_) == 1)
{
lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4250_; 
lean_inc(v_mvarId_4197_);
v_isSharedCheck_4250_ = !lean_is_exclusive(v_goal_4182_);
if (v_isSharedCheck_4250_ == 0)
{
lean_object* v_unused_4251_; lean_object* v_unused_4252_; 
v_unused_4251_ = lean_ctor_get(v_goal_4182_, 1);
lean_dec(v_unused_4251_);
v_unused_4252_ = lean_ctor_get(v_goal_4182_, 0);
lean_dec(v_unused_4252_);
v___x_4220_ = v_goal_4182_;
v_isShared_4221_ = v_isSharedCheck_4250_;
goto v_resetjp_4219_;
}
else
{
lean_dec(v_goal_4182_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4250_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v_val_4222_; lean_object* v_fst_4223_; lean_object* v_snd_4224_; lean_object* v_proof_4225_; lean_object* v_prop_4226_; lean_object* v_generation_4227_; lean_object* v_splitSource_4228_; lean_object* v_ematchDiagSource_4229_; lean_object* v_simp_4230_; lean_object* v_simpMethods_4231_; lean_object* v_symSimpMethods_4232_; lean_object* v_symDSimpMethods_4233_; lean_object* v_config_4234_; lean_object* v_anchorRefs_x3f_4235_; uint8_t v_cheapCases_4236_; uint8_t v_reportMVarIssue_4237_; lean_object* v_symPrios_4238_; lean_object* v_extensions_4239_; uint8_t v_debug_4240_; uint8_t v_ematchDiag_4241_; lean_object* v___x_4243_; 
v_val_4222_ = lean_ctor_get(v___x_4218_, 0);
lean_inc(v_val_4222_);
lean_dec_ref_known(v___x_4218_, 1);
v_fst_4223_ = lean_ctor_get(v_val_4222_, 0);
lean_inc(v_fst_4223_);
v_snd_4224_ = lean_ctor_get(v_val_4222_, 1);
lean_inc(v_snd_4224_);
lean_dec(v_val_4222_);
v_proof_4225_ = lean_ctor_get(v_fst_4223_, 0);
lean_inc_ref(v_proof_4225_);
v_prop_4226_ = lean_ctor_get(v_fst_4223_, 1);
lean_inc_ref(v_prop_4226_);
v_generation_4227_ = lean_ctor_get(v_fst_4223_, 2);
lean_inc(v_generation_4227_);
v_splitSource_4228_ = lean_ctor_get(v_fst_4223_, 3);
lean_inc(v_splitSource_4228_);
v_ematchDiagSource_4229_ = lean_ctor_get(v_fst_4223_, 4);
lean_inc(v_ematchDiagSource_4229_);
lean_dec(v_fst_4223_);
v_simp_4230_ = lean_ctor_get(v_a_4186_, 0);
v_simpMethods_4231_ = lean_ctor_get(v_a_4186_, 1);
v_symSimpMethods_4232_ = lean_ctor_get(v_a_4186_, 2);
v_symDSimpMethods_4233_ = lean_ctor_get(v_a_4186_, 3);
v_config_4234_ = lean_ctor_get(v_a_4186_, 4);
v_anchorRefs_x3f_4235_ = lean_ctor_get(v_a_4186_, 5);
v_cheapCases_4236_ = lean_ctor_get_uint8(v_a_4186_, sizeof(void*)*10);
v_reportMVarIssue_4237_ = lean_ctor_get_uint8(v_a_4186_, sizeof(void*)*10 + 1);
v_symPrios_4238_ = lean_ctor_get(v_a_4186_, 8);
v_extensions_4239_ = lean_ctor_get(v_a_4186_, 9);
v_debug_4240_ = lean_ctor_get_uint8(v_a_4186_, sizeof(void*)*10 + 2);
v_ematchDiag_4241_ = lean_ctor_get_uint8(v_a_4186_, sizeof(void*)*10 + 3);
if (v_isShared_4217_ == 0)
{
lean_ctor_set(v___x_4216_, 9, v_snd_4224_);
v___x_4243_ = v___x_4216_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_nextDeclIdx_4198_);
lean_ctor_set(v_reuseFailAlloc_4249_, 1, v_enodeMap_4199_);
lean_ctor_set(v_reuseFailAlloc_4249_, 2, v_exprs_4200_);
lean_ctor_set(v_reuseFailAlloc_4249_, 3, v_parents_4201_);
lean_ctor_set(v_reuseFailAlloc_4249_, 4, v_congrTable_4202_);
lean_ctor_set(v_reuseFailAlloc_4249_, 5, v_appMap_4203_);
lean_ctor_set(v_reuseFailAlloc_4249_, 6, v_indicesFound_4204_);
lean_ctor_set(v_reuseFailAlloc_4249_, 7, v_newFacts_4205_);
lean_ctor_set(v_reuseFailAlloc_4249_, 8, v_nextIdx_4206_);
lean_ctor_set(v_reuseFailAlloc_4249_, 9, v_snd_4224_);
lean_ctor_set(v_reuseFailAlloc_4249_, 10, v_facts_4208_);
lean_ctor_set(v_reuseFailAlloc_4249_, 11, v_extThms_4209_);
lean_ctor_set(v_reuseFailAlloc_4249_, 12, v_ematch_4210_);
lean_ctor_set(v_reuseFailAlloc_4249_, 13, v_inj_4211_);
lean_ctor_set(v_reuseFailAlloc_4249_, 14, v_split_4212_);
lean_ctor_set(v_reuseFailAlloc_4249_, 15, v_clean_4213_);
lean_ctor_set(v_reuseFailAlloc_4249_, 16, v_sstates_4214_);
lean_ctor_set_uint8(v_reuseFailAlloc_4249_, sizeof(void*)*17, v_inconsistent_4196_);
v___x_4243_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
lean_object* v_goal_4245_; 
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 0, v___x_4243_);
v_goal_4245_ = v___x_4220_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v___x_4243_);
lean_ctor_set(v_reuseFailAlloc_4248_, 1, v_mvarId_4197_);
v_goal_4245_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
lean_object* v___x_4246_; lean_object* v___x_4247_; 
lean_inc_ref(v_extensions_4239_);
lean_inc_ref(v_symPrios_4238_);
lean_inc(v_anchorRefs_x3f_4235_);
lean_inc_ref(v_config_4234_);
lean_inc_ref(v_symDSimpMethods_4233_);
lean_inc_ref(v_symSimpMethods_4232_);
lean_inc_ref(v_simpMethods_4231_);
lean_inc_ref(v_simp_4230_);
v___x_4246_ = lean_alloc_ctor(0, 10, 4);
lean_ctor_set(v___x_4246_, 0, v_simp_4230_);
lean_ctor_set(v___x_4246_, 1, v_simpMethods_4231_);
lean_ctor_set(v___x_4246_, 2, v_symSimpMethods_4232_);
lean_ctor_set(v___x_4246_, 3, v_symDSimpMethods_4233_);
lean_ctor_set(v___x_4246_, 4, v_config_4234_);
lean_ctor_set(v___x_4246_, 5, v_anchorRefs_x3f_4235_);
lean_ctor_set(v___x_4246_, 6, v_splitSource_4228_);
lean_ctor_set(v___x_4246_, 7, v_ematchDiagSource_4229_);
lean_ctor_set(v___x_4246_, 8, v_symPrios_4238_);
lean_ctor_set(v___x_4246_, 9, v_extensions_4239_);
lean_ctor_set_uint8(v___x_4246_, sizeof(void*)*10, v_cheapCases_4236_);
lean_ctor_set_uint8(v___x_4246_, sizeof(void*)*10 + 1, v_reportMVarIssue_4237_);
lean_ctor_set_uint8(v___x_4246_, sizeof(void*)*10 + 2, v_debug_4240_);
lean_ctor_set_uint8(v___x_4246_, sizeof(void*)*10 + 3, v_ematchDiag_4241_);
v___x_4247_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(v_proof_4225_, v_prop_4226_, v_generation_4227_, v_goal_4245_, v_kna_4183_, v_kp_4184_, v_a_4185_, v___x_4246_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_);
lean_dec_ref_known(v___x_4246_, 10);
return v___x_4247_;
}
}
}
}
else
{
lean_object* v___x_4253_; 
lean_dec(v___x_4218_);
lean_del_object(v___x_4216_);
lean_dec_ref(v_sstates_4214_);
lean_dec_ref(v_clean_4213_);
lean_dec_ref(v_split_4212_);
lean_dec_ref(v_inj_4211_);
lean_dec_ref(v_ematch_4210_);
lean_dec_ref(v_extThms_4209_);
lean_dec_ref(v_facts_4208_);
lean_dec(v_nextIdx_4206_);
lean_dec_ref(v_newFacts_4205_);
lean_dec_ref(v_indicesFound_4204_);
lean_dec_ref(v_appMap_4203_);
lean_dec_ref(v_congrTable_4202_);
lean_dec_ref(v_parents_4201_);
lean_dec_ref(v_exprs_4200_);
lean_dec_ref(v_enodeMap_4199_);
lean_dec(v_nextDeclIdx_4198_);
lean_dec_ref(v_kp_4184_);
lean_inc(v_a_4193_);
lean_inc_ref(v_a_4192_);
lean_inc(v_a_4191_);
lean_inc_ref(v_a_4190_);
lean_inc(v_a_4189_);
lean_inc_ref(v_a_4188_);
lean_inc(v_a_4187_);
lean_inc_ref(v_a_4186_);
lean_inc(v_a_4185_);
v___x_4253_ = lean_apply_11(v_kna_4183_, v_goal_4182_, v_a_4185_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_, lean_box(0));
return v___x_4253_;
}
}
}
else
{
lean_object* v___x_4255_; lean_object* v___x_4256_; 
lean_dec_ref(v_toGoalState_4195_);
lean_dec_ref(v_kp_4184_);
lean_dec_ref(v_kna_4183_);
lean_dec_ref(v_goal_4182_);
v___x_4255_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intro___closed__0));
v___x_4256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4255_);
return v___x_4256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext___boxed(lean_object* v_goal_4257_, lean_object* v_kna_4258_, lean_object* v_kp_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l_Lean_Meta_Grind_Action_assertNext(v_goal_4257_, v_kna_4258_, v_kp_4259_, v_a_4260_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_, v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_);
lean_dec(v_a_4268_);
lean_dec_ref(v_a_4267_);
lean_dec(v_a_4266_);
lean_dec_ref(v_a_4265_);
lean_dec(v_a_4264_);
lean_dec_ref(v_a_4263_);
lean_dec(v_a_4262_);
lean_dec_ref(v_a_4261_);
lean_dec(v_a_4260_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg(lean_object* v_a_4271_, lean_object* v_kp_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_){
_start:
{
lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; 
v___x_4283_ = lean_unsigned_to_nat(1000000u);
v___x_4284_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_assertNext___boxed), 13, 0);
v___x_4285_ = l_Lean_Meta_Grind_Action_loop___redArg(v___x_4283_, v___x_4284_, v_a_4271_, v_kp_4272_, v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_);
return v___x_4285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg___boxed(lean_object* v_a_4286_, lean_object* v_kp_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_){
_start:
{
lean_object* v_res_4298_; 
v_res_4298_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4286_, v_kp_4287_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_);
lean_dec(v_a_4296_);
lean_dec_ref(v_a_4295_);
lean_dec(v_a_4294_);
lean_dec_ref(v_a_4293_);
lean_dec(v_a_4292_);
lean_dec_ref(v_a_4291_);
lean_dec(v_a_4290_);
lean_dec_ref(v_a_4289_);
lean_dec(v_a_4288_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll(lean_object* v_a_4299_, lean_object* v_kna_4300_, lean_object* v_kp_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_){
_start:
{
lean_object* v___x_4312_; 
v___x_4312_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4299_, v_kp_4301_, v_a_4302_, v_a_4303_, v_a_4304_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_);
return v___x_4312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___boxed(lean_object* v_a_4313_, lean_object* v_kna_4314_, lean_object* v_kp_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_){
_start:
{
lean_object* v_res_4326_; 
v_res_4326_ = l_Lean_Meta_Grind_Action_assertAll(v_a_4313_, v_kna_4314_, v_kp_4315_, v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_, v_a_4324_);
lean_dec(v_a_4324_);
lean_dec_ref(v_a_4323_);
lean_dec(v_a_4322_);
lean_dec_ref(v_a_4321_);
lean_dec(v_a_4320_);
lean_dec_ref(v_a_4319_);
lean_dec(v_a_4318_);
lean_dec_ref(v_a_4317_);
lean_dec(v_a_4316_);
lean_dec_ref(v_kna_4314_);
return v_res_4326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__0(lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_){
_start:
{
lean_object* v___x_4340_; 
v___x_4340_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_4327_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
return v___x_4340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__0___boxed(lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_){
_start:
{
lean_object* v_res_4354_; 
v_res_4354_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__0(v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_);
lean_dec(v___y_4352_);
lean_dec_ref(v___y_4351_);
lean_dec(v___y_4350_);
lean_dec_ref(v___y_4349_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4342_);
return v_res_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__1(lean_object* v_a_4355_, lean_object* v___f_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_){
_start:
{
lean_object* v___x_4370_; 
v___x_4370_ = l_Lean_Meta_Grind_Action_andThen(v_a_4355_, v___f_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed(lean_object* v_a_4371_, lean_object* v___f_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
lean_object* v_res_4386_; 
v_res_4386_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__1(v_a_4371_, v___f_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4383_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
lean_dec(v___y_4378_);
lean_dec_ref(v___y_4377_);
lean_dec(v___y_4376_);
return v_res_4386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction(){
_start:
{
lean_object* v___f_4389_; lean_object* v___x_4390_; 
v___f_4389_ = ((lean_object*)(l_Lean_Meta_Grind_Solvers_mkAction___closed__0));
v___x_4390_ = l_Lean_Meta_Grind_Solvers_mkActionCore();
if (lean_obj_tag(v___x_4390_) == 0)
{
lean_object* v_a_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4399_; 
v_a_4391_ = lean_ctor_get(v___x_4390_, 0);
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4393_ = v___x_4390_;
v_isShared_4394_ = v_isSharedCheck_4399_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_a_4391_);
lean_dec(v___x_4390_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4399_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___f_4395_; lean_object* v___x_4397_; 
v___f_4395_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed), 15, 2);
lean_closure_set(v___f_4395_, 0, v_a_4391_);
lean_closure_set(v___f_4395_, 1, v___f_4389_);
if (v_isShared_4394_ == 0)
{
lean_ctor_set(v___x_4393_, 0, v___f_4395_);
v___x_4397_ = v___x_4393_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v___f_4395_);
v___x_4397_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
return v___x_4397_;
}
}
}
else
{
return v___x_4390_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___boxed(lean_object* v_a_4400_){
_start:
{
lean_object* v_res_4401_; 
v_res_4401_ = l_Lean_Meta_Grind_Solvers_mkAction();
return v_res_4401_;
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
