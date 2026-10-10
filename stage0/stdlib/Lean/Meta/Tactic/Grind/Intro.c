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
lean_object* l_Lean_Meta_Grind_preprocessHypothesis(lean_object* v_e_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_){
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
LEAN_EXPORT void l_Lean_Meta_Grind_preprocessHypothesis_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_80_ = stack[0].m_obj;
lean_object* v_a_81_ = stack[1].m_obj;
lean_object* v_a_82_ = stack[2].m_obj;
lean_object* v_a_83_ = stack[3].m_obj;
lean_object* v_a_84_ = stack[4].m_obj;
lean_object* v_a_85_ = stack[5].m_obj;
lean_object* v_a_86_ = stack[6].m_obj;
lean_object* v_a_87_ = stack[7].m_obj;
lean_object* v_a_88_ = stack[8].m_obj;
lean_object* v_a_89_ = stack[9].m_obj;
lean_object* v_a_90_ = stack[10].m_obj;
lean_object* v_res_128_;
v_res_128_ = l_Lean_Meta_Grind_preprocessHypothesis(v_e_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
stack->m_obj
 = v_res_128_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessHypothesis___boxed(lean_object* v_e_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Meta_Grind_preprocessHypothesis(v_e_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
lean_dec(v_a_135_);
lean_dec_ref(v_a_134_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec(v_a_130_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(lean_object* v___x_142_, lean_object* v_str_143_, lean_object* v_a_144_, lean_object* v_b_145_){
_start:
{
uint8_t v_decide_146_; 
v_decide_146_ = lean_nat_dec_eq(v_a_144_, v___x_142_);
if (v_decide_146_ == 0)
{
uint32_t v___x_147_; uint32_t v___x_148_; uint8_t v___x_149_; 
v___x_147_ = lean_string_utf8_get_fast(v_str_143_, v_a_144_);
v___x_148_ = 95;
v___x_149_ = lean_uint32_dec_eq(v___x_147_, v___x_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_box(0);
v___x_151_ = lean_string_utf8_next_fast(v_str_143_, v_a_144_);
lean_dec(v_a_144_);
v_a_144_ = v___x_151_;
v_b_145_ = v___x_150_;
goto _start;
}
else
{
lean_object* v___x_153_; 
v___x_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_153_, 0, v_a_144_);
return v___x_153_;
}
}
else
{
lean_dec(v_a_144_);
lean_inc(v_b_145_);
return v_b_145_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg___boxed(lean_object* v___x_154_, lean_object* v_str_155_, lean_object* v_a_156_, lean_object* v_b_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_154_, v_str_155_, v_a_156_, v_b_157_);
lean_dec(v_b_157_);
lean_dec_ref(v_str_155_);
lean_dec(v___x_154_);
return v_res_158_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(lean_object* v_name_165_, lean_object* v_type_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___y_175_; lean_object* v___y_176_; 
if (lean_obj_tag(v_name_165_) == 1)
{
lean_object* v_str_200_; lean_object* v___y_202_; lean_object* v_searcher_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v_str_200_ = lean_ctor_get(v_name_165_, 1);
lean_inc_ref(v_str_200_);
lean_dec_ref_known(v_name_165_, 2);
v_searcher_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = lean_string_utf8_byte_size(v_str_200_);
v___x_222_ = lean_box(0);
v___x_223_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_221_, v_str_200_, v_searcher_220_, v___x_222_);
if (lean_obj_tag(v___x_223_) == 0)
{
v___y_202_ = v___x_221_;
goto v___jp_201_;
}
else
{
lean_object* v_val_224_; 
v_val_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_val_224_);
lean_dec_ref_known(v___x_223_, 1);
v___y_202_ = v_val_224_;
goto v___jp_201_;
}
v___jp_201_:
{
lean_object* v___x_203_; uint8_t v_decide_204_; 
v___x_203_ = lean_string_utf8_byte_size(v_str_200_);
v_decide_204_ = lean_nat_dec_eq(v___y_202_, v___x_203_);
if (v_decide_204_ == 0)
{
lean_object* v___x_205_; lean_object* v_suffix_206_; uint8_t v___x_207_; 
v___x_205_ = lean_string_utf8_next_fast(v_str_200_, v___y_202_);
lean_inc_ref(v_str_200_);
v_suffix_206_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_suffix_206_, 0, v_str_200_);
lean_ctor_set(v_suffix_206_, 1, v___x_205_);
lean_ctor_set(v_suffix_206_, 2, v___x_203_);
v___x_207_ = l_String_Slice_isNat(v_suffix_206_);
lean_dec_ref_known(v_suffix_206_, 3);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
lean_dec(v___y_202_);
lean_dec_ref(v_type_166_);
v___x_208_ = lean_box(0);
v___x_209_ = l_Lean_Name_str___override(v___x_208_, v_str_200_);
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
return v___x_210_;
}
else
{
lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = lean_nat_dec_eq(v___y_202_, v___x_211_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
lean_dec_ref(v_type_166_);
v___x_213_ = lean_string_utf8_extract_fast(v_str_200_, v___x_211_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v_str_200_);
v___x_214_ = lean_box(0);
v___x_215_ = l_Lean_Name_str___override(v___x_214_, v___x_213_);
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
return v___x_216_;
}
else
{
lean_dec(v___y_202_);
lean_dec_ref(v_str_200_);
v___y_173_ = v_a_167_;
v___y_174_ = v_a_168_;
v___y_175_ = v_a_169_;
v___y_176_ = v_a_170_;
goto v___jp_172_;
}
}
}
else
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
lean_dec(v___y_202_);
lean_dec_ref(v_type_166_);
v___x_217_ = lean_box(0);
v___x_218_ = l_Lean_Name_str___override(v___x_217_, v_str_200_);
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
return v___x_219_;
}
}
}
else
{
lean_dec(v_name_165_);
v___y_173_ = v_a_167_;
v___y_174_ = v_a_168_;
v___y_175_ = v_a_169_;
v___y_176_ = v_a_170_;
goto v___jp_172_;
}
v___jp_172_:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_Meta_isProp(v_type_166_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_191_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_191_ == 0)
{
v___x_180_ = v___x_177_;
v_isShared_181_ = v_isSharedCheck_191_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_177_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_191_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
uint8_t v___x_182_; 
v___x_182_ = lean_unbox(v_a_178_);
lean_dec(v_a_178_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_183_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_183_);
v___x_185_ = v___x_180_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_183_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
else
{
lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_187_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_187_);
v___x_189_ = v___x_180_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
v_a_192_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_177_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_177_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_165_ = stack[0].m_obj;
lean_object* v_type_166_ = stack[1].m_obj;
lean_object* v_a_167_ = stack[2].m_obj;
lean_object* v_a_168_ = stack[3].m_obj;
lean_object* v_a_169_ = stack[4].m_obj;
lean_object* v_a_170_ = stack[5].m_obj;
lean_object* v_res_225_;
v_res_225_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(v_name_165_, v_type_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_);
stack->m_obj
 = v_res_225_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___boxed(lean_object* v_name_226_, lean_object* v_type_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(v_name_226_, v_type_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
lean_dec(v_a_231_);
lean_dec_ref(v_a_230_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0(lean_object* v___x_234_, lean_object* v___x_235_, lean_object* v_str_236_, lean_object* v_inst_237_, lean_object* v_R_238_, lean_object* v_a_239_, lean_object* v_b_240_, lean_object* v_c_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_234_, v_str_236_, v_a_239_, v_b_240_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___boxed(lean_object* v___x_243_, lean_object* v___x_244_, lean_object* v_str_245_, lean_object* v_inst_246_, lean_object* v_R_247_, lean_object* v_a_248_, lean_object* v_b_249_, lean_object* v_c_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0(v___x_243_, v___x_244_, v_str_245_, v_inst_246_, v_R_247_, v_a_248_, v_b_249_, v_c_250_);
lean_dec(v_b_249_);
lean_dec_ref(v_str_245_);
lean_dec_ref(v___x_244_);
lean_dec(v___x_243_);
return v_res_251_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(lean_object* v_keys_252_, lean_object* v_i_253_, lean_object* v_k_254_){
_start:
{
lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_255_ = lean_array_get_size(v_keys_252_);
v___x_256_ = lean_nat_dec_lt(v_i_253_, v___x_255_);
if (v___x_256_ == 0)
{
lean_dec(v_i_253_);
return v___x_256_;
}
else
{
lean_object* v_k_x27_257_; uint8_t v___x_258_; 
v_k_x27_257_ = lean_array_fget_borrowed(v_keys_252_, v_i_253_);
v___x_258_ = lean_name_eq(v_k_254_, v_k_x27_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_unsigned_to_nat(1u);
v___x_260_ = lean_nat_add(v_i_253_, v___x_259_);
lean_dec(v_i_253_);
v_i_253_ = v___x_260_;
goto _start;
}
else
{
lean_dec(v_i_253_);
return v___x_256_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_252_ = stack[0].m_obj;
lean_object* v_i_253_ = stack[1].m_obj;
lean_object* v_k_254_ = stack[2].m_obj;
uint8_t v_res_262_;
v_res_262_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_keys_252_, v_i_253_, v_k_254_);
stack->m_num = v_res_262_;
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
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(lean_object* v_x_268_, size_t v_x_269_, lean_object* v_x_270_){
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
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_268_ = stack[0].m_obj;
size_t v_x_269_ = stack[1].m_num;
lean_object* v_x_270_ = stack[2].m_obj;
uint8_t v_res_287_;
v_res_287_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_268_, v_x_269_, v_x_270_);
stack->m_num = v_res_287_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___boxed(lean_object* v_x_288_, lean_object* v_x_289_, lean_object* v_x_290_){
_start:
{
size_t v_x_32934__boxed_291_; uint8_t v_res_292_; lean_object* v_r_293_; 
v_x_32934__boxed_291_ = lean_unbox_usize(v_x_289_);
lean_dec(v_x_289_);
v_res_292_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_288_, v_x_32934__boxed_291_, v_x_290_);
lean_dec(v_x_290_);
lean_dec_ref(v_x_288_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(lean_object* v_x_294_, lean_object* v_x_295_){
_start:
{
uint64_t v___y_297_; 
if (lean_obj_tag(v_x_295_) == 0)
{
uint64_t v___x_300_; 
v___x_300_ = 1723ULL;
v___y_297_ = v___x_300_;
goto v___jp_296_;
}
else
{
uint64_t v_hash_301_; 
v_hash_301_ = lean_ctor_get_uint64(v_x_295_, sizeof(void*)*2);
v___y_297_ = v_hash_301_;
goto v___jp_296_;
}
v___jp_296_:
{
size_t v___x_298_; uint8_t v___x_299_; 
v___x_298_ = lean_uint64_to_usize(v___y_297_);
v___x_299_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_294_, v___x_298_, v_x_295_);
return v___x_299_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_294_ = stack[0].m_obj;
lean_object* v_x_295_ = stack[1].m_obj;
uint8_t v_res_302_;
v_res_302_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_x_294_, v_x_295_);
stack->m_num = v_res_302_;
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
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_snd_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_331_; 
v_snd_311_ = lean_ctor_get(v_a_308_, 1);
v_isSharedCheck_331_ = !lean_is_exclusive(v_a_308_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; 
v_unused_332_ = lean_ctor_get(v_a_308_, 0);
lean_dec(v_unused_332_);
v___x_313_ = v_a_308_;
v_isShared_314_ = v_isSharedCheck_331_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_snd_311_);
lean_dec(v_a_308_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_331_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v_toGoalState_319_; lean_object* v_clean_320_; lean_object* v_used_321_; uint8_t v___x_322_; 
lean_inc(v_snd_311_);
lean_inc(v_a_307_);
v___x_315_ = lean_name_append_index_after(v_a_307_, v_snd_311_);
v___x_316_ = lean_unsigned_to_nat(1u);
v___x_317_ = lean_nat_add(v_snd_311_, v___x_316_);
lean_dec(v_snd_311_);
v___x_318_ = lean_st_ref_get(v___y_309_);
v_toGoalState_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc_ref(v_toGoalState_319_);
lean_dec(v___x_318_);
v_clean_320_ = lean_ctor_get(v_toGoalState_319_, 15);
lean_inc_ref(v_clean_320_);
lean_dec_ref(v_toGoalState_319_);
v_used_321_ = lean_ctor_get(v_clean_320_, 0);
lean_inc_ref(v_used_321_);
lean_dec_ref(v_clean_320_);
v___x_322_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_used_321_, v___x_315_);
lean_dec_ref(v_used_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_324_; 
lean_dec(v_a_307_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 1, v___x_317_);
lean_ctor_set(v___x_313_, 0, v___x_315_);
v___x_324_ = v___x_313_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_315_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v___x_317_);
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
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 1, v___x_317_);
lean_ctor_set(v___x_313_, 0, v___x_315_);
v___x_328_ = v___x_313_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_315_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v___x_317_);
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
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_307_ = stack[0].m_obj;
lean_object* v_a_308_ = stack[1].m_obj;
lean_object* v___y_309_ = stack[2].m_obj;
lean_object* v_res_333_;
v_res_333_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v_a_307_, v_a_308_, v___y_309_);
stack->m_obj
 = v_res_333_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg___boxed(lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v_a_334_, v_a_335_, v___y_336_);
lean_dec(v___y_336_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_339_, lean_object* v_x_340_, lean_object* v_x_341_, lean_object* v_x_342_){
_start:
{
lean_object* v_ks_343_; lean_object* v_vs_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_368_; 
v_ks_343_ = lean_ctor_get(v_x_339_, 0);
v_vs_344_ = lean_ctor_get(v_x_339_, 1);
v_isSharedCheck_368_ = !lean_is_exclusive(v_x_339_);
if (v_isSharedCheck_368_ == 0)
{
v___x_346_ = v_x_339_;
v_isShared_347_ = v_isSharedCheck_368_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_vs_344_);
lean_inc(v_ks_343_);
lean_dec(v_x_339_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_368_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = lean_array_get_size(v_ks_343_);
v___x_349_ = lean_nat_dec_lt(v_x_340_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_353_; 
lean_dec(v_x_340_);
v___x_350_ = lean_array_push(v_ks_343_, v_x_341_);
v___x_351_ = lean_array_push(v_vs_344_, v_x_342_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v___x_351_);
lean_ctor_set(v___x_346_, 0, v___x_350_);
v___x_353_ = v___x_346_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
else
{
lean_object* v_k_x27_355_; uint8_t v___x_356_; 
v_k_x27_355_ = lean_array_fget_borrowed(v_ks_343_, v_x_340_);
v___x_356_ = lean_name_eq(v_x_341_, v_k_x27_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_358_; 
if (v_isShared_347_ == 0)
{
v___x_358_ = v___x_346_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_ks_343_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_vs_344_);
v___x_358_ = v_reuseFailAlloc_362_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_unsigned_to_nat(1u);
v___x_360_ = lean_nat_add(v_x_340_, v___x_359_);
lean_dec(v_x_340_);
v_x_339_ = v___x_358_;
v_x_340_ = v___x_360_;
goto _start;
}
}
else
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_363_ = lean_array_fset(v_ks_343_, v_x_340_, v_x_341_);
v___x_364_ = lean_array_fset(v_vs_344_, v_x_340_, v_x_342_);
lean_dec(v_x_340_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v___x_364_);
lean_ctor_set(v___x_346_, 0, v___x_363_);
v___x_366_ = v___x_346_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v___x_364_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(lean_object* v_n_369_, lean_object* v_k_370_, lean_object* v_v_371_){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_unsigned_to_nat(0u);
v___x_373_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(v_n_369_, v___x_372_, v_k_370_, v_v_371_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_374_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(lean_object* v_x_375_, size_t v_x_376_, size_t v_x_377_, lean_object* v_x_378_, lean_object* v_x_379_){
_start:
{
if (lean_obj_tag(v_x_375_) == 0)
{
lean_object* v_es_380_; size_t v___x_381_; size_t v___x_382_; lean_object* v_j_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
v_es_380_ = lean_ctor_get(v_x_375_, 0);
v___x_381_ = ((size_t)31ULL);
v___x_382_ = lean_usize_land(v_x_376_, v___x_381_);
v_j_383_ = lean_usize_to_nat(v___x_382_);
v___x_384_ = lean_array_get_size(v_es_380_);
v___x_385_ = lean_nat_dec_lt(v_j_383_, v___x_384_);
if (v___x_385_ == 0)
{
lean_dec(v_j_383_);
lean_dec(v_x_379_);
lean_dec(v_x_378_);
return v_x_375_;
}
else
{
lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_424_; 
lean_inc_ref(v_es_380_);
v_isSharedCheck_424_ = !lean_is_exclusive(v_x_375_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; 
v_unused_425_ = lean_ctor_get(v_x_375_, 0);
lean_dec(v_unused_425_);
v___x_387_ = v_x_375_;
v_isShared_388_ = v_isSharedCheck_424_;
goto v_resetjp_386_;
}
else
{
lean_dec(v_x_375_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_424_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v_v_389_; lean_object* v___x_390_; lean_object* v_xs_x27_391_; lean_object* v___y_393_; 
v_v_389_ = lean_array_fget(v_es_380_, v_j_383_);
v___x_390_ = lean_box(0);
v_xs_x27_391_ = lean_array_fset(v_es_380_, v_j_383_, v___x_390_);
switch(lean_obj_tag(v_v_389_))
{
case 0:
{
lean_object* v_key_398_; lean_object* v_val_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_409_; 
v_key_398_ = lean_ctor_get(v_v_389_, 0);
v_val_399_ = lean_ctor_get(v_v_389_, 1);
v_isSharedCheck_409_ = !lean_is_exclusive(v_v_389_);
if (v_isSharedCheck_409_ == 0)
{
v___x_401_ = v_v_389_;
v_isShared_402_ = v_isSharedCheck_409_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_val_399_);
lean_inc(v_key_398_);
lean_dec(v_v_389_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_409_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
uint8_t v___x_403_; 
v___x_403_ = lean_name_eq(v_x_378_, v_key_398_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_del_object(v___x_401_);
v___x_404_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_398_, v_val_399_, v_x_378_, v_x_379_);
v___x_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
v___y_393_ = v___x_405_;
goto v___jp_392_;
}
else
{
lean_object* v___x_407_; 
lean_dec(v_val_399_);
lean_dec(v_key_398_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 1, v_x_379_);
lean_ctor_set(v___x_401_, 0, v_x_378_);
v___x_407_ = v___x_401_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_x_378_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_x_379_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
v___y_393_ = v___x_407_;
goto v___jp_392_;
}
}
}
}
case 1:
{
lean_object* v_node_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_422_; 
v_node_410_ = lean_ctor_get(v_v_389_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v_v_389_);
if (v_isSharedCheck_422_ == 0)
{
v___x_412_ = v_v_389_;
v_isShared_413_ = v_isSharedCheck_422_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_node_410_);
lean_dec(v_v_389_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_422_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
size_t v___x_414_; size_t v___x_415_; size_t v___x_416_; size_t v___x_417_; lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_414_ = ((size_t)5ULL);
v___x_415_ = lean_usize_shift_right(v_x_376_, v___x_414_);
v___x_416_ = ((size_t)1ULL);
v___x_417_ = lean_usize_add(v_x_377_, v___x_416_);
v___x_418_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_node_410_, v___x_415_, v___x_417_, v_x_378_, v_x_379_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_418_);
v___x_420_ = v___x_412_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
v___y_393_ = v___x_420_;
goto v___jp_392_;
}
}
}
default: 
{
lean_object* v___x_423_; 
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v_x_378_);
lean_ctor_set(v___x_423_, 1, v_x_379_);
v___y_393_ = v___x_423_;
goto v___jp_392_;
}
}
v___jp_392_:
{
lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_394_ = lean_array_fset(v_xs_x27_391_, v_j_383_, v___y_393_);
lean_dec(v_j_383_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v___x_394_);
v___x_396_ = v___x_387_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_394_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
}
else
{
lean_object* v_ks_426_; lean_object* v_vs_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_445_; 
v_ks_426_ = lean_ctor_get(v_x_375_, 0);
v_vs_427_ = lean_ctor_get(v_x_375_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v_x_375_);
if (v_isSharedCheck_445_ == 0)
{
v___x_429_ = v_x_375_;
v_isShared_430_ = v_isSharedCheck_445_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_vs_427_);
lean_inc(v_ks_426_);
lean_dec(v_x_375_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_445_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_ks_426_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_vs_427_);
v___x_432_ = v_reuseFailAlloc_444_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v_newNode_433_; size_t v___x_434_; uint8_t v___x_435_; 
v_newNode_433_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(v___x_432_, v_x_378_, v_x_379_);
v___x_434_ = ((size_t)7ULL);
v___x_435_ = lean_usize_dec_le(v___x_434_, v_x_377_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_436_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_433_);
v___x_437_ = lean_unsigned_to_nat(4u);
v___x_438_ = lean_nat_dec_lt(v___x_436_, v___x_437_);
lean_dec(v___x_436_);
if (v___x_438_ == 0)
{
lean_object* v_ks_439_; lean_object* v_vs_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v_ks_439_ = lean_ctor_get(v_newNode_433_, 0);
lean_inc_ref(v_ks_439_);
v_vs_440_ = lean_ctor_get(v_newNode_433_, 1);
lean_inc_ref(v_vs_440_);
lean_dec_ref(v_newNode_433_);
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0);
v___x_443_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_x_377_, v_ks_439_, v_vs_440_, v___x_441_, v___x_442_);
lean_dec_ref(v_vs_440_);
lean_dec_ref(v_ks_439_);
return v___x_443_;
}
else
{
return v_newNode_433_;
}
}
else
{
return v_newNode_433_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_375_ = stack[0].m_obj;
size_t v_x_376_ = stack[1].m_num;
size_t v_x_377_ = stack[2].m_num;
lean_object* v_x_378_ = stack[3].m_obj;
lean_object* v_x_379_ = stack[4].m_obj;
lean_object* v_res_446_;
v_res_446_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_375_, v_x_376_, v_x_377_, v_x_378_, v_x_379_);
stack->m_obj
 = v_res_446_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(size_t v_depth_447_, lean_object* v_keys_448_, lean_object* v_vals_449_, lean_object* v_i_450_, lean_object* v_entries_451_){
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
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_447_ = stack[0].m_num;
lean_object* v_keys_448_ = stack[1].m_obj;
lean_object* v_vals_449_ = stack[2].m_obj;
lean_object* v_i_450_ = stack[3].m_obj;
lean_object* v_entries_451_ = stack[4].m_obj;
lean_object* v_res_470_;
v_res_470_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_depth_447_, v_keys_448_, v_vals_449_, v_i_450_, v_entries_451_);
stack->m_obj
 = v_res_470_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_471_, lean_object* v_keys_472_, lean_object* v_vals_473_, lean_object* v_i_474_, lean_object* v_entries_475_){
_start:
{
size_t v_depth_boxed_476_; lean_object* v_res_477_; 
v_depth_boxed_476_ = lean_unbox_usize(v_depth_471_);
lean_dec(v_depth_471_);
v_res_477_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_depth_boxed_476_, v_keys_472_, v_vals_473_, v_i_474_, v_entries_475_);
lean_dec_ref(v_vals_473_);
lean_dec_ref(v_keys_472_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___boxed(lean_object* v_x_478_, lean_object* v_x_479_, lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v_x_482_){
_start:
{
size_t v_x_33199__boxed_483_; size_t v_x_33200__boxed_484_; lean_object* v_res_485_; 
v_x_33199__boxed_483_ = lean_unbox_usize(v_x_479_);
lean_dec(v_x_479_);
v_x_33200__boxed_484_ = lean_unbox_usize(v_x_480_);
lean_dec(v_x_480_);
v_res_485_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_478_, v_x_33199__boxed_483_, v_x_33200__boxed_484_, v_x_481_, v_x_482_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(lean_object* v_x_486_, lean_object* v_x_487_, lean_object* v_x_488_){
_start:
{
uint64_t v___y_490_; 
if (lean_obj_tag(v_x_487_) == 0)
{
uint64_t v___x_494_; 
v___x_494_ = 1723ULL;
v___y_490_ = v___x_494_;
goto v___jp_489_;
}
else
{
uint64_t v_hash_495_; 
v_hash_495_ = lean_ctor_get_uint64(v_x_487_, sizeof(void*)*2);
v___y_490_ = v_hash_495_;
goto v___jp_489_;
}
v___jp_489_:
{
size_t v___x_491_; size_t v___x_492_; lean_object* v___x_493_; 
v___x_491_ = lean_uint64_to_usize(v___y_490_);
v___x_492_ = ((size_t)1ULL);
v___x_493_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_486_, v___x_491_, v___x_492_, v_x_487_, v_x_488_);
return v___x_493_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(lean_object* v_keys_496_, lean_object* v_vals_497_, lean_object* v_i_498_, lean_object* v_k_499_){
_start:
{
lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_500_ = lean_array_get_size(v_keys_496_);
v___x_501_ = lean_nat_dec_lt(v_i_498_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
lean_dec(v_i_498_);
v___x_502_ = lean_box(0);
return v___x_502_;
}
else
{
lean_object* v_k_x27_503_; uint8_t v___x_504_; 
v_k_x27_503_ = lean_array_fget_borrowed(v_keys_496_, v_i_498_);
v___x_504_ = lean_name_eq(v_k_499_, v_k_x27_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_unsigned_to_nat(1u);
v___x_506_ = lean_nat_add(v_i_498_, v___x_505_);
lean_dec(v_i_498_);
v_i_498_ = v___x_506_;
goto _start;
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_array_fget_borrowed(v_vals_497_, v_i_498_);
lean_dec(v_i_498_);
lean_inc(v___x_508_);
v___x_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_keys_510_, lean_object* v_vals_511_, lean_object* v_i_512_, lean_object* v_k_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_keys_510_, v_vals_511_, v_i_512_, v_k_513_);
lean_dec(v_k_513_);
lean_dec_ref(v_vals_511_);
lean_dec_ref(v_keys_510_);
return v_res_514_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(lean_object* v_x_515_, size_t v_x_516_, lean_object* v_x_517_){
_start:
{
if (lean_obj_tag(v_x_515_) == 0)
{
lean_object* v_es_518_; lean_object* v___x_519_; size_t v___x_520_; size_t v___x_521_; lean_object* v_j_522_; lean_object* v___x_523_; 
v_es_518_ = lean_ctor_get(v_x_515_, 0);
v___x_519_ = lean_box(2);
v___x_520_ = ((size_t)31ULL);
v___x_521_ = lean_usize_land(v_x_516_, v___x_520_);
v_j_522_ = lean_usize_to_nat(v___x_521_);
v___x_523_ = lean_array_get_borrowed(v___x_519_, v_es_518_, v_j_522_);
lean_dec(v_j_522_);
switch(lean_obj_tag(v___x_523_))
{
case 0:
{
lean_object* v_key_524_; lean_object* v_val_525_; uint8_t v___x_526_; 
v_key_524_ = lean_ctor_get(v___x_523_, 0);
v_val_525_ = lean_ctor_get(v___x_523_, 1);
v___x_526_ = lean_name_eq(v_x_517_, v_key_524_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; 
v___x_527_ = lean_box(0);
return v___x_527_;
}
else
{
lean_object* v___x_528_; 
lean_inc(v_val_525_);
v___x_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_528_, 0, v_val_525_);
return v___x_528_;
}
}
case 1:
{
lean_object* v_node_529_; size_t v___x_530_; size_t v___x_531_; 
v_node_529_ = lean_ctor_get(v___x_523_, 0);
v___x_530_ = ((size_t)5ULL);
v___x_531_ = lean_usize_shift_right(v_x_516_, v___x_530_);
v_x_515_ = v_node_529_;
v_x_516_ = v___x_531_;
goto _start;
}
default: 
{
lean_object* v___x_533_; 
v___x_533_ = lean_box(0);
return v___x_533_;
}
}
}
else
{
lean_object* v_ks_534_; lean_object* v_vs_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v_ks_534_ = lean_ctor_get(v_x_515_, 0);
v_vs_535_ = lean_ctor_get(v_x_515_, 1);
v___x_536_ = lean_unsigned_to_nat(0u);
v___x_537_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_ks_534_, v_vs_535_, v___x_536_, v_x_517_);
return v___x_537_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_515_ = stack[0].m_obj;
size_t v_x_516_ = stack[1].m_num;
lean_object* v_x_517_ = stack[2].m_obj;
lean_object* v_res_538_;
v_res_538_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_515_, v_x_516_, v_x_517_);
stack->m_obj
 = v_res_538_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg___boxed(lean_object* v_x_539_, lean_object* v_x_540_, lean_object* v_x_541_){
_start:
{
size_t v_x_33493__boxed_542_; lean_object* v_res_543_; 
v_x_33493__boxed_542_ = lean_unbox_usize(v_x_540_);
lean_dec(v_x_540_);
v_res_543_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_539_, v_x_33493__boxed_542_, v_x_541_);
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
v___x_550_ = 1723ULL;
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
lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(lean_object* v_name_558_, lean_object* v_type_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
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
v_clean_751_ = lean_ctor_get_uint8(v_a_726_, sizeof(void*)*14 + 16);
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
lean_object* v_nextDeclIdx_581_; lean_object* v_enodeMap_582_; lean_object* v_exprs_583_; lean_object* v_parents_584_; lean_object* v_congrTable_585_; lean_object* v_appMap_586_; lean_object* v_indicesFound_587_; lean_object* v_toProcess_588_; uint8_t v_inconsistent_589_; lean_object* v_nextIdx_590_; lean_object* v_newRawFacts_591_; lean_object* v_facts_592_; lean_object* v_extThms_593_; lean_object* v_ematch_594_; lean_object* v_inj_595_; lean_object* v_split_596_; lean_object* v_sstates_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_620_; 
v_nextDeclIdx_581_ = lean_ctor_get(v_toGoalState_575_, 0);
v_enodeMap_582_ = lean_ctor_get(v_toGoalState_575_, 1);
v_exprs_583_ = lean_ctor_get(v_toGoalState_575_, 2);
v_parents_584_ = lean_ctor_get(v_toGoalState_575_, 3);
v_congrTable_585_ = lean_ctor_get(v_toGoalState_575_, 4);
v_appMap_586_ = lean_ctor_get(v_toGoalState_575_, 5);
v_indicesFound_587_ = lean_ctor_get(v_toGoalState_575_, 6);
v_toProcess_588_ = lean_ctor_get(v_toGoalState_575_, 7);
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
lean_inc(v_toProcess_588_);
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
lean_ctor_set(v_reuseFailAlloc_617_, 7, v_toProcess_588_);
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
v___x_614_ = lean_st_ref_put(v___y_573_, v___x_613_);
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
lean_ctor_set(v___x_638_, 0, v___y_632_);
lean_ctor_set(v___x_638_, 1, v___y_637_);
lean_inc(v___y_627_);
v___x_639_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v___y_627_, v___x_638_, v___y_628_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v_fst_641_; lean_object* v_snd_642_; lean_object* v___x_643_; lean_object* v_toGoalState_644_; lean_object* v_clean_645_; lean_object* v_mvarId_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_689_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref_known(v___x_639_, 1);
v_fst_641_ = lean_ctor_get(v_a_640_, 0);
lean_inc(v_fst_641_);
v_snd_642_ = lean_ctor_get(v_a_640_, 1);
lean_inc(v_snd_642_);
lean_dec(v_a_640_);
v___x_643_ = lean_st_ref_take(v___y_628_);
v_toGoalState_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc_ref(v_toGoalState_644_);
v_clean_645_ = lean_ctor_get(v_toGoalState_644_, 15);
lean_inc_ref(v_clean_645_);
v_mvarId_646_ = lean_ctor_get(v___x_643_, 1);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_689_ == 0)
{
lean_object* v_unused_690_; 
v_unused_690_ = lean_ctor_get(v___x_643_, 0);
lean_dec(v_unused_690_);
v___x_648_ = v___x_643_;
v_isShared_649_ = v_isSharedCheck_689_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_mvarId_646_);
lean_dec(v___x_643_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_689_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v_nextDeclIdx_650_; lean_object* v_enodeMap_651_; lean_object* v_exprs_652_; lean_object* v_parents_653_; lean_object* v_congrTable_654_; lean_object* v_appMap_655_; lean_object* v_indicesFound_656_; lean_object* v_toProcess_657_; uint8_t v_inconsistent_658_; lean_object* v_nextIdx_659_; lean_object* v_newRawFacts_660_; lean_object* v_facts_661_; lean_object* v_extThms_662_; lean_object* v_ematch_663_; lean_object* v_inj_664_; lean_object* v_split_665_; lean_object* v_sstates_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_687_; 
v_nextDeclIdx_650_ = lean_ctor_get(v_toGoalState_644_, 0);
v_enodeMap_651_ = lean_ctor_get(v_toGoalState_644_, 1);
v_exprs_652_ = lean_ctor_get(v_toGoalState_644_, 2);
v_parents_653_ = lean_ctor_get(v_toGoalState_644_, 3);
v_congrTable_654_ = lean_ctor_get(v_toGoalState_644_, 4);
v_appMap_655_ = lean_ctor_get(v_toGoalState_644_, 5);
v_indicesFound_656_ = lean_ctor_get(v_toGoalState_644_, 6);
v_toProcess_657_ = lean_ctor_get(v_toGoalState_644_, 7);
v_inconsistent_658_ = lean_ctor_get_uint8(v_toGoalState_644_, sizeof(void*)*17);
v_nextIdx_659_ = lean_ctor_get(v_toGoalState_644_, 8);
v_newRawFacts_660_ = lean_ctor_get(v_toGoalState_644_, 9);
v_facts_661_ = lean_ctor_get(v_toGoalState_644_, 10);
v_extThms_662_ = lean_ctor_get(v_toGoalState_644_, 11);
v_ematch_663_ = lean_ctor_get(v_toGoalState_644_, 12);
v_inj_664_ = lean_ctor_get(v_toGoalState_644_, 13);
v_split_665_ = lean_ctor_get(v_toGoalState_644_, 14);
v_sstates_666_ = lean_ctor_get(v_toGoalState_644_, 16);
v_isSharedCheck_687_ = !lean_is_exclusive(v_toGoalState_644_);
if (v_isSharedCheck_687_ == 0)
{
lean_object* v_unused_688_; 
v_unused_688_ = lean_ctor_get(v_toGoalState_644_, 15);
lean_dec(v_unused_688_);
v___x_668_ = v_toGoalState_644_;
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
lean_inc(v_toProcess_657_);
lean_inc(v_indicesFound_656_);
lean_inc(v_appMap_655_);
lean_inc(v_congrTable_654_);
lean_inc(v_parents_653_);
lean_inc(v_exprs_652_);
lean_inc(v_enodeMap_651_);
lean_inc(v_nextDeclIdx_650_);
lean_dec(v_toGoalState_644_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_687_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v_used_670_; lean_object* v_next_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_686_; 
v_used_670_ = lean_ctor_get(v_clean_645_, 0);
v_next_671_ = lean_ctor_get(v_clean_645_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v_clean_645_);
if (v_isSharedCheck_686_ == 0)
{
v___x_673_ = v_clean_645_;
v_isShared_674_ = v_isSharedCheck_686_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_next_671_);
lean_inc(v_used_670_);
lean_dec(v_clean_645_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_686_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_675_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_next_671_, v___y_627_, v_snd_642_);
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
lean_ctor_set(v_reuseFailAlloc_684_, 7, v_toProcess_657_);
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
v___x_682_ = lean_st_ref_put(v___y_628_, v___x_681_);
v_name_572_ = v_fst_641_;
v___y_573_ = v___y_628_;
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
lean_dec(v___y_627_);
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
v___y_625_ = v___y_702_;
v___y_626_ = v___y_704_;
v___y_627_ = v_a_717_;
v___y_628_ = v___y_701_;
v___y_629_ = v___y_705_;
v___y_630_ = v___y_707_;
v___y_631_ = v___y_709_;
v___y_632_ = v_name_700_;
v___y_633_ = v___y_703_;
v___y_634_ = v___y_706_;
v___y_635_ = v___y_710_;
v___y_636_ = v___y_708_;
v___y_637_ = v_val_723_;
goto v___jp_624_;
}
else
{
lean_object* v___x_724_; 
lean_dec(v___x_722_);
v___x_724_ = lean_unsigned_to_nat(1u);
v___y_625_ = v___y_702_;
v___y_626_ = v___y_704_;
v___y_627_ = v_a_717_;
v___y_628_ = v___y_701_;
v___y_629_ = v___y_705_;
v___y_630_ = v___y_707_;
v___y_631_ = v___y_709_;
v___y_632_ = v_name_700_;
v___y_633_ = v___y_703_;
v___y_634_ = v___y_706_;
v___y_635_ = v___y_710_;
v___y_636_ = v___y_708_;
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_558_ = stack[0].m_obj;
lean_object* v_type_559_ = stack[1].m_obj;
lean_object* v_a_560_ = stack[2].m_obj;
lean_object* v_a_561_ = stack[3].m_obj;
lean_object* v_a_562_ = stack[4].m_obj;
lean_object* v_a_563_ = stack[5].m_obj;
lean_object* v_a_564_ = stack[6].m_obj;
lean_object* v_a_565_ = stack[7].m_obj;
lean_object* v_a_566_ = stack[8].m_obj;
lean_object* v_a_567_ = stack[9].m_obj;
lean_object* v_a_568_ = stack[10].m_obj;
lean_object* v_a_569_ = stack[11].m_obj;
lean_object* v_res_795_;
v_res_795_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v_name_558_, v_type_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
stack->m_obj
 = v_res_795_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___boxed(lean_object* v_name_796_, lean_object* v_type_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v_name_796_, v_type_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec(v_a_798_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0(lean_object* v_00_u03b2_810_, lean_object* v_x_811_, lean_object* v_x_812_, lean_object* v_x_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_x_811_, v_x_812_, v_x_813_);
return v___x_814_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(lean_object* v_00_u03b2_815_, lean_object* v_x_816_, lean_object* v_x_817_){
_start:
{
uint8_t v___x_818_; 
v___x_818_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_x_816_, v_x_817_);
return v___x_818_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_816_ = stack[1].m_obj;
lean_object* v_x_817_ = stack[2].m_obj;
uint8_t v_res_819_;
v_res_819_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(lean_box(0), v_x_816_, v_x_817_);
stack->m_num = v_res_819_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___boxed(lean_object* v_00_u03b2_820_, lean_object* v_x_821_, lean_object* v_x_822_){
_start:
{
uint8_t v_res_823_; lean_object* v_r_824_; 
v_res_823_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(v_00_u03b2_820_, v_x_821_, v_x_822_);
lean_dec(v_x_822_);
lean_dec_ref(v_x_821_);
v_r_824_ = lean_box(v_res_823_);
return v_r_824_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(lean_object* v_a_825_, lean_object* v_inst_826_, lean_object* v_a_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v_a_825_, v_a_827_, v___y_828_);
return v___x_839_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_825_ = stack[0].m_obj;
lean_object* v_a_827_ = stack[2].m_obj;
lean_object* v___y_828_ = stack[3].m_obj;
lean_object* v___y_829_ = stack[4].m_obj;
lean_object* v___y_830_ = stack[5].m_obj;
lean_object* v___y_831_ = stack[6].m_obj;
lean_object* v___y_832_ = stack[7].m_obj;
lean_object* v___y_833_ = stack[8].m_obj;
lean_object* v___y_834_ = stack[9].m_obj;
lean_object* v___y_835_ = stack[10].m_obj;
lean_object* v___y_836_ = stack[11].m_obj;
lean_object* v___y_837_ = stack[12].m_obj;
lean_object* v_res_840_;
v_res_840_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(v_a_825_, lean_box(0), v_a_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
stack->m_obj
 = v_res_840_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___boxed(lean_object* v_a_841_, lean_object* v_inst_842_, lean_object* v_a_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(v_a_841_, v_inst_842_, v_a_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec(v___y_844_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(lean_object* v_00_u03b2_856_, lean_object* v_x_857_, lean_object* v_x_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_x_857_, v_x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___boxed(lean_object* v_00_u03b2_860_, lean_object* v_x_861_, lean_object* v_x_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(v_00_u03b2_860_, v_x_861_, v_x_862_);
lean_dec(v_x_862_);
lean_dec_ref(v_x_861_);
return v_res_863_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(lean_object* v_00_u03b2_864_, lean_object* v_x_865_, size_t v_x_866_, size_t v_x_867_, lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_865_, v_x_866_, v_x_867_, v_x_868_, v_x_869_);
return v___x_870_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_865_ = stack[1].m_obj;
size_t v_x_866_ = stack[2].m_num;
size_t v_x_867_ = stack[3].m_num;
lean_object* v_x_868_ = stack[4].m_obj;
lean_object* v_x_869_ = stack[5].m_obj;
lean_object* v_res_871_;
v_res_871_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(lean_box(0), v_x_865_, v_x_866_, v_x_867_, v_x_868_, v_x_869_);
stack->m_obj
 = v_res_871_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___boxed(lean_object* v_00_u03b2_872_, lean_object* v_x_873_, lean_object* v_x_874_, lean_object* v_x_875_, lean_object* v_x_876_, lean_object* v_x_877_){
_start:
{
size_t v_x_34236__boxed_878_; size_t v_x_34237__boxed_879_; lean_object* v_res_880_; 
v_x_34236__boxed_878_ = lean_unbox_usize(v_x_874_);
lean_dec(v_x_874_);
v_x_34237__boxed_879_ = lean_unbox_usize(v_x_875_);
lean_dec(v_x_875_);
v_res_880_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(v_00_u03b2_872_, v_x_873_, v_x_34236__boxed_878_, v_x_34237__boxed_879_, v_x_876_, v_x_877_);
return v_res_880_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(lean_object* v_00_u03b2_881_, lean_object* v_x_882_, size_t v_x_883_, lean_object* v_x_884_){
_start:
{
uint8_t v___x_885_; 
v___x_885_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_882_, v_x_883_, v_x_884_);
return v___x_885_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_882_ = stack[1].m_obj;
size_t v_x_883_ = stack[2].m_num;
lean_object* v_x_884_ = stack[3].m_obj;
uint8_t v_res_886_;
v_res_886_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(lean_box(0), v_x_882_, v_x_883_, v_x_884_);
stack->m_num = v_res_886_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___boxed(lean_object* v_00_u03b2_887_, lean_object* v_x_888_, lean_object* v_x_889_, lean_object* v_x_890_){
_start:
{
size_t v_x_34264__boxed_891_; uint8_t v_res_892_; lean_object* v_r_893_; 
v_x_34264__boxed_891_ = lean_unbox_usize(v_x_889_);
lean_dec(v_x_889_);
v_res_892_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(v_00_u03b2_887_, v_x_888_, v_x_34264__boxed_891_, v_x_890_);
lean_dec(v_x_890_);
lean_dec_ref(v_x_888_);
v_r_893_ = lean_box(v_res_892_);
return v_r_893_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(lean_object* v_00_u03b2_894_, lean_object* v_x_895_, size_t v_x_896_, lean_object* v_x_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_895_, v_x_896_, v_x_897_);
return v___x_898_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_895_ = stack[1].m_obj;
size_t v_x_896_ = stack[2].m_num;
lean_object* v_x_897_ = stack[3].m_obj;
lean_object* v_res_899_;
v_res_899_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(lean_box(0), v_x_895_, v_x_896_, v_x_897_);
stack->m_obj
 = v_res_899_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___boxed(lean_object* v_00_u03b2_900_, lean_object* v_x_901_, lean_object* v_x_902_, lean_object* v_x_903_){
_start:
{
size_t v_x_34282__boxed_904_; lean_object* v_res_905_; 
v_x_34282__boxed_904_ = lean_unbox_usize(v_x_902_);
lean_dec(v_x_902_);
v_res_905_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(v_00_u03b2_900_, v_x_901_, v_x_34282__boxed_904_, v_x_903_);
lean_dec(v_x_903_);
lean_dec_ref(v_x_901_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_906_, lean_object* v_n_907_, lean_object* v_k_908_, lean_object* v_v_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(v_n_907_, v_k_908_, v_v_909_);
return v___x_910_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_911_, size_t v_depth_912_, lean_object* v_keys_913_, lean_object* v_vals_914_, lean_object* v_heq_915_, lean_object* v_i_916_, lean_object* v_entries_917_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_depth_912_, v_keys_913_, v_vals_914_, v_i_916_, v_entries_917_);
return v___x_918_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_depth_912_ = stack[1].m_num;
lean_object* v_keys_913_ = stack[2].m_obj;
lean_object* v_vals_914_ = stack[3].m_obj;
lean_object* v_i_916_ = stack[5].m_obj;
lean_object* v_entries_917_ = stack[6].m_obj;
lean_object* v_res_919_;
v_res_919_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(lean_box(0), v_depth_912_, v_keys_913_, v_vals_914_, lean_box(0), v_i_916_, v_entries_917_);
stack->m_obj
 = v_res_919_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_920_, lean_object* v_depth_921_, lean_object* v_keys_922_, lean_object* v_vals_923_, lean_object* v_heq_924_, lean_object* v_i_925_, lean_object* v_entries_926_){
_start:
{
size_t v_depth_boxed_927_; lean_object* v_res_928_; 
v_depth_boxed_927_ = lean_unbox_usize(v_depth_921_);
lean_dec(v_depth_921_);
v_res_928_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(v_00_u03b2_920_, v_depth_boxed_927_, v_keys_922_, v_vals_923_, v_heq_924_, v_i_925_, v_entries_926_);
lean_dec_ref(v_vals_923_);
lean_dec_ref(v_keys_922_);
return v_res_928_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_929_, lean_object* v_keys_930_, lean_object* v_vals_931_, lean_object* v_heq_932_, lean_object* v_i_933_, lean_object* v_k_934_){
_start:
{
uint8_t v___x_935_; 
v___x_935_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_keys_930_, v_i_933_, v_k_934_);
return v___x_935_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_930_ = stack[1].m_obj;
lean_object* v_vals_931_ = stack[2].m_obj;
lean_object* v_i_933_ = stack[4].m_obj;
lean_object* v_k_934_ = stack[5].m_obj;
uint8_t v_res_936_;
v_res_936_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(lean_box(0), v_keys_930_, v_vals_931_, lean_box(0), v_i_933_, v_k_934_);
stack->m_num = v_res_936_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_937_, lean_object* v_keys_938_, lean_object* v_vals_939_, lean_object* v_heq_940_, lean_object* v_i_941_, lean_object* v_k_942_){
_start:
{
uint8_t v_res_943_; lean_object* v_r_944_; 
v_res_943_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(v_00_u03b2_937_, v_keys_938_, v_vals_939_, v_heq_940_, v_i_941_, v_k_942_);
lean_dec(v_k_942_);
lean_dec_ref(v_vals_939_);
lean_dec_ref(v_keys_938_);
v_r_944_ = lean_box(v_res_943_);
return v_r_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_945_, lean_object* v_keys_946_, lean_object* v_vals_947_, lean_object* v_heq_948_, lean_object* v_i_949_, lean_object* v_k_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_keys_946_, v_vals_947_, v_i_949_, v_k_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_952_, lean_object* v_keys_953_, lean_object* v_vals_954_, lean_object* v_heq_955_, lean_object* v_i_956_, lean_object* v_k_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(v_00_u03b2_952_, v_keys_953_, v_vals_954_, v_heq_955_, v_i_956_, v_k_957_);
lean_dec(v_k_957_);
lean_dec_ref(v_vals_954_);
lean_dec_ref(v_keys_953_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_959_, lean_object* v_x_960_, lean_object* v_x_961_, lean_object* v_x_962_, lean_object* v_x_963_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(v_x_960_, v_x_961_, v_x_962_, v_x_963_);
return v___x_964_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(lean_object* v_msgData_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; lean_object* v_env_972_; uint8_t v___x_973_; lean_object* v_env_974_; lean_object* v___x_975_; lean_object* v_toCold_976_; lean_object* v_mctx_977_; lean_object* v_lctx_978_; lean_object* v_options_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_971_ = lean_st_ref_get(v___y_969_);
v_env_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc_ref(v_env_972_);
lean_dec(v___x_971_);
v___x_973_ = 0;
v_env_974_ = l_Lean_Environment_setRecordingDeps(v_env_972_, v___x_973_);
v___x_975_ = lean_st_ref_get(v___y_967_);
v_toCold_976_ = lean_ctor_get(v___y_968_, 0);
v_mctx_977_ = lean_ctor_get(v___x_975_, 0);
lean_inc_ref(v_mctx_977_);
lean_dec(v___x_975_);
v_lctx_978_ = lean_ctor_get(v___y_966_, 2);
v_options_979_ = lean_ctor_get(v_toCold_976_, 2);
lean_inc_ref(v_options_979_);
lean_inc_ref(v_lctx_978_);
v___x_980_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_980_, 0, v_env_974_);
lean_ctor_set(v___x_980_, 1, v_mctx_977_);
lean_ctor_set(v___x_980_, 2, v_lctx_978_);
lean_ctor_set(v___x_980_, 3, v_options_979_);
v___x_981_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v_msgData_965_);
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
return v___x_982_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_965_ = stack[0].m_obj;
lean_object* v___y_966_ = stack[1].m_obj;
lean_object* v___y_967_ = stack[2].m_obj;
lean_object* v___y_968_ = stack[3].m_obj;
lean_object* v___y_969_ = stack[4].m_obj;
lean_object* v_res_983_;
v_res_983_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(v_msgData_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
stack->m_obj
 = v_res_983_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0___boxed(lean_object* v_msgData_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(v_msgData_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
return v_res_990_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(lean_object* v_msg_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_ref_997_; lean_object* v___x_998_; lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1007_; 
v_ref_997_ = lean_ctor_get(v___y_994_, 2);
v___x_998_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(v_msg_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1007_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1007_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
lean_inc(v_ref_997_);
v___x_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1003_, 0, v_ref_997_);
lean_ctor_set(v___x_1003_, 1, v_a_999_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set_tag(v___x_1001_, 1);
lean_ctor_set(v___x_1001_, 0, v___x_1003_);
v___x_1005_ = v___x_1001_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_991_ = stack[0].m_obj;
lean_object* v___y_992_ = stack[1].m_obj;
lean_object* v___y_993_ = stack[2].m_obj;
lean_object* v___y_994_ = stack[3].m_obj;
lean_object* v___y_995_ = stack[4].m_obj;
lean_object* v_res_1008_;
v_res_1008_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v_msg_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
stack->m_obj
 = v_res_1008_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg___boxed(lean_object* v_msg_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v_msg_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
return v_res_1015_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__0));
v___x_1018_ = l_Lean_stringToMessageData(v___x_1017_);
return v___x_1018_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v_fst_1031_; lean_object* v_snd_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___x_1085_; lean_object* v_mvarId_1086_; lean_object* v___x_1087_; 
v___x_1085_ = lean_st_ref_get(v_a_1019_);
v_mvarId_1086_ = lean_ctor_get(v___x_1085_, 1);
lean_inc(v_mvarId_1086_);
lean_dec(v___x_1085_);
v___x_1087_ = l_Lean_MVarId_getType(v_mvarId_1086_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1087_, 1);
switch(lean_obj_tag(v_a_1088_))
{
case 7:
{
lean_object* v_binderName_1089_; lean_object* v_binderType_1090_; 
v_binderName_1089_ = lean_ctor_get(v_a_1088_, 0);
lean_inc(v_binderName_1089_);
v_binderType_1090_ = lean_ctor_get(v_a_1088_, 1);
lean_inc_ref(v_binderType_1090_);
lean_dec_ref_known(v_a_1088_, 3);
v_fst_1031_ = v_binderName_1089_;
v_snd_1032_ = v_binderType_1090_;
v___y_1033_ = v_a_1019_;
v___y_1034_ = v_a_1020_;
v___y_1035_ = v_a_1021_;
v___y_1036_ = v_a_1022_;
v___y_1037_ = v_a_1023_;
v___y_1038_ = v_a_1024_;
v___y_1039_ = v_a_1025_;
v___y_1040_ = v_a_1026_;
v___y_1041_ = v_a_1027_;
v___y_1042_ = v_a_1028_;
goto v___jp_1030_;
}
case 8:
{
lean_object* v_declName_1091_; lean_object* v_type_1092_; 
v_declName_1091_ = lean_ctor_get(v_a_1088_, 0);
lean_inc(v_declName_1091_);
v_type_1092_ = lean_ctor_get(v_a_1088_, 1);
lean_inc_ref(v_type_1092_);
lean_dec_ref_known(v_a_1088_, 4);
v_fst_1031_ = v_declName_1091_;
v_snd_1032_ = v_type_1092_;
v___y_1033_ = v_a_1019_;
v___y_1034_ = v_a_1020_;
v___y_1035_ = v_a_1021_;
v___y_1036_ = v_a_1022_;
v___y_1037_ = v_a_1023_;
v___y_1038_ = v_a_1024_;
v___y_1039_ = v_a_1025_;
v___y_1040_ = v_a_1026_;
v___y_1041_ = v_a_1027_;
v___y_1042_ = v_a_1028_;
goto v___jp_1030_;
}
default: 
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_dec(v_a_1088_);
v___x_1093_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1);
v___x_1094_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v___x_1093_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1094_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1094_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
v_a_1103_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1087_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1087_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
v___jp_1030_:
{
lean_object* v___x_1043_; 
v___x_1043_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v_fst_1031_, v_snd_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1045_; lean_object* v_mvarId_1046_; lean_object* v___x_1047_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref_known(v___x_1043_, 1);
v___x_1045_ = lean_st_ref_get(v___y_1033_);
v_mvarId_1046_ = lean_ctor_get(v___x_1045_, 1);
lean_inc(v_mvarId_1046_);
lean_dec(v___x_1045_);
v___x_1047_ = l_Lean_MVarId_intro(v_mvarId_1046_, v_a_1044_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1068_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1050_ = v___x_1047_;
v_isShared_1051_ = v_isSharedCheck_1068_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1047_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1068_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v_fst_1052_; lean_object* v_snd_1053_; lean_object* v___x_1054_; lean_object* v_toGoalState_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1066_; 
v_fst_1052_ = lean_ctor_get(v_a_1048_, 0);
lean_inc(v_fst_1052_);
v_snd_1053_ = lean_ctor_get(v_a_1048_, 1);
lean_inc(v_snd_1053_);
lean_dec(v_a_1048_);
v___x_1054_ = lean_st_ref_take(v___y_1033_);
v_toGoalState_1055_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1066_ == 0)
{
lean_object* v_unused_1067_; 
v_unused_1067_ = lean_ctor_get(v___x_1054_, 1);
lean_dec(v_unused_1067_);
v___x_1057_ = v___x_1054_;
v_isShared_1058_ = v_isSharedCheck_1066_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_toGoalState_1055_);
lean_dec(v___x_1054_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1066_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 1, v_snd_1053_);
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_toGoalState_1055_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_snd_1053_);
v___x_1060_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1061_ = lean_st_ref_put(v___y_1033_, v___x_1060_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 0, v_fst_1052_);
v___x_1063_ = v___x_1050_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_fst_1052_);
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
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
v_a_1069_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1047_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1047_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
v_a_1077_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1043_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1043_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1019_ = stack[0].m_obj;
lean_object* v_a_1020_ = stack[1].m_obj;
lean_object* v_a_1021_ = stack[2].m_obj;
lean_object* v_a_1022_ = stack[3].m_obj;
lean_object* v_a_1023_ = stack[4].m_obj;
lean_object* v_a_1024_ = stack[5].m_obj;
lean_object* v_a_1025_ = stack[6].m_obj;
lean_object* v_a_1026_ = stack[7].m_obj;
lean_object* v_a_1027_ = stack[8].m_obj;
lean_object* v_a_1028_ = stack[9].m_obj;
lean_object* v_res_1111_;
v_res_1111_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
stack->m_obj
 = v_res_1111_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___boxed(lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec(v_a_1112_);
return v_res_1123_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0(lean_object* v_00_u03b1_1124_, lean_object* v_msg_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v_msg_1125_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
return v___x_1137_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1125_ = stack[1].m_obj;
lean_object* v___y_1126_ = stack[2].m_obj;
lean_object* v___y_1127_ = stack[3].m_obj;
lean_object* v___y_1128_ = stack[4].m_obj;
lean_object* v___y_1129_ = stack[5].m_obj;
lean_object* v___y_1130_ = stack[6].m_obj;
lean_object* v___y_1131_ = stack[7].m_obj;
lean_object* v___y_1132_ = stack[8].m_obj;
lean_object* v___y_1133_ = stack[9].m_obj;
lean_object* v___y_1134_ = stack[10].m_obj;
lean_object* v___y_1135_ = stack[11].m_obj;
lean_object* v_res_1138_;
v_res_1138_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0(lean_box(0), v_msg_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
stack->m_obj
 = v_res_1138_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___boxed(lean_object* v_00_u03b1_1139_, lean_object* v_msg_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0(v_00_u03b1_1139_, v_msg_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec(v___y_1141_);
return v_res_1152_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(lean_object* v_x_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v___x_1165_; 
lean_inc(v___y_1159_);
lean_inc_ref(v___y_1158_);
lean_inc(v___y_1157_);
lean_inc_ref(v___y_1156_);
lean_inc(v___y_1155_);
lean_inc(v___y_1154_);
v___x_1165_ = lean_apply_11(v_x_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, lean_box(0));
return v___x_1165_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1153_ = stack[0].m_obj;
lean_object* v___y_1154_ = stack[1].m_obj;
lean_object* v___y_1155_ = stack[2].m_obj;
lean_object* v___y_1156_ = stack[3].m_obj;
lean_object* v___y_1157_ = stack[4].m_obj;
lean_object* v___y_1158_ = stack[5].m_obj;
lean_object* v___y_1159_ = stack[6].m_obj;
lean_object* v___y_1160_ = stack[7].m_obj;
lean_object* v___y_1161_ = stack[8].m_obj;
lean_object* v___y_1162_ = stack[9].m_obj;
lean_object* v___y_1163_ = stack[10].m_obj;
lean_object* v_res_1166_;
v_res_1166_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(v_x_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
stack->m_obj
 = v_res_1166_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0___boxed(lean_object* v_x_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(v_x_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec(v___y_1168_);
return v_res_1179_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(lean_object* v_mvarId_1180_, lean_object* v_x_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v___f_1193_; lean_object* v___x_1194_; 
lean_inc(v___y_1187_);
lean_inc_ref(v___y_1186_);
lean_inc(v___y_1185_);
lean_inc_ref(v___y_1184_);
lean_inc(v___y_1183_);
lean_inc(v___y_1182_);
v___f_1193_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_1193_, 0, v_x_1181_);
lean_closure_set(v___f_1193_, 1, v___y_1182_);
lean_closure_set(v___f_1193_, 2, v___y_1183_);
lean_closure_set(v___f_1193_, 3, v___y_1184_);
lean_closure_set(v___f_1193_, 4, v___y_1185_);
lean_closure_set(v___f_1193_, 5, v___y_1186_);
lean_closure_set(v___f_1193_, 6, v___y_1187_);
v___x_1194_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1180_, v___f_1193_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
if (lean_obj_tag(v___x_1194_) == 0)
{
return v___x_1194_;
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1194_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1194_);
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
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1180_ = stack[0].m_obj;
lean_object* v_x_1181_ = stack[1].m_obj;
lean_object* v___y_1182_ = stack[2].m_obj;
lean_object* v___y_1183_ = stack[3].m_obj;
lean_object* v___y_1184_ = stack[4].m_obj;
lean_object* v___y_1185_ = stack[5].m_obj;
lean_object* v___y_1186_ = stack[6].m_obj;
lean_object* v___y_1187_ = stack[7].m_obj;
lean_object* v___y_1188_ = stack[8].m_obj;
lean_object* v___y_1189_ = stack[9].m_obj;
lean_object* v___y_1190_ = stack[10].m_obj;
lean_object* v___y_1191_ = stack[11].m_obj;
lean_object* v_res_1203_;
v_res_1203_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_1180_, v_x_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
stack->m_obj
 = v_res_1203_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___boxed(lean_object* v_mvarId_1204_, lean_object* v_x_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_1204_, v_x_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec(v___y_1206_);
return v_res_1217_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(lean_object* v_00_u03b1_1218_, lean_object* v_mvarId_1219_, lean_object* v_x_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_1219_, v_x_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
return v___x_1232_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1219_ = stack[1].m_obj;
lean_object* v_x_1220_ = stack[2].m_obj;
lean_object* v___y_1221_ = stack[3].m_obj;
lean_object* v___y_1222_ = stack[4].m_obj;
lean_object* v___y_1223_ = stack[5].m_obj;
lean_object* v___y_1224_ = stack[6].m_obj;
lean_object* v___y_1225_ = stack[7].m_obj;
lean_object* v___y_1226_ = stack[8].m_obj;
lean_object* v___y_1227_ = stack[9].m_obj;
lean_object* v___y_1228_ = stack[10].m_obj;
lean_object* v___y_1229_ = stack[11].m_obj;
lean_object* v___y_1230_ = stack[12].m_obj;
lean_object* v_res_1233_;
v_res_1233_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(lean_box(0), v_mvarId_1219_, v_x_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
stack->m_obj
 = v_res_1233_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___boxed(lean_object* v_00_u03b1_1234_, lean_object* v_mvarId_1235_, lean_object* v_x_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(v_00_u03b1_1234_, v_mvarId_1235_, v_x_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec(v___y_1237_);
return v_res_1248_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0(lean_object* v_x_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___x_1260_; 
lean_inc(v___y_1254_);
lean_inc_ref(v___y_1253_);
lean_inc(v___y_1252_);
lean_inc_ref(v___y_1251_);
lean_inc(v___y_1250_);
v___x_1260_ = lean_apply_10(v_x_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, lean_box(0));
return v___x_1260_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1249_ = stack[0].m_obj;
lean_object* v___y_1250_ = stack[1].m_obj;
lean_object* v___y_1251_ = stack[2].m_obj;
lean_object* v___y_1252_ = stack[3].m_obj;
lean_object* v___y_1253_ = stack[4].m_obj;
lean_object* v___y_1254_ = stack[5].m_obj;
lean_object* v___y_1255_ = stack[6].m_obj;
lean_object* v___y_1256_ = stack[7].m_obj;
lean_object* v___y_1257_ = stack[8].m_obj;
lean_object* v___y_1258_ = stack[9].m_obj;
lean_object* v_res_1261_;
v_res_1261_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0(v_x_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
stack->m_obj
 = v_res_1261_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0___boxed(lean_object* v_x_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0(v_x_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
return v_res_1273_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(lean_object* v_mvarId_1274_, lean_object* v_x_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v___f_1286_; lean_object* v___x_1287_; 
lean_inc(v___y_1280_);
lean_inc_ref(v___y_1279_);
lean_inc(v___y_1278_);
lean_inc_ref(v___y_1277_);
lean_inc(v___y_1276_);
v___f_1286_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1286_, 0, v_x_1275_);
lean_closure_set(v___f_1286_, 1, v___y_1276_);
lean_closure_set(v___f_1286_, 2, v___y_1277_);
lean_closure_set(v___f_1286_, 3, v___y_1278_);
lean_closure_set(v___f_1286_, 4, v___y_1279_);
lean_closure_set(v___f_1286_, 5, v___y_1280_);
v___x_1287_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1274_, v___f_1286_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
if (lean_obj_tag(v___x_1287_) == 0)
{
return v___x_1287_;
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1287_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1287_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1274_ = stack[0].m_obj;
lean_object* v_x_1275_ = stack[1].m_obj;
lean_object* v___y_1276_ = stack[2].m_obj;
lean_object* v___y_1277_ = stack[3].m_obj;
lean_object* v___y_1278_ = stack[4].m_obj;
lean_object* v___y_1279_ = stack[5].m_obj;
lean_object* v___y_1280_ = stack[6].m_obj;
lean_object* v___y_1281_ = stack[7].m_obj;
lean_object* v___y_1282_ = stack[8].m_obj;
lean_object* v___y_1283_ = stack[9].m_obj;
lean_object* v___y_1284_ = stack[10].m_obj;
lean_object* v_res_1296_;
v_res_1296_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_1274_, v_x_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
stack->m_obj
 = v_res_1296_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___boxed(lean_object* v_mvarId_1297_, lean_object* v_x_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_1297_, v_x_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
return v_res_1309_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3(lean_object* v_00_u03b1_1310_, lean_object* v_mvarId_1311_, lean_object* v_x_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_1311_, v_x_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
return v___x_1323_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1311_ = stack[1].m_obj;
lean_object* v_x_1312_ = stack[2].m_obj;
lean_object* v___y_1313_ = stack[3].m_obj;
lean_object* v___y_1314_ = stack[4].m_obj;
lean_object* v___y_1315_ = stack[5].m_obj;
lean_object* v___y_1316_ = stack[6].m_obj;
lean_object* v___y_1317_ = stack[7].m_obj;
lean_object* v___y_1318_ = stack[8].m_obj;
lean_object* v___y_1319_ = stack[9].m_obj;
lean_object* v___y_1320_ = stack[10].m_obj;
lean_object* v___y_1321_ = stack[11].m_obj;
lean_object* v_res_1324_;
v_res_1324_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3(lean_box(0), v_mvarId_1311_, v_x_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
stack->m_obj
 = v_res_1324_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___boxed(lean_object* v_00_u03b1_1325_, lean_object* v_mvarId_1326_, lean_object* v_x_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3(v_00_u03b1_1325_, v_mvarId_1326_, v_x_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
return v_res_1338_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(lean_object* v_a_1339_, lean_object* v_generation_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v___x_1352_; 
lean_inc(v_a_1339_);
v___x_1352_ = l_Lean_FVarId_getDecl___redArg(v_a_1339_, v___y_1347_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_a_1353_);
lean_dec_ref_known(v___x_1352_, 1);
v___x_1354_ = l_Lean_LocalDecl_type(v_a_1353_);
lean_dec(v_a_1353_);
lean_inc_ref(v___x_1354_);
v___x_1355_ = l_Lean_Meta_isProp(v___x_1354_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; uint8_t v___x_1357_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1356_);
lean_dec_ref_known(v___x_1355_, 1);
v___x_1357_ = lean_unbox(v_a_1356_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; 
lean_dec_ref(v___x_1354_);
lean_inc(v_a_1339_);
v___x_1358_ = l_Lean_FVarId_getDecl___redArg(v_a_1339_, v___y_1347_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; uint8_t v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_a_1359_);
lean_dec_ref_known(v___x_1358_, 1);
v___x_1360_ = lean_unbox(v_a_1356_);
lean_dec(v_a_1356_);
v___x_1361_ = l_Lean_LocalDecl_value(v_a_1359_, v___x_1360_);
lean_dec(v_a_1359_);
v___x_1362_ = l_Lean_Meta_Grind_preprocessHypothesis(v___x_1361_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
lean_dec_ref_known(v___x_1362_, 1);
lean_inc(v_a_1339_);
v___x_1364_ = l_Lean_mkFVar(v_a_1339_);
v___x_1365_ = l_Lean_Meta_Sym_shareCommon(v___x_1364_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1367_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1366_);
lean_dec_ref_known(v___x_1365_, 1);
lean_inc(v_a_1363_);
v___x_1367_ = l_Lean_Meta_Simp_Result_getProof(v_a_1363_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; lean_object* v_expr_1369_; lean_object* v___x_1370_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1368_);
lean_dec_ref_known(v___x_1367_, 1);
v_expr_1369_ = lean_ctor_get(v_a_1363_, 0);
lean_inc_ref(v_expr_1369_);
lean_dec(v_a_1363_);
v___x_1370_ = l_Lean_Meta_Grind_addNewEq(v_a_1366_, v_expr_1369_, v_a_1368_, v_generation_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1379_; 
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1379_ == 0)
{
lean_object* v_unused_1380_; 
v_unused_1380_ = lean_ctor_get(v___x_1370_, 0);
lean_dec(v_unused_1380_);
v___x_1372_ = v___x_1370_;
v_isShared_1373_ = v_isSharedCheck_1379_;
goto v_resetjp_1371_;
}
else
{
lean_dec(v___x_1370_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1379_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1377_; 
v___x_1374_ = lean_st_ref_get(v___y_1341_);
v___x_1375_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1375_, 0, v_a_1339_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1375_);
v___x_1377_ = v___x_1372_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec(v_a_1339_);
v_a_1381_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1370_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1370_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_dec(v_a_1366_);
lean_dec(v_a_1363_);
lean_dec(v_generation_1340_);
lean_dec(v_a_1339_);
v_a_1389_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1367_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1367_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_dec(v_a_1363_);
lean_dec(v_generation_1340_);
lean_dec(v_a_1339_);
v_a_1397_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1365_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1365_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_dec(v_generation_1340_);
lean_dec(v_a_1339_);
v_a_1405_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1362_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1362_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec(v_a_1356_);
lean_dec(v_generation_1340_);
lean_dec(v_a_1339_);
v_a_1413_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1358_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1358_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
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
else
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_dec(v_a_1356_);
lean_dec(v_generation_1340_);
v___x_1421_ = lean_st_ref_get(v___y_1341_);
v___x_1422_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
lean_inc_ref(v___x_1354_);
v___x_1423_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v___x_1422_, v___x_1354_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v_mvarId_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
lean_dec_ref_known(v___x_1423_, 1);
v_mvarId_1425_ = lean_ctor_get(v___x_1421_, 1);
lean_inc(v_mvarId_1425_);
lean_dec(v___x_1421_);
v___x_1426_ = l_Lean_mkFVar(v_a_1339_);
v___x_1427_ = l_Lean_MVarId_assert(v_mvarId_1425_, v_a_1424_, v___x_1354_, v___x_1426_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1446_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1446_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1446_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v_toGoalState_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1444_; 
v___x_1432_ = lean_st_ref_get(v___y_1341_);
v_toGoalState_1433_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1444_ == 0)
{
lean_object* v_unused_1445_; 
v_unused_1445_ = lean_ctor_get(v___x_1432_, 1);
lean_dec(v_unused_1445_);
v___x_1435_ = v___x_1432_;
v_isShared_1436_ = v_isSharedCheck_1444_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_toGoalState_1433_);
lean_dec(v___x_1432_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1444_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 1, v_a_1428_);
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_toGoalState_1433_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_a_1428_);
v___x_1438_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1439_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1439_);
v___x_1441_ = v___x_1430_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1439_);
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
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
v_a_1447_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1427_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1427_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_dec(v___x_1421_);
lean_dec_ref(v___x_1354_);
lean_dec(v_a_1339_);
v_a_1455_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1423_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1423_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec_ref(v___x_1354_);
lean_dec(v_generation_1340_);
lean_dec(v_a_1339_);
v_a_1463_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1355_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1355_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec(v_generation_1340_);
lean_dec(v_a_1339_);
v_a_1471_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1352_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1352_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1339_ = stack[0].m_obj;
lean_object* v_generation_1340_ = stack[1].m_obj;
lean_object* v___y_1341_ = stack[2].m_obj;
lean_object* v___y_1342_ = stack[3].m_obj;
lean_object* v___y_1343_ = stack[4].m_obj;
lean_object* v___y_1344_ = stack[5].m_obj;
lean_object* v___y_1345_ = stack[6].m_obj;
lean_object* v___y_1346_ = stack[7].m_obj;
lean_object* v___y_1347_ = stack[8].m_obj;
lean_object* v___y_1348_ = stack[9].m_obj;
lean_object* v___y_1349_ = stack[10].m_obj;
lean_object* v___y_1350_ = stack[11].m_obj;
lean_object* v_res_1479_;
v_res_1479_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(v_a_1339_, v_generation_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
stack->m_obj
 = v_res_1479_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed(lean_object* v_a_1480_, lean_object* v_generation_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(v_a_1480_, v_generation_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec(v___y_1482_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(lean_object* v_x_1494_, lean_object* v_x_1495_, lean_object* v_x_1496_, lean_object* v_x_1497_){
_start:
{
lean_object* v_ks_1498_; lean_object* v_vs_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1523_; 
v_ks_1498_ = lean_ctor_get(v_x_1494_, 0);
v_vs_1499_ = lean_ctor_get(v_x_1494_, 1);
v_isSharedCheck_1523_ = !lean_is_exclusive(v_x_1494_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1501_ = v_x_1494_;
v_isShared_1502_ = v_isSharedCheck_1523_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_vs_1499_);
lean_inc(v_ks_1498_);
lean_dec(v_x_1494_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1523_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; uint8_t v___x_1504_; 
v___x_1503_ = lean_array_get_size(v_ks_1498_);
v___x_1504_ = lean_nat_dec_lt(v_x_1495_, v___x_1503_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1508_; 
lean_dec(v_x_1495_);
v___x_1505_ = lean_array_push(v_ks_1498_, v_x_1496_);
v___x_1506_ = lean_array_push(v_vs_1499_, v_x_1497_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 1, v___x_1506_);
lean_ctor_set(v___x_1501_, 0, v___x_1505_);
v___x_1508_ = v___x_1501_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
else
{
lean_object* v_k_x27_1510_; uint8_t v___x_1511_; 
v_k_x27_1510_ = lean_array_fget_borrowed(v_ks_1498_, v_x_1495_);
v___x_1511_ = l_Lean_instBEqMVarId_beq(v_x_1496_, v_k_x27_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1513_; 
if (v_isShared_1502_ == 0)
{
v___x_1513_ = v___x_1501_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_ks_1498_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_vs_1499_);
v___x_1513_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = lean_unsigned_to_nat(1u);
v___x_1515_ = lean_nat_add(v_x_1495_, v___x_1514_);
lean_dec(v_x_1495_);
v_x_1494_ = v___x_1513_;
v_x_1495_ = v___x_1515_;
goto _start;
}
}
else
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1521_; 
v___x_1518_ = lean_array_fset(v_ks_1498_, v_x_1495_, v_x_1496_);
v___x_1519_ = lean_array_fset(v_vs_1499_, v_x_1495_, v_x_1497_);
lean_dec(v_x_1495_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 1, v___x_1519_);
lean_ctor_set(v___x_1501_, 0, v___x_1518_);
v___x_1521_ = v___x_1501_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1518_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(lean_object* v_n_1524_, lean_object* v_k_1525_, lean_object* v_v_1526_){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = lean_unsigned_to_nat(0u);
v___x_1528_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_n_1524_, v___x_1527_, v_k_1525_, v_v_1526_);
return v___x_1528_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1529_, size_t v_x_1530_, size_t v_x_1531_, lean_object* v_x_1532_, lean_object* v_x_1533_){
_start:
{
if (lean_obj_tag(v_x_1529_) == 0)
{
lean_object* v_es_1534_; size_t v___x_1535_; size_t v___x_1536_; lean_object* v_j_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; 
v_es_1534_ = lean_ctor_get(v_x_1529_, 0);
v___x_1535_ = ((size_t)31ULL);
v___x_1536_ = lean_usize_land(v_x_1530_, v___x_1535_);
v_j_1537_ = lean_usize_to_nat(v___x_1536_);
v___x_1538_ = lean_array_get_size(v_es_1534_);
v___x_1539_ = lean_nat_dec_lt(v_j_1537_, v___x_1538_);
if (v___x_1539_ == 0)
{
lean_dec(v_j_1537_);
lean_dec(v_x_1533_);
lean_dec(v_x_1532_);
return v_x_1529_;
}
else
{
lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1578_; 
lean_inc_ref(v_es_1534_);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_x_1529_);
if (v_isSharedCheck_1578_ == 0)
{
lean_object* v_unused_1579_; 
v_unused_1579_ = lean_ctor_get(v_x_1529_, 0);
lean_dec(v_unused_1579_);
v___x_1541_ = v_x_1529_;
v_isShared_1542_ = v_isSharedCheck_1578_;
goto v_resetjp_1540_;
}
else
{
lean_dec(v_x_1529_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1578_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v_v_1543_; lean_object* v___x_1544_; lean_object* v_xs_x27_1545_; lean_object* v___y_1547_; 
v_v_1543_ = lean_array_fget(v_es_1534_, v_j_1537_);
v___x_1544_ = lean_box(0);
v_xs_x27_1545_ = lean_array_fset(v_es_1534_, v_j_1537_, v___x_1544_);
switch(lean_obj_tag(v_v_1543_))
{
case 0:
{
lean_object* v_key_1552_; lean_object* v_val_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1563_; 
v_key_1552_ = lean_ctor_get(v_v_1543_, 0);
v_val_1553_ = lean_ctor_get(v_v_1543_, 1);
v_isSharedCheck_1563_ = !lean_is_exclusive(v_v_1543_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1555_ = v_v_1543_;
v_isShared_1556_ = v_isSharedCheck_1563_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_val_1553_);
lean_inc(v_key_1552_);
lean_dec(v_v_1543_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1563_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
uint8_t v___x_1557_; 
v___x_1557_ = l_Lean_instBEqMVarId_beq(v_x_1532_, v_key_1552_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
lean_del_object(v___x_1555_);
v___x_1558_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1552_, v_val_1553_, v_x_1532_, v_x_1533_);
v___x_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
v___y_1547_ = v___x_1559_;
goto v___jp_1546_;
}
else
{
lean_object* v___x_1561_; 
lean_dec(v_val_1553_);
lean_dec(v_key_1552_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 1, v_x_1533_);
lean_ctor_set(v___x_1555_, 0, v_x_1532_);
v___x_1561_ = v___x_1555_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_x_1532_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_x_1533_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
v___y_1547_ = v___x_1561_;
goto v___jp_1546_;
}
}
}
}
case 1:
{
lean_object* v_node_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1576_; 
v_node_1564_ = lean_ctor_get(v_v_1543_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v_v_1543_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1566_ = v_v_1543_;
v_isShared_1567_ = v_isSharedCheck_1576_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_node_1564_);
lean_dec(v_v_1543_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1576_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
size_t v___x_1568_; size_t v___x_1569_; size_t v___x_1570_; size_t v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1574_; 
v___x_1568_ = ((size_t)5ULL);
v___x_1569_ = lean_usize_shift_right(v_x_1530_, v___x_1568_);
v___x_1570_ = ((size_t)1ULL);
v___x_1571_ = lean_usize_add(v_x_1531_, v___x_1570_);
v___x_1572_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_node_1564_, v___x_1569_, v___x_1571_, v_x_1532_, v_x_1533_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v___x_1572_);
v___x_1574_ = v___x_1566_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1572_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
v___y_1547_ = v___x_1574_;
goto v___jp_1546_;
}
}
}
default: 
{
lean_object* v___x_1577_; 
v___x_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1577_, 0, v_x_1532_);
lean_ctor_set(v___x_1577_, 1, v_x_1533_);
v___y_1547_ = v___x_1577_;
goto v___jp_1546_;
}
}
v___jp_1546_:
{
lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1548_ = lean_array_fset(v_xs_x27_1545_, v_j_1537_, v___y_1547_);
lean_dec(v_j_1537_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1548_);
v___x_1550_ = v___x_1541_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
}
else
{
lean_object* v_ks_1580_; lean_object* v_vs_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1599_; 
v_ks_1580_ = lean_ctor_get(v_x_1529_, 0);
v_vs_1581_ = lean_ctor_get(v_x_1529_, 1);
v_isSharedCheck_1599_ = !lean_is_exclusive(v_x_1529_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1583_ = v_x_1529_;
v_isShared_1584_ = v_isSharedCheck_1599_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_vs_1581_);
lean_inc(v_ks_1580_);
lean_dec(v_x_1529_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1599_;
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
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_ks_1580_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_vs_1581_);
v___x_1586_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
lean_object* v_newNode_1587_; size_t v___x_1588_; uint8_t v___x_1589_; 
v_newNode_1587_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(v___x_1586_, v_x_1532_, v_x_1533_);
v___x_1588_ = ((size_t)7ULL);
v___x_1589_ = lean_usize_dec_le(v___x_1588_, v_x_1531_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1590_; lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1590_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1587_);
v___x_1591_ = lean_unsigned_to_nat(4u);
v___x_1592_ = lean_nat_dec_lt(v___x_1590_, v___x_1591_);
lean_dec(v___x_1590_);
if (v___x_1592_ == 0)
{
lean_object* v_ks_1593_; lean_object* v_vs_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v_ks_1593_ = lean_ctor_get(v_newNode_1587_, 0);
lean_inc_ref(v_ks_1593_);
v_vs_1594_ = lean_ctor_get(v_newNode_1587_, 1);
lean_inc_ref(v_vs_1594_);
lean_dec_ref(v_newNode_1587_);
v___x_1595_ = lean_unsigned_to_nat(0u);
v___x_1596_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0);
v___x_1597_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_x_1531_, v_ks_1593_, v_vs_1594_, v___x_1595_, v___x_1596_);
lean_dec_ref(v_vs_1594_);
lean_dec_ref(v_ks_1593_);
return v___x_1597_;
}
else
{
return v_newNode_1587_;
}
}
else
{
return v_newNode_1587_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1529_ = stack[0].m_obj;
size_t v_x_1530_ = stack[1].m_num;
size_t v_x_1531_ = stack[2].m_num;
lean_object* v_x_1532_ = stack[3].m_obj;
lean_object* v_x_1533_ = stack[4].m_obj;
lean_object* v_res_1600_;
v_res_1600_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_1529_, v_x_1530_, v_x_1531_, v_x_1532_, v_x_1533_);
stack->m_obj
 = v_res_1600_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(size_t v_depth_1601_, lean_object* v_keys_1602_, lean_object* v_vals_1603_, lean_object* v_i_1604_, lean_object* v_entries_1605_){
_start:
{
lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1606_ = lean_array_get_size(v_keys_1602_);
v___x_1607_ = lean_nat_dec_lt(v_i_1604_, v___x_1606_);
if (v___x_1607_ == 0)
{
lean_dec(v_i_1604_);
return v_entries_1605_;
}
else
{
lean_object* v_k_1608_; lean_object* v_v_1609_; uint64_t v___x_1610_; size_t v_h_1611_; size_t v___x_1612_; lean_object* v___x_1613_; size_t v___x_1614_; size_t v___x_1615_; size_t v___x_1616_; size_t v_h_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v_k_1608_ = lean_array_fget_borrowed(v_keys_1602_, v_i_1604_);
v_v_1609_ = lean_array_fget_borrowed(v_vals_1603_, v_i_1604_);
v___x_1610_ = l_Lean_instHashableMVarId_hash(v_k_1608_);
v_h_1611_ = lean_uint64_to_usize(v___x_1610_);
v___x_1612_ = ((size_t)5ULL);
v___x_1613_ = lean_unsigned_to_nat(1u);
v___x_1614_ = ((size_t)1ULL);
v___x_1615_ = lean_usize_sub(v_depth_1601_, v___x_1614_);
v___x_1616_ = lean_usize_mul(v___x_1612_, v___x_1615_);
v_h_1617_ = lean_usize_shift_right(v_h_1611_, v___x_1616_);
v___x_1618_ = lean_nat_add(v_i_1604_, v___x_1613_);
lean_dec(v_i_1604_);
lean_inc(v_v_1609_);
lean_inc(v_k_1608_);
v___x_1619_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_entries_1605_, v_h_1617_, v_depth_1601_, v_k_1608_, v_v_1609_);
v_i_1604_ = v___x_1618_;
v_entries_1605_ = v___x_1619_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1601_ = stack[0].m_num;
lean_object* v_keys_1602_ = stack[1].m_obj;
lean_object* v_vals_1603_ = stack[2].m_obj;
lean_object* v_i_1604_ = stack[3].m_obj;
lean_object* v_entries_1605_ = stack[4].m_obj;
lean_object* v_res_1621_;
v_res_1621_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_1601_, v_keys_1602_, v_vals_1603_, v_i_1604_, v_entries_1605_);
stack->m_obj
 = v_res_1621_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_depth_1622_, lean_object* v_keys_1623_, lean_object* v_vals_1624_, lean_object* v_i_1625_, lean_object* v_entries_1626_){
_start:
{
size_t v_depth_boxed_1627_; lean_object* v_res_1628_; 
v_depth_boxed_1627_ = lean_unbox_usize(v_depth_1622_);
lean_dec(v_depth_1622_);
v_res_1628_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_boxed_1627_, v_keys_1623_, v_vals_1624_, v_i_1625_, v_entries_1626_);
lean_dec_ref(v_vals_1624_);
lean_dec_ref(v_keys_1623_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_1629_, lean_object* v_x_1630_, lean_object* v_x_1631_, lean_object* v_x_1632_, lean_object* v_x_1633_){
_start:
{
size_t v_x_152168__boxed_1634_; size_t v_x_152169__boxed_1635_; lean_object* v_res_1636_; 
v_x_152168__boxed_1634_ = lean_unbox_usize(v_x_1630_);
lean_dec(v_x_1630_);
v_x_152169__boxed_1635_ = lean_unbox_usize(v_x_1631_);
lean_dec(v_x_1631_);
v_res_1636_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_1629_, v_x_152168__boxed_1634_, v_x_152169__boxed_1635_, v_x_1632_, v_x_1633_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(lean_object* v_x_1637_, lean_object* v_x_1638_, lean_object* v_x_1639_){
_start:
{
uint64_t v___x_1640_; size_t v___x_1641_; size_t v___x_1642_; lean_object* v___x_1643_; 
v___x_1640_ = l_Lean_instHashableMVarId_hash(v_x_1638_);
v___x_1641_ = lean_uint64_to_usize(v___x_1640_);
v___x_1642_ = ((size_t)1ULL);
v___x_1643_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_1637_, v___x_1641_, v___x_1642_, v_x_1638_, v_x_1639_);
return v___x_1643_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(lean_object* v_mvarId_1644_, lean_object* v_val_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v___x_1648_; lean_object* v_mctx_1649_; lean_object* v_cache_1650_; lean_object* v_zetaDeltaFVarIds_1651_; lean_object* v_postponed_1652_; lean_object* v_diag_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1683_; 
v___x_1648_ = lean_st_ref_take(v___y_1646_);
v_mctx_1649_ = lean_ctor_get(v___x_1648_, 0);
v_cache_1650_ = lean_ctor_get(v___x_1648_, 1);
v_zetaDeltaFVarIds_1651_ = lean_ctor_get(v___x_1648_, 2);
v_postponed_1652_ = lean_ctor_get(v___x_1648_, 3);
v_diag_1653_ = lean_ctor_get(v___x_1648_, 4);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1655_ = v___x_1648_;
v_isShared_1656_ = v_isSharedCheck_1683_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_diag_1653_);
lean_inc(v_postponed_1652_);
lean_inc(v_zetaDeltaFVarIds_1651_);
lean_inc(v_cache_1650_);
lean_inc(v_mctx_1649_);
lean_dec(v___x_1648_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1683_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v_depth_1657_; lean_object* v_levelAssignDepth_1658_; lean_object* v_lmvarCounter_1659_; lean_object* v_mvarCounter_1660_; lean_object* v_lDecls_1661_; lean_object* v_decls_1662_; lean_object* v_userNames_1663_; lean_object* v_lAssignment_1664_; lean_object* v_eAssignment_1665_; lean_object* v_dAssignment_1666_; lean_object* v_instanceTypedMVars_1667_; lean_object* v_synthNormMemo_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1682_; 
v_depth_1657_ = lean_ctor_get(v_mctx_1649_, 0);
v_levelAssignDepth_1658_ = lean_ctor_get(v_mctx_1649_, 1);
v_lmvarCounter_1659_ = lean_ctor_get(v_mctx_1649_, 2);
v_mvarCounter_1660_ = lean_ctor_get(v_mctx_1649_, 3);
v_lDecls_1661_ = lean_ctor_get(v_mctx_1649_, 4);
v_decls_1662_ = lean_ctor_get(v_mctx_1649_, 5);
v_userNames_1663_ = lean_ctor_get(v_mctx_1649_, 6);
v_lAssignment_1664_ = lean_ctor_get(v_mctx_1649_, 7);
v_eAssignment_1665_ = lean_ctor_get(v_mctx_1649_, 8);
v_dAssignment_1666_ = lean_ctor_get(v_mctx_1649_, 9);
v_instanceTypedMVars_1667_ = lean_ctor_get(v_mctx_1649_, 10);
v_synthNormMemo_1668_ = lean_ctor_get(v_mctx_1649_, 11);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_mctx_1649_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1670_ = v_mctx_1649_;
v_isShared_1671_ = v_isSharedCheck_1682_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_synthNormMemo_1668_);
lean_inc(v_instanceTypedMVars_1667_);
lean_inc(v_dAssignment_1666_);
lean_inc(v_eAssignment_1665_);
lean_inc(v_lAssignment_1664_);
lean_inc(v_userNames_1663_);
lean_inc(v_decls_1662_);
lean_inc(v_lDecls_1661_);
lean_inc(v_mvarCounter_1660_);
lean_inc(v_lmvarCounter_1659_);
lean_inc(v_levelAssignDepth_1658_);
lean_inc(v_depth_1657_);
lean_dec(v_mctx_1649_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1682_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1672_ = lean_box(0);
v___x_1673_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_eAssignment_1665_, v_mvarId_1644_, v_val_1645_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 8, v___x_1673_);
v___x_1675_ = v___x_1670_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_depth_1657_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v_levelAssignDepth_1658_);
lean_ctor_set(v_reuseFailAlloc_1681_, 2, v_lmvarCounter_1659_);
lean_ctor_set(v_reuseFailAlloc_1681_, 3, v_mvarCounter_1660_);
lean_ctor_set(v_reuseFailAlloc_1681_, 4, v_lDecls_1661_);
lean_ctor_set(v_reuseFailAlloc_1681_, 5, v_decls_1662_);
lean_ctor_set(v_reuseFailAlloc_1681_, 6, v_userNames_1663_);
lean_ctor_set(v_reuseFailAlloc_1681_, 7, v_lAssignment_1664_);
lean_ctor_set(v_reuseFailAlloc_1681_, 8, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1681_, 9, v_dAssignment_1666_);
lean_ctor_set(v_reuseFailAlloc_1681_, 10, v_instanceTypedMVars_1667_);
lean_ctor_set(v_reuseFailAlloc_1681_, 11, v_synthNormMemo_1668_);
v___x_1675_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v___x_1677_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1675_);
v___x_1677_ = v___x_1655_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1675_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_cache_1650_);
lean_ctor_set(v_reuseFailAlloc_1680_, 2, v_zetaDeltaFVarIds_1651_);
lean_ctor_set(v_reuseFailAlloc_1680_, 3, v_postponed_1652_);
lean_ctor_set(v_reuseFailAlloc_1680_, 4, v_diag_1653_);
v___x_1677_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = lean_st_ref_put(v___y_1646_, v___x_1677_);
v___x_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1672_);
return v___x_1679_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1644_ = stack[0].m_obj;
lean_object* v_val_1645_ = stack[1].m_obj;
lean_object* v___y_1646_ = stack[2].m_obj;
lean_object* v_res_1684_;
v_res_1684_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1644_, v_val_1645_, v___y_1646_);
stack->m_obj
 = v_res_1684_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg___boxed(lean_object* v_mvarId_1685_, lean_object* v_val_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1685_, v_val_1686_, v___y_1687_);
lean_dec(v___y_1687_);
return v_res_1689_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(lean_object* v___y_1690_){
_start:
{
lean_object* v___x_1692_; lean_object* v_ngen_1693_; lean_object* v_namePrefix_1694_; lean_object* v_idx_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1725_; 
v___x_1692_ = lean_st_ref_get(v___y_1690_);
v_ngen_1693_ = lean_ctor_get(v___x_1692_, 2);
lean_inc_ref(v_ngen_1693_);
lean_dec(v___x_1692_);
v_namePrefix_1694_ = lean_ctor_get(v_ngen_1693_, 0);
v_idx_1695_ = lean_ctor_get(v_ngen_1693_, 1);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_ngen_1693_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1697_ = v_ngen_1693_;
v_isShared_1698_ = v_isSharedCheck_1725_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_idx_1695_);
lean_inc(v_namePrefix_1694_);
lean_dec(v_ngen_1693_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1725_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v_r_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1703_; 
lean_inc(v_idx_1695_);
lean_inc(v_namePrefix_1694_);
v_r_1699_ = l_Lean_Name_num___override(v_namePrefix_1694_, v_idx_1695_);
v___x_1700_ = lean_unsigned_to_nat(1u);
v___x_1701_ = lean_nat_add(v_idx_1695_, v___x_1700_);
lean_dec(v_idx_1695_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 1, v___x_1701_);
v___x_1703_ = v___x_1697_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_namePrefix_1694_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v___x_1701_);
v___x_1703_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
lean_object* v___x_1704_; lean_object* v_env_1705_; lean_object* v_nextMacroScope_1706_; lean_object* v_auxDeclNGen_1707_; lean_object* v_traceState_1708_; lean_object* v_cache_1709_; lean_object* v_recordedDeps_1710_; lean_object* v_messages_1711_; lean_object* v_infoState_1712_; lean_object* v_snapshotTasks_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1722_; 
v___x_1704_ = lean_st_ref_take(v___y_1690_);
v_env_1705_ = lean_ctor_get(v___x_1704_, 0);
v_nextMacroScope_1706_ = lean_ctor_get(v___x_1704_, 1);
v_auxDeclNGen_1707_ = lean_ctor_get(v___x_1704_, 3);
v_traceState_1708_ = lean_ctor_get(v___x_1704_, 4);
v_cache_1709_ = lean_ctor_get(v___x_1704_, 5);
v_recordedDeps_1710_ = lean_ctor_get(v___x_1704_, 6);
v_messages_1711_ = lean_ctor_get(v___x_1704_, 7);
v_infoState_1712_ = lean_ctor_get(v___x_1704_, 8);
v_snapshotTasks_1713_ = lean_ctor_get(v___x_1704_, 9);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1722_ == 0)
{
lean_object* v_unused_1723_; 
v_unused_1723_ = lean_ctor_get(v___x_1704_, 2);
lean_dec(v_unused_1723_);
v___x_1715_ = v___x_1704_;
v_isShared_1716_ = v_isSharedCheck_1722_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_snapshotTasks_1713_);
lean_inc(v_infoState_1712_);
lean_inc(v_messages_1711_);
lean_inc(v_recordedDeps_1710_);
lean_inc(v_cache_1709_);
lean_inc(v_traceState_1708_);
lean_inc(v_auxDeclNGen_1707_);
lean_inc(v_nextMacroScope_1706_);
lean_inc(v_env_1705_);
lean_dec(v___x_1704_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1722_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 2, v___x_1703_);
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_env_1705_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_nextMacroScope_1706_);
lean_ctor_set(v_reuseFailAlloc_1721_, 2, v___x_1703_);
lean_ctor_set(v_reuseFailAlloc_1721_, 3, v_auxDeclNGen_1707_);
lean_ctor_set(v_reuseFailAlloc_1721_, 4, v_traceState_1708_);
lean_ctor_set(v_reuseFailAlloc_1721_, 5, v_cache_1709_);
lean_ctor_set(v_reuseFailAlloc_1721_, 6, v_recordedDeps_1710_);
lean_ctor_set(v_reuseFailAlloc_1721_, 7, v_messages_1711_);
lean_ctor_set(v_reuseFailAlloc_1721_, 8, v_infoState_1712_);
lean_ctor_set(v_reuseFailAlloc_1721_, 9, v_snapshotTasks_1713_);
v___x_1718_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = lean_st_ref_put(v___y_1690_, v___x_1718_);
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v_r_1699_);
return v___x_1720_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1690_ = stack[0].m_obj;
lean_object* v_res_1726_;
v_res_1726_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_1690_);
stack->m_obj
 = v_res_1726_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg___boxed(lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_1727_);
lean_dec(v___y_1727_);
return v_res_1729_;
}
}
lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v___x_1741_; lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
v___x_1741_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_1739_);
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1741_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1741_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1730_ = stack[0].m_obj;
lean_object* v___y_1731_ = stack[1].m_obj;
lean_object* v___y_1732_ = stack[2].m_obj;
lean_object* v___y_1733_ = stack[3].m_obj;
lean_object* v___y_1734_ = stack[4].m_obj;
lean_object* v___y_1735_ = stack[5].m_obj;
lean_object* v___y_1736_ = stack[6].m_obj;
lean_object* v___y_1737_ = stack[7].m_obj;
lean_object* v___y_1738_ = stack[8].m_obj;
lean_object* v___y_1739_ = stack[9].m_obj;
lean_object* v_res_1750_;
v_res_1750_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
stack->m_obj
 = v_res_1750_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2___boxed(lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec(v___y_1751_);
return v_res_1762_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(lean_object* v___x_1768_, lean_object* v_a_1769_, uint8_t v___y_1770_, uint8_t v___x_1771_, uint8_t v___x_1772_, lean_object* v_a_1773_, lean_object* v___x_1774_, lean_object* v_expr_1775_, lean_object* v___x_1776_, lean_object* v_val_1777_, lean_object* v_mvarId_1778_, lean_object* v___x_1779_, lean_object* v_a_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_Meta_mkLambdaFVars(v___x_1768_, v_a_1769_, v___y_1770_, v___x_1771_, v___y_1770_, v___x_1771_, v___x_1772_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1793_);
lean_dec_ref_known(v___x_1792_, 1);
v___x_1794_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1));
v___x_1795_ = lean_box(0);
v___x_1796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1796_, 0, v_a_1773_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
v___x_1797_ = l_Lean_mkConst(v___x_1794_, v___x_1796_);
v___x_1798_ = lean_unsigned_to_nat(5u);
v___x_1799_ = lean_mk_empty_array_with_capacity(v___x_1798_);
v___x_1800_ = lean_array_push(v___x_1799_, v___x_1774_);
v___x_1801_ = lean_array_push(v___x_1800_, v_expr_1775_);
v___x_1802_ = lean_array_push(v___x_1801_, v___x_1776_);
v___x_1803_ = lean_array_push(v___x_1802_, v_val_1777_);
v___x_1804_ = lean_array_push(v___x_1803_, v_a_1793_);
v___x_1805_ = l_Lean_mkAppN(v___x_1797_, v___x_1804_);
lean_dec_ref(v___x_1804_);
v___x_1806_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1778_, v___x_1805_, v___y_1788_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1824_; 
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1824_ == 0)
{
lean_object* v_unused_1825_; 
v_unused_1825_ = lean_ctor_get(v___x_1806_, 0);
lean_dec(v_unused_1825_);
v___x_1808_ = v___x_1806_;
v_isShared_1809_ = v_isSharedCheck_1824_;
goto v_resetjp_1807_;
}
else
{
lean_dec(v___x_1806_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1824_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; lean_object* v_toGoalState_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1822_; 
v___x_1810_ = lean_st_ref_get(v___y_1781_);
v_toGoalState_1811_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1822_ == 0)
{
lean_object* v_unused_1823_; 
v_unused_1823_ = lean_ctor_get(v___x_1810_, 1);
lean_dec(v_unused_1823_);
v___x_1813_ = v___x_1810_;
v_isShared_1814_ = v_isSharedCheck_1822_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_toGoalState_1811_);
lean_dec(v___x_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1822_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 1, v___x_1779_);
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_toGoalState_1811_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v___x_1779_);
v___x_1816_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1817_, 0, v_a_1780_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v___x_1817_);
v___x_1819_ = v___x_1808_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_dec(v_a_1780_);
lean_dec(v___x_1779_);
v_a_1826_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1806_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1806_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
lean_dec(v_a_1780_);
lean_dec(v___x_1779_);
lean_dec(v_mvarId_1778_);
lean_dec_ref(v_val_1777_);
lean_dec_ref(v___x_1776_);
lean_dec_ref(v_expr_1775_);
lean_dec_ref(v___x_1774_);
lean_dec(v_a_1773_);
v_a_1834_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1792_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1792_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1768_ = stack[0].m_obj;
lean_object* v_a_1769_ = stack[1].m_obj;
uint8_t v___y_1770_ = stack[2].m_num;
uint8_t v___x_1771_ = stack[3].m_num;
uint8_t v___x_1772_ = stack[4].m_num;
lean_object* v_a_1773_ = stack[5].m_obj;
lean_object* v___x_1774_ = stack[6].m_obj;
lean_object* v_expr_1775_ = stack[7].m_obj;
lean_object* v___x_1776_ = stack[8].m_obj;
lean_object* v_val_1777_ = stack[9].m_obj;
lean_object* v_mvarId_1778_ = stack[10].m_obj;
lean_object* v___x_1779_ = stack[11].m_obj;
lean_object* v_a_1780_ = stack[12].m_obj;
lean_object* v___y_1781_ = stack[13].m_obj;
lean_object* v___y_1782_ = stack[14].m_obj;
lean_object* v___y_1783_ = stack[15].m_obj;
lean_object* v___y_1784_ = stack[16].m_obj;
lean_object* v___y_1785_ = stack[17].m_obj;
lean_object* v___y_1786_ = stack[18].m_obj;
lean_object* v___y_1787_ = stack[19].m_obj;
lean_object* v___y_1788_ = stack[20].m_obj;
lean_object* v___y_1789_ = stack[21].m_obj;
lean_object* v___y_1790_ = stack[22].m_obj;
lean_object* v_res_1842_;
v_res_1842_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(v___x_1768_, v_a_1769_, v___y_1770_, v___x_1771_, v___x_1772_, v_a_1773_, v___x_1774_, v_expr_1775_, v___x_1776_, v_val_1777_, v_mvarId_1778_, v___x_1779_, v_a_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
stack->m_obj
 = v_res_1842_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed(lean_object** _args){
lean_object* v___x_1843_ = _args[0];
lean_object* v_a_1844_ = _args[1];
lean_object* v___y_1845_ = _args[2];
lean_object* v___x_1846_ = _args[3];
lean_object* v___x_1847_ = _args[4];
lean_object* v_a_1848_ = _args[5];
lean_object* v___x_1849_ = _args[6];
lean_object* v_expr_1850_ = _args[7];
lean_object* v___x_1851_ = _args[8];
lean_object* v_val_1852_ = _args[9];
lean_object* v_mvarId_1853_ = _args[10];
lean_object* v___x_1854_ = _args[11];
lean_object* v_a_1855_ = _args[12];
lean_object* v___y_1856_ = _args[13];
lean_object* v___y_1857_ = _args[14];
lean_object* v___y_1858_ = _args[15];
lean_object* v___y_1859_ = _args[16];
lean_object* v___y_1860_ = _args[17];
lean_object* v___y_1861_ = _args[18];
lean_object* v___y_1862_ = _args[19];
lean_object* v___y_1863_ = _args[20];
lean_object* v___y_1864_ = _args[21];
lean_object* v___y_1865_ = _args[22];
lean_object* v___y_1866_ = _args[23];
_start:
{
uint8_t v___y_152659__boxed_1867_; uint8_t v___x_152660__boxed_1868_; uint8_t v___x_152661__boxed_1869_; lean_object* v_res_1870_; 
v___y_152659__boxed_1867_ = lean_unbox(v___y_1845_);
v___x_152660__boxed_1868_ = lean_unbox(v___x_1846_);
v___x_152661__boxed_1869_ = lean_unbox(v___x_1847_);
v_res_1870_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(v___x_1843_, v_a_1844_, v___y_152659__boxed_1867_, v___x_152660__boxed_1868_, v___x_152661__boxed_1869_, v_a_1848_, v___x_1849_, v_expr_1850_, v___x_1851_, v_val_1852_, v_mvarId_1853_, v___x_1854_, v_a_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___x_1843_);
return v_res_1870_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(lean_object* v___x_1876_, lean_object* v_a_1877_, uint8_t v___x_1878_, uint8_t v___x_1879_, uint8_t v___x_1880_, lean_object* v_a_1881_, lean_object* v___x_1882_, lean_object* v___x_1883_, lean_object* v_expr_1884_, lean_object* v___x_1885_, lean_object* v_val_1886_, lean_object* v_mvarId_1887_, lean_object* v___x_1888_, lean_object* v_a_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Lean_Meta_mkLambdaFVars(v___x_1876_, v_a_1877_, v___x_1878_, v___x_1879_, v___x_1878_, v___x_1879_, v___x_1880_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref_known(v___x_1901_, 1);
v___x_1903_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1));
v___x_1904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1904_, 0, v_a_1881_);
lean_ctor_set(v___x_1904_, 1, v___x_1882_);
v___x_1905_ = l_Lean_mkConst(v___x_1903_, v___x_1904_);
v___x_1906_ = lean_unsigned_to_nat(5u);
v___x_1907_ = lean_mk_empty_array_with_capacity(v___x_1906_);
v___x_1908_ = lean_array_push(v___x_1907_, v___x_1883_);
v___x_1909_ = lean_array_push(v___x_1908_, v_expr_1884_);
v___x_1910_ = lean_array_push(v___x_1909_, v___x_1885_);
v___x_1911_ = lean_array_push(v___x_1910_, v_val_1886_);
v___x_1912_ = lean_array_push(v___x_1911_, v_a_1902_);
v___x_1913_ = l_Lean_mkAppN(v___x_1905_, v___x_1912_);
lean_dec_ref(v___x_1912_);
v___x_1914_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1887_, v___x_1913_, v___y_1897_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1932_; 
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1932_ == 0)
{
lean_object* v_unused_1933_; 
v_unused_1933_ = lean_ctor_get(v___x_1914_, 0);
lean_dec(v_unused_1933_);
v___x_1916_ = v___x_1914_;
v_isShared_1917_ = v_isSharedCheck_1932_;
goto v_resetjp_1915_;
}
else
{
lean_dec(v___x_1914_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1932_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1918_; lean_object* v_toGoalState_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1930_; 
v___x_1918_ = lean_st_ref_get(v___y_1890_);
v_toGoalState_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1930_ == 0)
{
lean_object* v_unused_1931_; 
v_unused_1931_ = lean_ctor_get(v___x_1918_, 1);
lean_dec(v_unused_1931_);
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1930_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_toGoalState_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1930_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 1, v___x_1888_);
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_toGoalState_1919_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v___x_1888_);
v___x_1924_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1925_, 0, v_a_1889_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 0, v___x_1925_);
v___x_1927_ = v___x_1916_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
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
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_dec(v_a_1889_);
lean_dec(v___x_1888_);
v_a_1934_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1914_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1914_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_dec(v_a_1889_);
lean_dec(v___x_1888_);
lean_dec(v_mvarId_1887_);
lean_dec_ref(v_val_1886_);
lean_dec_ref(v___x_1885_);
lean_dec_ref(v_expr_1884_);
lean_dec_ref(v___x_1883_);
lean_dec(v___x_1882_);
lean_dec(v_a_1881_);
v_a_1942_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1901_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1901_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1876_ = stack[0].m_obj;
lean_object* v_a_1877_ = stack[1].m_obj;
uint8_t v___x_1878_ = stack[2].m_num;
uint8_t v___x_1879_ = stack[3].m_num;
uint8_t v___x_1880_ = stack[4].m_num;
lean_object* v_a_1881_ = stack[5].m_obj;
lean_object* v___x_1882_ = stack[6].m_obj;
lean_object* v___x_1883_ = stack[7].m_obj;
lean_object* v_expr_1884_ = stack[8].m_obj;
lean_object* v___x_1885_ = stack[9].m_obj;
lean_object* v_val_1886_ = stack[10].m_obj;
lean_object* v_mvarId_1887_ = stack[11].m_obj;
lean_object* v___x_1888_ = stack[12].m_obj;
lean_object* v_a_1889_ = stack[13].m_obj;
lean_object* v___y_1890_ = stack[14].m_obj;
lean_object* v___y_1891_ = stack[15].m_obj;
lean_object* v___y_1892_ = stack[16].m_obj;
lean_object* v___y_1893_ = stack[17].m_obj;
lean_object* v___y_1894_ = stack[18].m_obj;
lean_object* v___y_1895_ = stack[19].m_obj;
lean_object* v___y_1896_ = stack[20].m_obj;
lean_object* v___y_1897_ = stack[21].m_obj;
lean_object* v___y_1898_ = stack[22].m_obj;
lean_object* v___y_1899_ = stack[23].m_obj;
lean_object* v_res_1950_;
v_res_1950_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(v___x_1876_, v_a_1877_, v___x_1878_, v___x_1879_, v___x_1880_, v_a_1881_, v___x_1882_, v___x_1883_, v_expr_1884_, v___x_1885_, v_val_1886_, v_mvarId_1887_, v___x_1888_, v_a_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
stack->m_obj
 = v_res_1950_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed(lean_object** _args){
lean_object* v___x_1951_ = _args[0];
lean_object* v_a_1952_ = _args[1];
lean_object* v___x_1953_ = _args[2];
lean_object* v___x_1954_ = _args[3];
lean_object* v___x_1955_ = _args[4];
lean_object* v_a_1956_ = _args[5];
lean_object* v___x_1957_ = _args[6];
lean_object* v___x_1958_ = _args[7];
lean_object* v_expr_1959_ = _args[8];
lean_object* v___x_1960_ = _args[9];
lean_object* v_val_1961_ = _args[10];
lean_object* v_mvarId_1962_ = _args[11];
lean_object* v___x_1963_ = _args[12];
lean_object* v_a_1964_ = _args[13];
lean_object* v___y_1965_ = _args[14];
lean_object* v___y_1966_ = _args[15];
lean_object* v___y_1967_ = _args[16];
lean_object* v___y_1968_ = _args[17];
lean_object* v___y_1969_ = _args[18];
lean_object* v___y_1970_ = _args[19];
lean_object* v___y_1971_ = _args[20];
lean_object* v___y_1972_ = _args[21];
lean_object* v___y_1973_ = _args[22];
lean_object* v___y_1974_ = _args[23];
lean_object* v___y_1975_ = _args[24];
_start:
{
uint8_t v___x_152939__boxed_1976_; uint8_t v___x_152940__boxed_1977_; uint8_t v___x_152941__boxed_1978_; lean_object* v_res_1979_; 
v___x_152939__boxed_1976_ = lean_unbox(v___x_1953_);
v___x_152940__boxed_1977_ = lean_unbox(v___x_1954_);
v___x_152941__boxed_1978_ = lean_unbox(v___x_1955_);
v_res_1979_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(v___x_1951_, v_a_1952_, v___x_152939__boxed_1976_, v___x_152940__boxed_1977_, v___x_152941__boxed_1978_, v_a_1956_, v___x_1957_, v___x_1958_, v_expr_1959_, v___x_1960_, v_val_1961_, v_mvarId_1962_, v___x_1963_, v_a_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
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
lean_dec_ref(v___x_1951_);
return v_res_1979_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(lean_object* v___x_1980_, lean_object* v_a_1981_, uint8_t v___y_1982_, uint8_t v___x_1983_, uint8_t v___x_1984_, lean_object* v_mvarId_1985_, lean_object* v___x_1986_, lean_object* v_a_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_Meta_mkLambdaFVars(v___x_1980_, v_a_1981_, v___y_1982_, v___x_1983_, v___y_1982_, v___x_1983_, v___x_1984_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2001_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___x_1999_, 1);
v___x_2001_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_1985_, v_a_2000_, v___y_1995_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2019_; 
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2019_ == 0)
{
lean_object* v_unused_2020_; 
v_unused_2020_ = lean_ctor_get(v___x_2001_, 0);
lean_dec(v_unused_2020_);
v___x_2003_ = v___x_2001_;
v_isShared_2004_ = v_isSharedCheck_2019_;
goto v_resetjp_2002_;
}
else
{
lean_dec(v___x_2001_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2019_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v_toGoalState_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2017_; 
v___x_2005_ = lean_st_ref_get(v___y_1988_);
v_toGoalState_2006_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2017_ == 0)
{
lean_object* v_unused_2018_; 
v_unused_2018_ = lean_ctor_get(v___x_2005_, 1);
lean_dec(v_unused_2018_);
v___x_2008_ = v___x_2005_;
v_isShared_2009_ = v_isSharedCheck_2017_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_toGoalState_2006_);
lean_dec(v___x_2005_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2017_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 1, v___x_1986_);
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_toGoalState_2006_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v___x_1986_);
v___x_2011_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2012_; lean_object* v___x_2014_; 
v___x_2012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2012_, 0, v_a_1987_);
lean_ctor_set(v___x_2012_, 1, v___x_2011_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2012_);
v___x_2014_ = v___x_2003_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2012_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
lean_dec(v_a_1987_);
lean_dec(v___x_1986_);
v_a_2021_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_2001_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2001_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v_a_1987_);
lean_dec(v___x_1986_);
lean_dec(v_mvarId_1985_);
v_a_2029_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_1999_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_1999_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1980_ = stack[0].m_obj;
lean_object* v_a_1981_ = stack[1].m_obj;
uint8_t v___y_1982_ = stack[2].m_num;
uint8_t v___x_1983_ = stack[3].m_num;
uint8_t v___x_1984_ = stack[4].m_num;
lean_object* v_mvarId_1985_ = stack[5].m_obj;
lean_object* v___x_1986_ = stack[6].m_obj;
lean_object* v_a_1987_ = stack[7].m_obj;
lean_object* v___y_1988_ = stack[8].m_obj;
lean_object* v___y_1989_ = stack[9].m_obj;
lean_object* v___y_1990_ = stack[10].m_obj;
lean_object* v___y_1991_ = stack[11].m_obj;
lean_object* v___y_1992_ = stack[12].m_obj;
lean_object* v___y_1993_ = stack[13].m_obj;
lean_object* v___y_1994_ = stack[14].m_obj;
lean_object* v___y_1995_ = stack[15].m_obj;
lean_object* v___y_1996_ = stack[16].m_obj;
lean_object* v___y_1997_ = stack[17].m_obj;
lean_object* v_res_2037_;
v_res_2037_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(v___x_1980_, v_a_1981_, v___y_1982_, v___x_1983_, v___x_1984_, v_mvarId_1985_, v___x_1986_, v_a_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
stack->m_obj
 = v_res_2037_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed(lean_object** _args){
lean_object* v___x_2038_ = _args[0];
lean_object* v_a_2039_ = _args[1];
lean_object* v___y_2040_ = _args[2];
lean_object* v___x_2041_ = _args[3];
lean_object* v___x_2042_ = _args[4];
lean_object* v_mvarId_2043_ = _args[5];
lean_object* v___x_2044_ = _args[6];
lean_object* v_a_2045_ = _args[7];
lean_object* v___y_2046_ = _args[8];
lean_object* v___y_2047_ = _args[9];
lean_object* v___y_2048_ = _args[10];
lean_object* v___y_2049_ = _args[11];
lean_object* v___y_2050_ = _args[12];
lean_object* v___y_2051_ = _args[13];
lean_object* v___y_2052_ = _args[14];
lean_object* v___y_2053_ = _args[15];
lean_object* v___y_2054_ = _args[16];
lean_object* v___y_2055_ = _args[17];
lean_object* v___y_2056_ = _args[18];
_start:
{
uint8_t v___y_153209__boxed_2057_; uint8_t v___x_153210__boxed_2058_; uint8_t v___x_153211__boxed_2059_; lean_object* v_res_2060_; 
v___y_153209__boxed_2057_ = lean_unbox(v___y_2040_);
v___x_153210__boxed_2058_ = lean_unbox(v___x_2041_);
v___x_153211__boxed_2059_ = lean_unbox(v___x_2042_);
v_res_2060_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(v___x_2038_, v_a_2039_, v___y_153209__boxed_2057_, v___x_153210__boxed_2058_, v___x_153211__boxed_2059_, v_mvarId_2043_, v___x_2044_, v_a_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec(v___y_2046_);
lean_dec_ref(v___x_2038_);
return v_res_2060_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(lean_object* v_mvarId_2063_, lean_object* v___x_2064_, lean_object* v_generation_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v___x_2077_; 
lean_inc(v_mvarId_2063_);
v___x_2077_ = l_Lean_MVarId_getTag(v_mvarId_2063_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2079_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
lean_dec_ref_known(v___x_2077_, 1);
v___x_2079_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2064_, v_a_2078_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2081_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc_n(v_a_2080_, 2);
lean_dec_ref_known(v___x_2079_, 1);
v___x_2081_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2063_, v_a_2080_, v___y_2073_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v___x_2082_; lean_object* v_toGoalState_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2092_; 
lean_dec_ref_known(v___x_2081_, 1);
v___x_2082_ = lean_st_ref_get(v___y_2066_);
v_toGoalState_2083_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2092_ == 0)
{
lean_object* v_unused_2093_; 
v_unused_2093_ = lean_ctor_get(v___x_2082_, 1);
lean_dec(v_unused_2093_);
v___x_2085_ = v___x_2082_;
v_isShared_2086_ = v_isSharedCheck_2092_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_toGoalState_2083_);
lean_dec(v___x_2082_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2092_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2087_; lean_object* v___x_2089_; 
v___x_2087_ = l_Lean_Expr_mvarId_x21(v_a_2080_);
lean_dec(v_a_2080_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 1, v___x_2087_);
v___x_2089_ = v___x_2085_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_toGoalState_2083_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v___x_2087_);
v___x_2089_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
lean_object* v___x_2090_; 
v___x_2090_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v___x_2089_, v_generation_2065_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
return v___x_2090_;
}
}
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
lean_dec(v_a_2080_);
lean_dec(v_generation_2065_);
v_a_2094_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_2081_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2081_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec(v_generation_2065_);
lean_dec(v_mvarId_2063_);
v_a_2102_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2079_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2079_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_dec(v_generation_2065_);
lean_dec_ref(v___x_2064_);
lean_dec(v_mvarId_2063_);
v_a_2110_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2077_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2077_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2063_ = stack[0].m_obj;
lean_object* v___x_2064_ = stack[1].m_obj;
lean_object* v_generation_2065_ = stack[2].m_obj;
lean_object* v___y_2066_ = stack[3].m_obj;
lean_object* v___y_2067_ = stack[4].m_obj;
lean_object* v___y_2068_ = stack[5].m_obj;
lean_object* v___y_2069_ = stack[6].m_obj;
lean_object* v___y_2070_ = stack[7].m_obj;
lean_object* v___y_2071_ = stack[8].m_obj;
lean_object* v___y_2072_ = stack[9].m_obj;
lean_object* v___y_2073_ = stack[10].m_obj;
lean_object* v___y_2074_ = stack[11].m_obj;
lean_object* v___y_2075_ = stack[12].m_obj;
lean_object* v_res_2118_;
v_res_2118_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(v_mvarId_2063_, v___x_2064_, v_generation_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
stack->m_obj
 = v_res_2118_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed(lean_object* v_mvarId_2119_, lean_object* v___x_2120_, lean_object* v_generation_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(v_mvarId_2119_, v___x_2120_, v_generation_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec(v___y_2122_);
return v_res_2133_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4(void){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2139_ = lean_box(0);
v___x_2140_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3));
v___x_2141_ = l_Lean_mkConst(v___x_2140_, v___x_2139_);
return v___x_2141_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(lean_object* v_goal_2142_, lean_object* v_generation_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v___x_2154_; lean_object* v_a_2156_; lean_object* v___y_2161_; lean_object* v___x_2171_; lean_object* v_mvarId_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2460_; 
lean_inc_ref(v_goal_2142_);
v___x_2154_ = lean_st_mk_ref(v_goal_2142_);
v___x_2171_ = lean_st_ref_get(v___x_2154_);
v_mvarId_2172_ = lean_ctor_get(v___x_2171_, 1);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2460_ == 0)
{
lean_object* v_unused_2461_; 
v_unused_2461_ = lean_ctor_get(v___x_2171_, 0);
lean_dec(v_unused_2461_);
v___x_2174_ = v___x_2171_;
v_isShared_2175_ = v_isSharedCheck_2460_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_mvarId_2172_);
lean_dec(v___x_2171_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2460_;
goto v_resetjp_2173_;
}
v___jp_2155_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2157_ = lean_st_ref_get(v___x_2154_);
lean_dec(v___x_2154_);
v___x_2158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2158_, 0, v_a_2156_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
return v___x_2159_;
}
v___jp_2160_:
{
if (lean_obj_tag(v___y_2161_) == 0)
{
lean_object* v_a_2162_; 
v_a_2162_ = lean_ctor_get(v___y_2161_, 0);
lean_inc(v_a_2162_);
lean_dec_ref_known(v___y_2161_, 1);
v_a_2156_ = v_a_2162_;
goto v___jp_2155_;
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
lean_dec(v___x_2154_);
v_a_2163_ = lean_ctor_get(v___y_2161_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___y_2161_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___y_2161_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___y_2161_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2163_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
v_resetjp_2173_:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lean_MVarId_getType(v_mvarId_2172_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; uint8_t v___x_2178_; uint8_t v___x_2179_; lean_object* v___y_2181_; lean_object* v___y_2182_; uint8_t v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v___y_2196_; lean_object* v___y_2197_; lean_object* v___y_2198_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2176_, 1);
v___x_2178_ = l_Lean_Expr_isForall(v_a_2177_);
v___x_2179_ = 1;
if (v___x_2178_ == 0)
{
uint8_t v___x_2221_; 
lean_del_object(v___x_2174_);
v___x_2221_ = l_Lean_Expr_isLet(v_a_2177_);
if (v___x_2221_ == 0)
{
lean_object* v___x_2222_; 
lean_dec(v_a_2177_);
lean_dec_ref(v___y_2149_);
lean_dec(v_generation_2143_);
v___x_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2222_, 0, v_goal_2142_);
v_a_2156_ = v___x_2222_;
goto v___jp_2155_;
}
else
{
lean_object* v___x_2223_; 
lean_dec_ref(v_goal_2142_);
v___x_2223_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_2145_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v_a_2224_; uint8_t v_zetaDelta_2225_; 
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_a_2224_);
lean_dec_ref_known(v___x_2223_, 1);
v_zetaDelta_2225_ = lean_ctor_get_uint8(v_a_2224_, sizeof(void*)*14 + 19);
lean_dec(v_a_2224_);
if (v_zetaDelta_2225_ == 0)
{
lean_object* v___x_2226_; 
lean_dec(v_a_2177_);
v___x_2226_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_2154_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___f_2228_; lean_object* v___x_2229_; lean_object* v_mvarId_2230_; lean_object* v___x_2231_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec_ref_known(v___x_2226_, 1);
v___f_2228_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed), 13, 2);
lean_closure_set(v___f_2228_, 0, v_a_2227_);
lean_closure_set(v___f_2228_, 1, v_generation_2143_);
v___x_2229_ = lean_st_ref_get(v___x_2154_);
v_mvarId_2230_ = lean_ctor_get(v___x_2229_, 1);
lean_inc(v_mvarId_2230_);
lean_dec(v___x_2229_);
v___x_2231_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_2230_, v___f_2228_, v___x_2154_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
lean_dec_ref(v___y_2149_);
v___y_2161_ = v___x_2231_;
goto v___jp_2160_;
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec(v___x_2154_);
lean_dec_ref(v___y_2149_);
lean_dec(v_generation_2143_);
v_a_2232_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2226_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2226_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
else
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v_mvarId_2243_; lean_object* v___f_2244_; lean_object* v___x_2245_; 
v___x_2240_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__0));
v___x_2241_ = l_Lean_Meta_expandLet(v_a_2177_, v___x_2240_, v___x_2179_);
lean_dec(v_a_2177_);
v___x_2242_ = lean_st_ref_get(v___x_2154_);
v_mvarId_2243_ = lean_ctor_get(v___x_2242_, 1);
lean_inc_n(v_mvarId_2243_, 2);
lean_dec(v___x_2242_);
v___f_2244_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed), 14, 3);
lean_closure_set(v___f_2244_, 0, v_mvarId_2243_);
lean_closure_set(v___f_2244_, 1, v___x_2241_);
lean_closure_set(v___f_2244_, 2, v_generation_2143_);
v___x_2245_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_2243_, v___f_2244_, v___x_2154_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
lean_dec_ref(v___y_2149_);
v___y_2161_ = v___x_2245_;
goto v___jp_2160_;
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_dec(v_a_2177_);
lean_dec(v___x_2154_);
lean_dec_ref(v___y_2149_);
lean_dec(v_generation_2143_);
v_a_2246_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2223_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2223_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
}
else
{
lean_object* v___x_2254_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; uint8_t v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; uint8_t v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v_localInsts_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___x_2352_; 
lean_dec(v_generation_2143_);
lean_dec_ref(v_goal_2142_);
v___x_2254_ = l_Lean_Expr_bindingDomain_x21(v_a_2177_);
lean_inc_ref(v___x_2254_);
v___x_2352_ = l_Lean_Meta_isProp(v___x_2254_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; uint8_t v___y_2355_; uint8_t v___x_2428_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_a_2353_);
lean_dec_ref_known(v___x_2352_, 1);
v___x_2428_ = lean_unbox(v_a_2353_);
lean_dec(v_a_2353_);
if (v___x_2428_ == 0)
{
if (v___x_2178_ == 0)
{
lean_del_object(v___x_2174_);
v___y_2355_ = v___x_2178_;
goto v___jp_2354_;
}
else
{
lean_object* v___x_2429_; 
lean_dec_ref(v___x_2254_);
lean_dec(v_a_2177_);
v___x_2429_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_2154_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
lean_dec_ref(v___y_2149_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v___x_2431_; lean_object* v___x_2433_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2429_, 1);
v___x_2431_ = lean_st_ref_get(v___x_2154_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set_tag(v___x_2174_, 3);
lean_ctor_set(v___x_2174_, 1, v___x_2431_);
lean_ctor_set(v___x_2174_, 0, v_a_2430_);
v___x_2433_ = v___x_2174_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2430_);
lean_ctor_set(v_reuseFailAlloc_2434_, 1, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
v_a_2156_ = v___x_2433_;
goto v___jp_2155_;
}
}
else
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
lean_del_object(v___x_2174_);
lean_dec(v___x_2154_);
v_a_2435_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2429_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2429_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
}
else
{
uint8_t v___x_2443_; 
lean_del_object(v___x_2174_);
v___x_2443_ = 0;
v___y_2355_ = v___x_2443_;
goto v___jp_2354_;
}
v___jp_2354_:
{
lean_object* v___x_2356_; lean_object* v_mvarId_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2426_; 
v___x_2356_ = lean_st_ref_get(v___x_2154_);
v_mvarId_2357_ = lean_ctor_get(v___x_2356_, 1);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2426_ == 0)
{
lean_object* v_unused_2427_; 
v_unused_2427_ = lean_ctor_get(v___x_2356_, 0);
lean_dec(v_unused_2427_);
v___x_2359_ = v___x_2356_;
v_isShared_2360_ = v_isSharedCheck_2426_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_mvarId_2357_);
lean_dec(v___x_2356_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2426_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2361_; 
lean_inc(v_mvarId_2357_);
v___x_2361_ = l_Lean_MVarId_getTag(v_mvarId_2357_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v___x_2363_ = l_Lean_Expr_bindingBody_x21(v_a_2177_);
v___x_2364_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___x_2154_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc_n(v_a_2365_, 2);
lean_dec_ref_known(v___x_2364_, 1);
v___x_2366_ = l_Lean_mkFVar(v_a_2365_);
lean_inc_ref(v___x_2254_);
v___x_2367_ = l_Lean_Meta_Grind_preprocessHypothesis(v___x_2254_, v___x_2154_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v_a_2368_; lean_object* v_lctx_2369_; lean_object* v_localInstances_2370_; lean_object* v_expr_2371_; lean_object* v_proof_x3f_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
lean_inc(v_a_2368_);
lean_dec_ref_known(v___x_2367_, 1);
v_lctx_2369_ = lean_ctor_get(v___y_2149_, 2);
v_localInstances_2370_ = lean_ctor_get(v___y_2149_, 3);
v_expr_2371_ = lean_ctor_get(v_a_2368_, 0);
lean_inc_ref_n(v_expr_2371_, 2);
v_proof_x3f_2372_ = lean_ctor_get(v_a_2368_, 1);
lean_inc(v_proof_x3f_2372_);
lean_dec(v_a_2368_);
v___x_2373_ = l_Lean_Expr_bindingName_x21(v_a_2177_);
lean_inc(v___x_2373_);
v___x_2374_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v___x_2373_, v_expr_2371_, v___x_2154_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; uint8_t v___x_2376_; uint8_t v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref_known(v___x_2374_, 1);
v___x_2376_ = l_Lean_Expr_bindingInfo_x21(v_a_2177_);
v___x_2377_ = 0;
lean_inc_ref_n(v_expr_2371_, 2);
lean_inc(v_a_2365_);
lean_inc_ref(v_lctx_2369_);
v___x_2378_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_2369_, v_a_2365_, v_a_2375_, v_expr_2371_, v___x_2376_, v___x_2377_);
v___x_2379_ = l_Lean_Meta_isClass_x3f(v_expr_2371_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_a_2380_);
lean_dec_ref_known(v___x_2379_, 1);
if (lean_obj_tag(v_a_2380_) == 1)
{
lean_object* v_val_2381_; lean_object* v___x_2383_; 
v_val_2381_ = lean_ctor_get(v_a_2380_, 0);
lean_inc(v_val_2381_);
lean_dec_ref_known(v_a_2380_, 1);
lean_inc_ref(v___x_2366_);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 1, v___x_2366_);
lean_ctor_set(v___x_2359_, 0, v_val_2381_);
v___x_2383_ = v___x_2359_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_val_2381_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v___x_2366_);
v___x_2383_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
lean_object* v___x_2384_; 
lean_inc_ref(v_localInstances_2370_);
v___x_2384_ = lean_array_push(v_localInstances_2370_, v___x_2383_);
lean_inc(v___x_2154_);
lean_inc_ref(v___x_2363_);
v___y_2256_ = v_proof_x3f_2372_;
v___y_2257_ = v_expr_2371_;
v___y_2258_ = v_mvarId_2357_;
v___y_2259_ = v_a_2365_;
v___y_2260_ = v___x_2363_;
v___y_2261_ = v___y_2355_;
v___y_2262_ = v___x_2373_;
v___y_2263_ = v___x_2378_;
v___y_2264_ = v___x_2376_;
v___y_2265_ = v___x_2363_;
v___y_2266_ = v_a_2362_;
v___y_2267_ = v___x_2366_;
v_localInsts_2268_ = v___x_2384_;
v___y_2269_ = v___x_2154_;
v___y_2270_ = v___y_2144_;
v___y_2271_ = v___y_2145_;
v___y_2272_ = v___y_2146_;
v___y_2273_ = v___y_2147_;
v___y_2274_ = v___y_2148_;
v___y_2275_ = v___y_2149_;
v___y_2276_ = v___y_2150_;
v___y_2277_ = v___y_2151_;
v___y_2278_ = v___y_2152_;
goto v___jp_2255_;
}
}
else
{
lean_inc_ref(v_localInstances_2370_);
lean_dec(v_a_2380_);
lean_del_object(v___x_2359_);
lean_inc(v___x_2154_);
lean_inc_ref(v___x_2363_);
v___y_2256_ = v_proof_x3f_2372_;
v___y_2257_ = v_expr_2371_;
v___y_2258_ = v_mvarId_2357_;
v___y_2259_ = v_a_2365_;
v___y_2260_ = v___x_2363_;
v___y_2261_ = v___y_2355_;
v___y_2262_ = v___x_2373_;
v___y_2263_ = v___x_2378_;
v___y_2264_ = v___x_2376_;
v___y_2265_ = v___x_2363_;
v___y_2266_ = v_a_2362_;
v___y_2267_ = v___x_2366_;
v_localInsts_2268_ = v_localInstances_2370_;
v___y_2269_ = v___x_2154_;
v___y_2270_ = v___y_2144_;
v___y_2271_ = v___y_2145_;
v___y_2272_ = v___y_2146_;
v___y_2273_ = v___y_2147_;
v___y_2274_ = v___y_2148_;
v___y_2275_ = v___y_2149_;
v___y_2276_ = v___y_2150_;
v___y_2277_ = v___y_2151_;
v___y_2278_ = v___y_2152_;
goto v___jp_2255_;
}
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
lean_dec_ref(v___x_2378_);
lean_dec(v___x_2373_);
lean_dec(v_proof_x3f_2372_);
lean_dec_ref(v_expr_2371_);
lean_dec_ref(v___x_2366_);
lean_dec(v_a_2365_);
lean_dec_ref(v___x_2363_);
lean_dec(v_a_2362_);
lean_del_object(v___x_2359_);
lean_dec(v_mvarId_2357_);
lean_dec_ref(v___x_2254_);
lean_dec(v_a_2177_);
lean_dec(v___x_2154_);
lean_dec_ref(v___y_2149_);
v_a_2386_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2379_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2379_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2386_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2401_; 
lean_dec(v___x_2373_);
lean_dec(v_proof_x3f_2372_);
lean_dec_ref(v_expr_2371_);
lean_dec_ref(v___x_2366_);
lean_dec(v_a_2365_);
lean_dec_ref(v___x_2363_);
lean_dec(v_a_2362_);
lean_del_object(v___x_2359_);
lean_dec(v_mvarId_2357_);
lean_dec_ref(v___x_2254_);
lean_dec(v_a_2177_);
lean_dec(v___x_2154_);
lean_dec_ref(v___y_2149_);
v_a_2394_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2396_ = v___x_2374_;
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2374_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2397_ == 0)
{
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
lean_dec_ref(v___x_2366_);
lean_dec(v_a_2365_);
lean_dec_ref(v___x_2363_);
lean_dec(v_a_2362_);
lean_del_object(v___x_2359_);
lean_dec(v_mvarId_2357_);
lean_dec_ref(v___x_2254_);
lean_dec(v_a_2177_);
lean_dec(v___x_2154_);
lean_dec_ref(v___y_2149_);
v_a_2402_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2367_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2367_);
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
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
lean_dec_ref(v___x_2363_);
lean_dec(v_a_2362_);
lean_del_object(v___x_2359_);
lean_dec(v_mvarId_2357_);
lean_dec_ref(v___x_2254_);
lean_dec(v_a_2177_);
lean_dec(v___x_2154_);
lean_dec_ref(v___y_2149_);
v_a_2410_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2364_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2364_);
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
lean_del_object(v___x_2359_);
lean_dec(v_mvarId_2357_);
lean_dec_ref(v___x_2254_);
lean_dec(v_a_2177_);
lean_dec(v___x_2154_);
lean_dec_ref(v___y_2149_);
v_a_2418_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2420_ = v___x_2361_;
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2361_);
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
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_dec_ref(v___x_2254_);
lean_dec(v_a_2177_);
lean_del_object(v___x_2174_);
lean_dec(v___x_2154_);
lean_dec_ref(v___y_2149_);
v_a_2444_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2352_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2352_);
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
v___jp_2255_:
{
if (lean_obj_tag(v___y_2256_) == 0)
{
uint8_t v___x_2279_; 
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2260_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v___x_2254_);
v___x_2279_ = l_Lean_Expr_isArrow(v_a_2177_);
lean_dec(v_a_2177_);
if (v___x_2279_ == 0)
{
lean_object* v___x_2280_; 
v___x_2280_ = lean_expr_instantiate1(v___y_2265_, v___y_2267_);
lean_dec_ref(v___y_2265_);
v___y_2181_ = v___y_2258_;
v___y_2182_ = v___y_2259_;
v___y_2183_ = v___y_2261_;
v___y_2184_ = v___y_2263_;
v___y_2185_ = v___y_2272_;
v___y_2186_ = v___y_2267_;
v___y_2187_ = v___y_2275_;
v___y_2188_ = v___y_2270_;
v___y_2189_ = v___y_2274_;
v___y_2190_ = v___y_2278_;
v___y_2191_ = v_localInsts_2268_;
v___y_2192_ = v___y_2269_;
v___y_2193_ = v___y_2276_;
v___y_2194_ = v___y_2273_;
v___y_2195_ = v___y_2266_;
v___y_2196_ = v___y_2271_;
v___y_2197_ = v___y_2277_;
v___y_2198_ = v___x_2280_;
goto v___jp_2180_;
}
else
{
v___y_2181_ = v___y_2258_;
v___y_2182_ = v___y_2259_;
v___y_2183_ = v___y_2261_;
v___y_2184_ = v___y_2263_;
v___y_2185_ = v___y_2272_;
v___y_2186_ = v___y_2267_;
v___y_2187_ = v___y_2275_;
v___y_2188_ = v___y_2270_;
v___y_2189_ = v___y_2274_;
v___y_2190_ = v___y_2278_;
v___y_2191_ = v_localInsts_2268_;
v___y_2192_ = v___y_2269_;
v___y_2193_ = v___y_2276_;
v___y_2194_ = v___y_2273_;
v___y_2195_ = v___y_2266_;
v___y_2196_ = v___y_2271_;
v___y_2197_ = v___y_2277_;
v___y_2198_ = v___y_2265_;
goto v___jp_2180_;
}
}
else
{
lean_object* v_val_2281_; uint8_t v___x_2282_; 
v_val_2281_ = lean_ctor_get(v___y_2256_, 0);
lean_inc(v_val_2281_);
lean_dec_ref_known(v___y_2256_, 1);
v___x_2282_ = l_Lean_Expr_isArrow(v_a_2177_);
lean_dec(v_a_2177_);
if (v___x_2282_ == 0)
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
lean_dec_ref(v___y_2260_);
lean_inc_ref(v___y_2265_);
lean_inc_ref_n(v___x_2254_, 2);
v___x_2283_ = l_Lean_mkLambda(v___y_2262_, v___y_2264_, v___x_2254_, v___y_2265_);
v___x_2284_ = lean_box(0);
v___x_2285_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4);
lean_inc_ref(v___y_2267_);
lean_inc(v_val_2281_);
lean_inc_ref(v___y_2257_);
v___x_2286_ = l_Lean_mkApp4(v___x_2285_, v___x_2254_, v___y_2257_, v_val_2281_, v___y_2267_);
v___x_2287_ = lean_expr_instantiate1(v___y_2265_, v___x_2286_);
lean_dec_ref(v___x_2286_);
lean_dec_ref(v___y_2265_);
lean_inc_ref(v___x_2287_);
v___x_2288_ = l_Lean_Meta_getLevel(v___x_2287_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; uint8_t v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_a_2289_);
lean_dec_ref_known(v___x_2288_, 1);
v___x_2290_ = 2;
v___x_2291_ = lean_unsigned_to_nat(0u);
v___x_2292_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_2263_, v_localInsts_2268_, v___x_2287_, v___x_2290_, v___y_2266_, v___x_2291_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; uint8_t v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___f_2302_; lean_object* v___x_2303_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
lean_dec_ref_known(v___x_2292_, 1);
v___x_2294_ = l_Lean_Expr_mvarId_x21(v_a_2293_);
v___x_2295_ = lean_unsigned_to_nat(1u);
v___x_2296_ = lean_mk_empty_array_with_capacity(v___x_2295_);
v___x_2297_ = lean_array_push(v___x_2296_, v___y_2267_);
v___x_2298_ = 1;
v___x_2299_ = lean_box(v___x_2282_);
v___x_2300_ = lean_box(v___x_2179_);
v___x_2301_ = lean_box(v___x_2298_);
lean_inc(v___x_2294_);
v___f_2302_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed), 25, 14);
lean_closure_set(v___f_2302_, 0, v___x_2297_);
lean_closure_set(v___f_2302_, 1, v_a_2293_);
lean_closure_set(v___f_2302_, 2, v___x_2299_);
lean_closure_set(v___f_2302_, 3, v___x_2300_);
lean_closure_set(v___f_2302_, 4, v___x_2301_);
lean_closure_set(v___f_2302_, 5, v_a_2289_);
lean_closure_set(v___f_2302_, 6, v___x_2284_);
lean_closure_set(v___f_2302_, 7, v___x_2254_);
lean_closure_set(v___f_2302_, 8, v___y_2257_);
lean_closure_set(v___f_2302_, 9, v___x_2283_);
lean_closure_set(v___f_2302_, 10, v_val_2281_);
lean_closure_set(v___f_2302_, 11, v___y_2258_);
lean_closure_set(v___f_2302_, 12, v___x_2294_);
lean_closure_set(v___f_2302_, 13, v___y_2259_);
v___x_2303_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2294_, v___f_2302_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2269_);
v___y_2161_ = v___x_2303_;
goto v___jp_2160_;
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec(v_a_2289_);
lean_dec_ref(v___x_2283_);
lean_dec(v_val_2281_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v___x_2254_);
lean_dec(v___x_2154_);
v_a_2304_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2292_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2292_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_dec_ref(v___x_2287_);
lean_dec_ref(v___x_2283_);
lean_dec(v_val_2281_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2269_);
lean_dec_ref(v_localInsts_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v___x_2254_);
lean_dec(v___x_2154_);
v_a_2312_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2288_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2288_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
else
{
lean_object* v___x_2320_; 
lean_dec(v___y_2262_);
lean_inc_ref(v___y_2265_);
v___x_2320_ = l_Lean_Meta_getLevel(v___y_2265_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; uint8_t v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2320_, 1);
v___x_2322_ = 2;
v___x_2323_ = lean_unsigned_to_nat(0u);
v___x_2324_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_2263_, v_localInsts_2268_, v___y_2265_, v___x_2322_, v___y_2266_, v___x_2323_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; uint8_t v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___f_2334_; lean_object* v___x_2335_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2325_);
lean_dec_ref_known(v___x_2324_, 1);
v___x_2326_ = l_Lean_Expr_mvarId_x21(v_a_2325_);
v___x_2327_ = lean_unsigned_to_nat(1u);
v___x_2328_ = lean_mk_empty_array_with_capacity(v___x_2327_);
v___x_2329_ = lean_array_push(v___x_2328_, v___y_2267_);
v___x_2330_ = 1;
v___x_2331_ = lean_box(v___y_2261_);
v___x_2332_ = lean_box(v___x_2179_);
v___x_2333_ = lean_box(v___x_2330_);
lean_inc(v___x_2326_);
v___f_2334_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed), 24, 13);
lean_closure_set(v___f_2334_, 0, v___x_2329_);
lean_closure_set(v___f_2334_, 1, v_a_2325_);
lean_closure_set(v___f_2334_, 2, v___x_2331_);
lean_closure_set(v___f_2334_, 3, v___x_2332_);
lean_closure_set(v___f_2334_, 4, v___x_2333_);
lean_closure_set(v___f_2334_, 5, v_a_2321_);
lean_closure_set(v___f_2334_, 6, v___x_2254_);
lean_closure_set(v___f_2334_, 7, v___y_2257_);
lean_closure_set(v___f_2334_, 8, v___y_2260_);
lean_closure_set(v___f_2334_, 9, v_val_2281_);
lean_closure_set(v___f_2334_, 10, v___y_2258_);
lean_closure_set(v___f_2334_, 11, v___x_2326_);
lean_closure_set(v___f_2334_, 12, v___y_2259_);
v___x_2335_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2326_, v___f_2334_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2269_);
v___y_2161_ = v___x_2335_;
goto v___jp_2160_;
}
else
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
lean_dec(v_a_2321_);
lean_dec(v_val_2281_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2267_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v___x_2254_);
lean_dec(v___x_2154_);
v_a_2336_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2324_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2324_);
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
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
lean_dec(v_val_2281_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2269_);
lean_dec_ref(v_localInsts_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec_ref(v___y_2263_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v___x_2254_);
lean_dec(v___x_2154_);
v_a_2344_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2320_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2320_);
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
}
}
}
v___jp_2180_:
{
uint8_t v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2199_ = 2;
v___x_2200_ = lean_unsigned_to_nat(0u);
v___x_2201_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_2184_, v___y_2191_, v___y_2198_, v___x_2199_, v___y_2195_, v___x_2200_, v___y_2187_, v___y_2193_, v___y_2197_, v___y_2190_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; uint8_t v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___f_2211_; lean_object* v___x_2212_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref_known(v___x_2201_, 1);
v___x_2203_ = l_Lean_Expr_mvarId_x21(v_a_2202_);
v___x_2204_ = lean_unsigned_to_nat(1u);
v___x_2205_ = lean_mk_empty_array_with_capacity(v___x_2204_);
v___x_2206_ = lean_array_push(v___x_2205_, v___y_2186_);
v___x_2207_ = 1;
v___x_2208_ = lean_box(v___y_2183_);
v___x_2209_ = lean_box(v___x_2179_);
v___x_2210_ = lean_box(v___x_2207_);
lean_inc(v___x_2203_);
v___f_2211_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed), 19, 8);
lean_closure_set(v___f_2211_, 0, v___x_2206_);
lean_closure_set(v___f_2211_, 1, v_a_2202_);
lean_closure_set(v___f_2211_, 2, v___x_2208_);
lean_closure_set(v___f_2211_, 3, v___x_2209_);
lean_closure_set(v___f_2211_, 4, v___x_2210_);
lean_closure_set(v___f_2211_, 5, v___y_2181_);
lean_closure_set(v___f_2211_, 6, v___x_2203_);
lean_closure_set(v___f_2211_, 7, v___y_2182_);
v___x_2212_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2203_, v___f_2211_, v___y_2192_, v___y_2188_, v___y_2196_, v___y_2185_, v___y_2194_, v___y_2189_, v___y_2187_, v___y_2193_, v___y_2197_, v___y_2190_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2192_);
v___y_2161_ = v___x_2212_;
goto v___jp_2160_;
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec(v___x_2154_);
v_a_2213_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2201_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2201_);
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
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
lean_del_object(v___x_2174_);
lean_dec(v___x_2154_);
lean_dec_ref(v___y_2149_);
lean_dec(v_generation_2143_);
lean_dec_ref(v_goal_2142_);
v_a_2452_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2176_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2176_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_2142_ = stack[0].m_obj;
lean_object* v_generation_2143_ = stack[1].m_obj;
lean_object* v___y_2144_ = stack[2].m_obj;
lean_object* v___y_2145_ = stack[3].m_obj;
lean_object* v___y_2146_ = stack[4].m_obj;
lean_object* v___y_2147_ = stack[5].m_obj;
lean_object* v___y_2148_ = stack[6].m_obj;
lean_object* v___y_2149_ = stack[7].m_obj;
lean_object* v___y_2150_ = stack[8].m_obj;
lean_object* v___y_2151_ = stack[9].m_obj;
lean_object* v___y_2152_ = stack[10].m_obj;
lean_object* v_res_2462_;
v_res_2462_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(v_goal_2142_, v_generation_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
stack->m_obj
 = v_res_2462_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed(lean_object* v_goal_2463_, lean_object* v_generation_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(v_goal_2463_, v_generation_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v___y_2471_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2468_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v___y_2465_);
return v_res_2475_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(lean_object* v_goal_2476_, lean_object* v_generation_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_){
_start:
{
lean_object* v_mvarId_2488_; lean_object* v___f_2489_; lean_object* v___x_2490_; 
v_mvarId_2488_ = lean_ctor_get(v_goal_2476_, 1);
lean_inc(v_mvarId_2488_);
v___f_2489_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed), 12, 2);
lean_closure_set(v___f_2489_, 0, v_goal_2476_);
lean_closure_set(v___f_2489_, 1, v_generation_2477_);
v___x_2490_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_2488_, v___f_2489_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2499_; 
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2493_ = v___x_2490_;
v_isShared_2494_ = v_isSharedCheck_2499_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2490_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2499_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v_fst_2495_; lean_object* v___x_2497_; 
v_fst_2495_ = lean_ctor_get(v_a_2491_, 0);
lean_inc(v_fst_2495_);
lean_dec(v_a_2491_);
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 0, v_fst_2495_);
v___x_2497_ = v___x_2493_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_fst_2495_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
v_a_2500_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2490_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2490_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_2476_ = stack[0].m_obj;
lean_object* v_generation_2477_ = stack[1].m_obj;
lean_object* v_a_2478_ = stack[2].m_obj;
lean_object* v_a_2479_ = stack[3].m_obj;
lean_object* v_a_2480_ = stack[4].m_obj;
lean_object* v_a_2481_ = stack[5].m_obj;
lean_object* v_a_2482_ = stack[6].m_obj;
lean_object* v_a_2483_ = stack[7].m_obj;
lean_object* v_a_2484_ = stack[8].m_obj;
lean_object* v_a_2485_ = stack[9].m_obj;
lean_object* v_a_2486_ = stack[10].m_obj;
lean_object* v_res_2508_;
v_res_2508_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_2476_, v_generation_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_);
stack->m_obj
 = v_res_2508_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___boxed(lean_object* v_goal_2509_, lean_object* v_generation_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_2509_, v_generation_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_);
lean_dec(v_a_2519_);
lean_dec_ref(v_a_2518_);
lean_dec(v_a_2517_);
lean_dec_ref(v_a_2516_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
lean_dec(v_a_2513_);
lean_dec_ref(v_a_2512_);
lean_dec(v_a_2511_);
return v_res_2521_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(lean_object* v_mvarId_2522_, lean_object* v_val_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2522_, v_val_2523_, v___y_2531_);
return v___x_2535_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2522_ = stack[0].m_obj;
lean_object* v_val_2523_ = stack[1].m_obj;
lean_object* v___y_2524_ = stack[2].m_obj;
lean_object* v___y_2525_ = stack[3].m_obj;
lean_object* v___y_2526_ = stack[4].m_obj;
lean_object* v___y_2527_ = stack[5].m_obj;
lean_object* v___y_2528_ = stack[6].m_obj;
lean_object* v___y_2529_ = stack[7].m_obj;
lean_object* v___y_2530_ = stack[8].m_obj;
lean_object* v___y_2531_ = stack[9].m_obj;
lean_object* v___y_2532_ = stack[10].m_obj;
lean_object* v___y_2533_ = stack[11].m_obj;
lean_object* v_res_2536_;
v_res_2536_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(v_mvarId_2522_, v_val_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
stack->m_obj
 = v_res_2536_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___boxed(lean_object* v_mvarId_2537_, lean_object* v_val_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(v_mvarId_2537_, v_val_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec(v___y_2539_);
return v_res_2550_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v___x_2562_; 
v___x_2562_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_2560_);
return v___x_2562_;
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2551_ = stack[0].m_obj;
lean_object* v___y_2552_ = stack[1].m_obj;
lean_object* v___y_2553_ = stack[2].m_obj;
lean_object* v___y_2554_ = stack[3].m_obj;
lean_object* v___y_2555_ = stack[4].m_obj;
lean_object* v___y_2556_ = stack[5].m_obj;
lean_object* v___y_2557_ = stack[6].m_obj;
lean_object* v___y_2558_ = stack[7].m_obj;
lean_object* v___y_2559_ = stack[8].m_obj;
lean_object* v___y_2560_ = stack[9].m_obj;
lean_object* v_res_2563_;
v_res_2563_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
stack->m_obj
 = v_res_2563_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___boxed(lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec(v___y_2564_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1(lean_object* v_00_u03b2_2576_, lean_object* v_x_2577_, lean_object* v_x_2578_, lean_object* v_x_2579_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_x_2577_, v_x_2578_, v_x_2579_);
return v___x_2580_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2581_, lean_object* v_x_2582_, size_t v_x_2583_, size_t v_x_2584_, lean_object* v_x_2585_, lean_object* v_x_2586_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_2582_, v_x_2583_, v_x_2584_, v_x_2585_, v_x_2586_);
return v___x_2587_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2582_ = stack[1].m_obj;
size_t v_x_2583_ = stack[2].m_num;
size_t v_x_2584_ = stack[3].m_num;
lean_object* v_x_2585_ = stack[4].m_obj;
lean_object* v_x_2586_ = stack[5].m_obj;
lean_object* v_res_2588_;
v_res_2588_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(lean_box(0), v_x_2582_, v_x_2583_, v_x_2584_, v_x_2585_, v_x_2586_);
stack->m_obj
 = v_res_2588_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2589_, lean_object* v_x_2590_, lean_object* v_x_2591_, lean_object* v_x_2592_, lean_object* v_x_2593_, lean_object* v_x_2594_){
_start:
{
size_t v_x_154772__boxed_2595_; size_t v_x_154773__boxed_2596_; lean_object* v_res_2597_; 
v_x_154772__boxed_2595_ = lean_unbox_usize(v_x_2591_);
lean_dec(v_x_2591_);
v_x_154773__boxed_2596_ = lean_unbox_usize(v_x_2592_);
lean_dec(v_x_2592_);
v_res_2597_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(v_00_u03b2_2589_, v_x_2590_, v_x_154772__boxed_2595_, v_x_154773__boxed_2596_, v_x_2593_, v_x_2594_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_2598_, lean_object* v_n_2599_, lean_object* v_k_2600_, lean_object* v_v_2601_){
_start:
{
lean_object* v___x_2602_; 
v___x_2602_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(v_n_2599_, v_k_2600_, v_v_2601_);
return v___x_2602_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2603_, size_t v_depth_2604_, lean_object* v_keys_2605_, lean_object* v_vals_2606_, lean_object* v_heq_2607_, lean_object* v_i_2608_, lean_object* v_entries_2609_){
_start:
{
lean_object* v___x_2610_; 
v___x_2610_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_2604_, v_keys_2605_, v_vals_2606_, v_i_2608_, v_entries_2609_);
return v___x_2610_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2604_ = stack[1].m_num;
lean_object* v_keys_2605_ = stack[2].m_obj;
lean_object* v_vals_2606_ = stack[3].m_obj;
lean_object* v_i_2608_ = stack[5].m_obj;
lean_object* v_entries_2609_ = stack[6].m_obj;
lean_object* v_res_2611_;
v_res_2611_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(lean_box(0), v_depth_2604_, v_keys_2605_, v_vals_2606_, lean_box(0), v_i_2608_, v_entries_2609_);
stack->m_obj
 = v_res_2611_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2612_, lean_object* v_depth_2613_, lean_object* v_keys_2614_, lean_object* v_vals_2615_, lean_object* v_heq_2616_, lean_object* v_i_2617_, lean_object* v_entries_2618_){
_start:
{
size_t v_depth_boxed_2619_; lean_object* v_res_2620_; 
v_depth_boxed_2619_ = lean_unbox_usize(v_depth_2613_);
lean_dec(v_depth_2613_);
v_res_2620_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(v_00_u03b2_2612_, v_depth_boxed_2619_, v_keys_2614_, v_vals_2615_, v_heq_2616_, v_i_2617_, v_entries_2618_);
lean_dec_ref(v_vals_2615_);
lean_dec_ref(v_keys_2614_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_2621_, lean_object* v_x_2622_, lean_object* v_x_2623_, lean_object* v_x_2624_, lean_object* v_x_2625_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_x_2622_, v_x_2623_, v_x_2624_, v_x_2625_);
return v___x_2626_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(lean_object* v_type_2627_, lean_object* v_a_2628_){
_start:
{
lean_object* v___x_2630_; 
v___x_2630_ = l_Lean_Expr_getAppFn(v_type_2627_);
if (lean_obj_tag(v___x_2630_) == 4)
{
lean_object* v_declName_2631_; lean_object* v___x_2632_; 
v_declName_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_declName_2631_);
lean_dec_ref_known(v___x_2630_, 2);
v___x_2632_ = l_Lean_Meta_Grind_isEagerSplit___redArg(v_declName_2631_, v_a_2628_);
lean_dec(v_declName_2631_);
return v___x_2632_;
}
else
{
uint8_t v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_dec_ref(v___x_2630_);
v___x_2633_ = 0;
v___x_2634_ = lean_box(v___x_2633_);
v___x_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2634_);
return v___x_2635_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2627_ = stack[0].m_obj;
lean_object* v_a_2628_ = stack[1].m_obj;
lean_object* v_res_2636_;
v_res_2636_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_2627_, v_a_2628_);
stack->m_obj
 = v_res_2636_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg___boxed(lean_object* v_type_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_2637_, v_a_2638_);
lean_dec_ref(v_a_2638_);
lean_dec_ref(v_type_2637_);
return v_res_2640_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(lean_object* v_type_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_){
_start:
{
lean_object* v___x_2652_; 
v___x_2652_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_2641_, v_a_2643_);
return v___x_2652_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2641_ = stack[0].m_obj;
lean_object* v_a_2642_ = stack[1].m_obj;
lean_object* v_a_2643_ = stack[2].m_obj;
lean_object* v_a_2644_ = stack[3].m_obj;
lean_object* v_a_2645_ = stack[4].m_obj;
lean_object* v_a_2646_ = stack[5].m_obj;
lean_object* v_a_2647_ = stack[6].m_obj;
lean_object* v_a_2648_ = stack[7].m_obj;
lean_object* v_a_2649_ = stack[8].m_obj;
lean_object* v_a_2650_ = stack[9].m_obj;
lean_object* v_res_2653_;
v_res_2653_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(v_type_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_);
stack->m_obj
 = v_res_2653_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___boxed(lean_object* v_type_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(v_type_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_);
lean_dec(v_a_2663_);
lean_dec_ref(v_a_2662_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_type_2654_);
return v_res_2665_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2666_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2667_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2667_);
return v___x_2668_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2669_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2670_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_2671_ = lean_unsigned_to_nat(0u);
v___x_2672_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2671_);
lean_ctor_set(v___x_2672_, 1, v___x_2671_);
lean_ctor_set(v___x_2672_, 2, v___x_2671_);
lean_ctor_set(v___x_2672_, 3, v___x_2671_);
lean_ctor_set(v___x_2672_, 4, v___x_2670_);
lean_ctor_set(v___x_2672_, 5, v___x_2670_);
lean_ctor_set(v___x_2672_, 6, v___x_2670_);
lean_ctor_set(v___x_2672_, 7, v___x_2670_);
lean_ctor_set(v___x_2672_, 8, v___x_2670_);
lean_ctor_set(v___x_2672_, 9, v___x_2670_);
lean_ctor_set(v___x_2672_, 10, v___x_2670_);
lean_ctor_set(v___x_2672_, 11, v___x_2669_);
return v___x_2672_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2673_ = lean_unsigned_to_nat(32u);
v___x_2674_ = lean_mk_empty_array_with_capacity(v___x_2673_);
v___x_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2674_);
return v___x_2675_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2676_ = ((size_t)5ULL);
v___x_2677_ = lean_unsigned_to_nat(0u);
v___x_2678_ = lean_unsigned_to_nat(32u);
v___x_2679_ = lean_mk_empty_array_with_capacity(v___x_2678_);
v___x_2680_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_2681_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
lean_ctor_set(v___x_2681_, 1, v___x_2679_);
lean_ctor_set(v___x_2681_, 2, v___x_2677_);
lean_ctor_set(v___x_2681_, 3, v___x_2677_);
lean_ctor_set_usize(v___x_2681_, 4, v___x_2676_);
return v___x_2681_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2682_ = lean_box(1);
v___x_2683_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_2684_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_2685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
lean_ctor_set(v___x_2685_, 1, v___x_2683_);
lean_ctor_set(v___x_2685_, 2, v___x_2682_);
return v___x_2685_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2687_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_2688_ = l_Lean_stringToMessageData(v___x_2687_);
return v___x_2688_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2690_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_2691_ = l_Lean_stringToMessageData(v___x_2690_);
return v___x_2691_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2693_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_2694_ = l_Lean_stringToMessageData(v___x_2693_);
return v___x_2694_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2696_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_2697_ = l_Lean_stringToMessageData(v___x_2696_);
return v___x_2697_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_2700_ = l_Lean_stringToMessageData(v___x_2699_);
return v___x_2700_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2702_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_2703_ = l_Lean_stringToMessageData(v___x_2702_);
return v___x_2703_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2705_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_2706_ = l_Lean_stringToMessageData(v___x_2705_);
return v___x_2706_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21(void){
_start:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2708_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__20));
v___x_2709_ = l_Lean_stringToMessageData(v___x_2708_);
return v___x_2709_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23(void){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__22));
v___x_2712_ = l_Lean_stringToMessageData(v___x_2711_);
return v___x_2712_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25(void){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2714_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__24));
v___x_2715_ = l_Lean_stringToMessageData(v___x_2714_);
return v___x_2715_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27(void){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__26));
v___x_2718_ = l_Lean_stringToMessageData(v___x_2717_);
return v___x_2718_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_2719_, lean_object* v_declHint_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v_env_2725_; uint8_t v___x_2726_; 
v___x_2723_ = lean_box(0);
v___x_2724_ = lean_st_ref_get(v___y_2721_);
v_env_2725_ = lean_ctor_get(v___x_2724_, 0);
lean_inc_ref(v_env_2725_);
lean_dec(v___x_2724_);
v___x_2726_ = l_Lean_Name_isAnonymous(v_declHint_2720_);
if (v___x_2726_ == 0)
{
uint8_t v_isExporting_2727_; 
v_isExporting_2727_ = lean_ctor_get_uint8(v_env_2725_, sizeof(void*)*13);
if (v_isExporting_2727_ == 0)
{
lean_object* v___x_2728_; 
lean_dec_ref(v_env_2725_);
lean_dec(v_declHint_2720_);
v___x_2728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2728_, 0, v_msg_2719_);
return v___x_2728_;
}
else
{
lean_object* v___x_2729_; uint8_t v___x_2730_; 
lean_inc_ref(v_env_2725_);
v___x_2729_ = l_Lean_Environment_setExporting(v_env_2725_, v___x_2726_);
lean_inc(v_declHint_2720_);
lean_inc_ref(v___x_2729_);
v___x_2730_ = l_Lean_Environment_contains(v___x_2729_, v_declHint_2720_, v_isExporting_2727_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2731_; 
lean_dec_ref(v___x_2729_);
lean_dec_ref(v_env_2725_);
lean_dec(v_declHint_2720_);
v___x_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2731_, 0, v_msg_2719_);
return v___x_2731_;
}
else
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v_c_2737_; lean_object* v___x_2738_; 
v___x_2732_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_2733_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_2734_ = l_Lean_Options_empty;
v___x_2735_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2729_);
lean_ctor_set(v___x_2735_, 1, v___x_2732_);
lean_ctor_set(v___x_2735_, 2, v___x_2733_);
lean_ctor_set(v___x_2735_, 3, v___x_2734_);
lean_inc(v_declHint_2720_);
v___x_2736_ = l_Lean_MessageData_ofConstName(v_declHint_2720_, v___x_2726_);
v_c_2737_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2737_, 0, v___x_2735_);
lean_ctor_set(v_c_2737_, 1, v___x_2736_);
v___x_2738_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2725_, v_declHint_2720_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
lean_dec_ref(v_env_2725_);
lean_dec(v_declHint_2720_);
v___x_2739_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_2740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2739_);
lean_ctor_set(v___x_2740_, 1, v_c_2737_);
v___x_2741_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_2742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2740_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v___x_2743_ = l_Lean_MessageData_note(v___x_2742_);
v___x_2744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2744_, 0, v_msg_2719_);
lean_ctor_set(v___x_2744_, 1, v___x_2743_);
v___x_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
return v___x_2745_;
}
else
{
lean_object* v_val_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2802_; 
v_val_2746_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2748_ = v___x_2738_;
v_isShared_2749_ = v_isSharedCheck_2802_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_val_2746_);
lean_dec(v___x_2738_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2802_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2750_; lean_object* v_modules_2751_; lean_object* v_moduleNames_2752_; lean_object* v_mod_2753_; uint8_t v___y_2755_; uint8_t v___x_2785_; 
v___x_2750_ = l_Lean_Environment_header(v_env_2725_);
lean_dec_ref(v_env_2725_);
v_modules_2751_ = lean_ctor_get(v___x_2750_, 3);
lean_inc_ref(v_modules_2751_);
v_moduleNames_2752_ = lean_ctor_get(v___x_2750_, 4);
lean_inc_ref(v_moduleNames_2752_);
lean_dec_ref(v___x_2750_);
v_mod_2753_ = lean_array_get(v___x_2723_, v_moduleNames_2752_, v_val_2746_);
lean_dec_ref(v_moduleNames_2752_);
v___x_2785_ = l_Lean_isPrivateName(v_declHint_2720_);
lean_dec(v_declHint_2720_);
if (v___x_2785_ == 0)
{
lean_object* v___x_2786_; uint8_t v___x_2787_; 
v___x_2786_ = lean_array_get_size(v_modules_2751_);
v___x_2787_ = lean_nat_dec_lt(v_val_2746_, v___x_2786_);
if (v___x_2787_ == 0)
{
lean_dec_ref(v_modules_2751_);
lean_dec(v_val_2746_);
v___y_2755_ = v___x_2785_;
goto v___jp_2754_;
}
else
{
lean_object* v___x_2788_; lean_object* v_toImport_2789_; uint8_t v_isExported_2790_; 
v___x_2788_ = lean_array_fget(v_modules_2751_, v_val_2746_);
lean_dec(v_val_2746_);
lean_dec_ref(v_modules_2751_);
v_toImport_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc_ref(v_toImport_2789_);
lean_dec(v___x_2788_);
v_isExported_2790_ = lean_ctor_get_uint8(v_toImport_2789_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_2789_);
v___y_2755_ = v_isExported_2790_;
goto v___jp_2754_;
}
}
else
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
lean_dec_ref(v_modules_2751_);
lean_del_object(v___x_2748_);
lean_dec(v_val_2746_);
v___x_2791_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_2792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2791_);
lean_ctor_set(v___x_2792_, 1, v_c_2737_);
v___x_2793_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25);
v___x_2794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2792_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
v___x_2795_ = l_Lean_MessageData_ofName(v_mod_2753_);
v___x_2796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2794_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
v___x_2797_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27);
v___x_2798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2796_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
v___x_2799_ = l_Lean_MessageData_note(v___x_2798_);
v___x_2800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2800_, 0, v_msg_2719_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
v___x_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
return v___x_2801_;
}
v___jp_2754_:
{
if (v___y_2755_ == 0)
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2767_; 
v___x_2756_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_2757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2756_);
lean_ctor_set(v___x_2757_, 1, v_c_2737_);
v___x_2758_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_2759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2757_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
v___x_2760_ = l_Lean_MessageData_ofName(v_mod_2753_);
v___x_2761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2759_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
v___x_2762_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_2763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2761_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = l_Lean_MessageData_note(v___x_2763_);
v___x_2765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2765_, 0, v_msg_2719_);
lean_ctor_set(v___x_2765_, 1, v___x_2764_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set_tag(v___x_2748_, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2765_);
v___x_2767_ = v___x_2748_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v___x_2765_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
else
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2783_; 
v___x_2769_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_2770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2769_);
lean_ctor_set(v___x_2770_, 1, v_c_2737_);
v___x_2771_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_2772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2770_);
lean_ctor_set(v___x_2772_, 1, v___x_2771_);
v___x_2773_ = l_Lean_MessageData_ofName(v_mod_2753_);
lean_inc_ref(v___x_2773_);
v___x_2774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2772_);
lean_ctor_set(v___x_2774_, 1, v___x_2773_);
v___x_2775_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21);
v___x_2776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2774_);
lean_ctor_set(v___x_2776_, 1, v___x_2775_);
v___x_2777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2776_);
lean_ctor_set(v___x_2777_, 1, v___x_2773_);
v___x_2778_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23);
v___x_2779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2777_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
v___x_2780_ = l_Lean_MessageData_note(v___x_2779_);
v___x_2781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2781_, 0, v_msg_2719_);
lean_ctor_set(v___x_2781_, 1, v___x_2780_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set_tag(v___x_2748_, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2781_);
v___x_2783_ = v___x_2748_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2781_);
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
}
}
}
}
else
{
lean_object* v___x_2803_; 
lean_dec_ref(v_env_2725_);
lean_dec(v_declHint_2720_);
v___x_2803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2803_, 0, v_msg_2719_);
return v___x_2803_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2719_ = stack[0].m_obj;
lean_object* v_declHint_2720_ = stack[1].m_obj;
lean_object* v___y_2721_ = stack[2].m_obj;
lean_object* v_res_2804_;
v_res_2804_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2719_, v_declHint_2720_, v___y_2721_);
stack->m_obj
 = v_res_2804_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_2805_, lean_object* v_declHint_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2805_, v_declHint_2806_, v___y_2807_);
lean_dec(v___y_2807_);
return v_res_2809_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_2810_, lean_object* v_declHint_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v___x_2815_; lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2825_; 
v___x_2815_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2810_, v_declHint_2811_, v___y_2813_);
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2818_ = v___x_2815_;
v_isShared_2819_ = v_isSharedCheck_2825_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2815_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2825_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2823_; 
v___x_2820_ = l_Lean_unknownIdentifierMessageTag;
v___x_2821_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2820_);
lean_ctor_set(v___x_2821_, 1, v_a_2816_);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v___x_2821_);
v___x_2823_ = v___x_2818_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v___x_2821_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2810_ = stack[0].m_obj;
lean_object* v_declHint_2811_ = stack[1].m_obj;
lean_object* v___y_2812_ = stack[2].m_obj;
lean_object* v___y_2813_ = stack[3].m_obj;
lean_object* v_res_2826_;
v_res_2826_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2810_, v_declHint_2811_, v___y_2812_, v___y_2813_);
stack->m_obj
 = v_res_2826_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_2827_, lean_object* v_declHint_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2827_, v_declHint_2828_, v___y_2829_, v___y_2830_);
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
return v_res_2832_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msgData_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v___x_2837_; lean_object* v_toCold_2838_; lean_object* v_env_2839_; lean_object* v_options_2840_; uint8_t v___x_2841_; lean_object* v_env_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2837_ = lean_st_ref_get(v___y_2835_);
v_toCold_2838_ = lean_ctor_get(v___y_2834_, 0);
v_env_2839_ = lean_ctor_get(v___x_2837_, 0);
lean_inc_ref(v_env_2839_);
lean_dec(v___x_2837_);
v_options_2840_ = lean_ctor_get(v_toCold_2838_, 2);
v___x_2841_ = 0;
v_env_2842_ = l_Lean_Environment_setRecordingDeps(v_env_2839_, v___x_2841_);
v___x_2843_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_2844_ = lean_unsigned_to_nat(32u);
v___x_2845_ = lean_mk_empty_array_with_capacity(v___x_2844_);
lean_dec_ref(v___x_2845_);
v___x_2846_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
lean_inc_ref(v_options_2840_);
v___x_2847_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2847_, 0, v_env_2842_);
lean_ctor_set(v___x_2847_, 1, v___x_2843_);
lean_ctor_set(v___x_2847_, 2, v___x_2846_);
lean_ctor_set(v___x_2847_, 3, v_options_2840_);
v___x_2848_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
lean_ctor_set(v___x_2848_, 1, v_msgData_2833_);
v___x_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
return v___x_2849_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2833_ = stack[0].m_obj;
lean_object* v___y_2834_ = stack[1].m_obj;
lean_object* v___y_2835_ = stack[2].m_obj;
lean_object* v_res_2850_;
v_res_2850_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_2833_, v___y_2834_, v___y_2835_);
stack->m_obj
 = v_res_2850_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msgData_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_2851_, v___y_2852_, v___y_2853_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
return v_res_2855_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_msg_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v_ref_2860_; lean_object* v___x_2861_; lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2870_; 
v_ref_2860_ = lean_ctor_get(v___y_2857_, 2);
v___x_2861_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_2856_, v___y_2857_, v___y_2858_);
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2864_ = v___x_2861_;
v_isShared_2865_ = v_isSharedCheck_2870_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2861_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2870_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2866_; lean_object* v___x_2868_; 
lean_inc(v_ref_2860_);
v___x_2866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2866_, 0, v_ref_2860_);
lean_ctor_set(v___x_2866_, 1, v_a_2862_);
if (v_isShared_2865_ == 0)
{
lean_ctor_set_tag(v___x_2864_, 1);
lean_ctor_set(v___x_2864_, 0, v___x_2866_);
v___x_2868_ = v___x_2864_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___x_2866_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2856_ = stack[0].m_obj;
lean_object* v___y_2857_ = stack[1].m_obj;
lean_object* v___y_2858_ = stack[2].m_obj;
lean_object* v_res_2871_;
v_res_2871_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2856_, v___y_2857_, v___y_2858_);
stack->m_obj
 = v_res_2871_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_msg_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
return v_res_2876_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_2877_, lean_object* v_msg_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v_toCold_2882_; lean_object* v_currRecDepth_2883_; lean_object* v_ref_2884_; uint16_t v_optionFlags_2885_; uint8_t v_suppressElabErrors_2886_; uint8_t v_isRecordingDeps_2887_; lean_object* v_ref_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v_toCold_2882_ = lean_ctor_get(v___y_2879_, 0);
v_currRecDepth_2883_ = lean_ctor_get(v___y_2879_, 1);
v_ref_2884_ = lean_ctor_get(v___y_2879_, 2);
v_optionFlags_2885_ = lean_ctor_get_uint16(v___y_2879_, sizeof(void*)*3);
v_suppressElabErrors_2886_ = lean_ctor_get_uint8(v___y_2879_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2887_ = lean_ctor_get_uint8(v___y_2879_, sizeof(void*)*3 + 3);
v_ref_2888_ = l_Lean_replaceRef(v_ref_2877_, v_ref_2884_);
lean_inc(v_currRecDepth_2883_);
lean_inc_ref(v_toCold_2882_);
v___x_2889_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2889_, 0, v_toCold_2882_);
lean_ctor_set(v___x_2889_, 1, v_currRecDepth_2883_);
lean_ctor_set(v___x_2889_, 2, v_ref_2888_);
lean_ctor_set_uint16(v___x_2889_, sizeof(void*)*3, v_optionFlags_2885_);
lean_ctor_set_uint8(v___x_2889_, sizeof(void*)*3 + 2, v_suppressElabErrors_2886_);
lean_ctor_set_uint8(v___x_2889_, sizeof(void*)*3 + 3, v_isRecordingDeps_2887_);
v___x_2890_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2878_, v___x_2889_, v___y_2880_);
lean_dec_ref_known(v___x_2889_, 3);
return v___x_2890_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2877_ = stack[0].m_obj;
lean_object* v_msg_2878_ = stack[1].m_obj;
lean_object* v___y_2879_ = stack[2].m_obj;
lean_object* v___y_2880_ = stack[3].m_obj;
lean_object* v_res_2891_;
v_res_2891_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2877_, v_msg_2878_, v___y_2879_, v___y_2880_);
stack->m_obj
 = v_res_2891_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_2892_, lean_object* v_msg_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2892_, v_msg_2893_, v___y_2894_, v___y_2895_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v_ref_2892_);
return v_res_2897_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_2898_, lean_object* v_msg_2899_, lean_object* v_declHint_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v___x_2904_; lean_object* v_a_2905_; lean_object* v___x_2906_; 
v___x_2904_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2899_, v_declHint_2900_, v___y_2901_, v___y_2902_);
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_a_2905_);
lean_dec_ref(v___x_2904_);
v___x_2906_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2898_, v_a_2905_, v___y_2901_, v___y_2902_);
return v___x_2906_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2898_ = stack[0].m_obj;
lean_object* v_msg_2899_ = stack[1].m_obj;
lean_object* v_declHint_2900_ = stack[2].m_obj;
lean_object* v___y_2901_ = stack[3].m_obj;
lean_object* v___y_2902_ = stack[4].m_obj;
lean_object* v_res_2907_;
v_res_2907_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2898_, v_msg_2899_, v_declHint_2900_, v___y_2901_, v___y_2902_);
stack->m_obj
 = v_res_2907_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_2908_, lean_object* v_msg_2909_, lean_object* v_declHint_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2908_, v_msg_2909_, v_declHint_2910_, v___y_2911_, v___y_2912_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v_ref_2908_);
return v_res_2914_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2917_ = l_Lean_stringToMessageData(v___x_2916_);
return v___x_2917_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_2920_ = l_Lean_stringToMessageData(v___x_2919_);
return v___x_2920_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2921_, lean_object* v_constName_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v___x_2926_; uint8_t v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2926_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2927_ = 0;
lean_inc(v_constName_2922_);
v___x_2928_ = l_Lean_MessageData_ofConstName(v_constName_2922_, v___x_2927_);
v___x_2929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2926_);
lean_ctor_set(v___x_2929_, 1, v___x_2928_);
v___x_2930_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_2931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2929_);
lean_ctor_set(v___x_2931_, 1, v___x_2930_);
v___x_2932_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2921_, v___x_2931_, v_constName_2922_, v___y_2923_, v___y_2924_);
return v___x_2932_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2921_ = stack[0].m_obj;
lean_object* v_constName_2922_ = stack[1].m_obj;
lean_object* v___y_2923_ = stack[2].m_obj;
lean_object* v___y_2924_ = stack[3].m_obj;
lean_object* v_res_2933_;
v_res_2933_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_2921_, v_constName_2922_, v___y_2923_, v___y_2924_);
stack->m_obj
 = v_res_2933_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2934_, lean_object* v_constName_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_2934_, v_constName_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v_ref_2934_);
return v_res_2939_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(lean_object* v_constName_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v_ref_2944_; lean_object* v___x_2945_; 
v_ref_2944_ = lean_ctor_get(v___y_2941_, 2);
v___x_2945_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_2944_, v_constName_2940_, v___y_2941_, v___y_2942_);
return v___x_2945_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2940_ = stack[0].m_obj;
lean_object* v___y_2941_ = stack[1].m_obj;
lean_object* v___y_2942_ = stack[2].m_obj;
lean_object* v_res_2946_;
v_res_2946_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_2940_, v___y_2941_, v___y_2942_);
stack->m_obj
 = v_res_2946_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_2947_, v___y_2948_, v___y_2949_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
return v_res_2951_;
}
}
lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(lean_object* v_constName_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
lean_object* v___x_2956_; lean_object* v_env_2957_; uint8_t v___x_2958_; lean_object* v___x_2959_; 
v___x_2956_ = lean_st_ref_get(v___y_2954_);
v_env_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc_ref(v_env_2957_);
lean_dec(v___x_2956_);
v___x_2958_ = 0;
lean_inc(v_constName_2952_);
v___x_2959_ = l_Lean_Environment_find_x3f(v_env_2957_, v_constName_2952_, v___x_2958_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v___x_2960_; 
v___x_2960_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_2952_, v___y_2953_, v___y_2954_);
return v___x_2960_;
}
else
{
lean_object* v_val_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
lean_dec(v_constName_2952_);
v_val_2961_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2959_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_val_2961_);
lean_dec(v___x_2959_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
lean_ctor_set_tag(v___x_2963_, 0);
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_val_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2952_ = stack[0].m_obj;
lean_object* v___y_2953_ = stack[1].m_obj;
lean_object* v___y_2954_ = stack[2].m_obj;
lean_object* v_res_2969_;
v_res_2969_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_constName_2952_, v___y_2953_, v___y_2954_);
stack->m_obj
 = v_res_2969_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0___boxed(lean_object* v_constName_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_constName_2970_, v___y_2971_, v___y_2972_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
return v_res_2974_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(lean_object* v_type_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = l_Lean_Expr_getAppFn(v_type_2975_);
if (lean_obj_tag(v___x_2979_) == 4)
{
lean_object* v_declName_2980_; lean_object* v___x_2981_; 
v_declName_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_declName_2980_);
lean_dec_ref_known(v___x_2979_, 2);
v___x_2981_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_declName_2980_, v_a_2976_, v_a_2977_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2999_; 
v_a_2982_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2984_ = v___x_2981_;
v_isShared_2985_ = v_isSharedCheck_2999_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2981_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2999_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
if (lean_obj_tag(v_a_2982_) == 5)
{
lean_object* v_val_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; uint8_t v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2992_; 
v_val_2986_ = lean_ctor_get(v_a_2982_, 0);
lean_inc_ref(v_val_2986_);
lean_dec_ref_known(v_a_2982_, 1);
v___x_2987_ = l_Lean_InductiveVal_numCtors(v_val_2986_);
lean_dec_ref(v_val_2986_);
v___x_2988_ = lean_unsigned_to_nat(1u);
v___x_2989_ = lean_nat_dec_le(v___x_2987_, v___x_2988_);
lean_dec(v___x_2987_);
v___x_2990_ = lean_box(v___x_2989_);
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 0, v___x_2990_);
v___x_2992_ = v___x_2984_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2990_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
else
{
uint8_t v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2997_; 
lean_dec(v_a_2982_);
v___x_2994_ = 0;
v___x_2995_ = lean_box(v___x_2994_);
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 0, v___x_2995_);
v___x_2997_ = v___x_2984_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2995_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
else
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
v_a_3000_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3002_ = v___x_2981_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2981_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_a_3000_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
}
else
{
uint8_t v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
lean_dec_ref(v___x_2979_);
v___x_3008_ = 0;
v___x_3009_ = lean_box(v___x_3008_);
v___x_3010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
return v___x_3010_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2975_ = stack[0].m_obj;
lean_object* v_a_2976_ = stack[1].m_obj;
lean_object* v_a_2977_ = stack[2].m_obj;
lean_object* v_res_3011_;
v_res_3011_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_type_2975_, v_a_2976_, v_a_2977_);
stack->m_obj
 = v_res_3011_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive___boxed(lean_object* v_type_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_type_3012_, v_a_3013_, v_a_3014_);
lean_dec(v_a_3014_);
lean_dec_ref(v_a_3013_);
lean_dec_ref(v_type_3012_);
return v_res_3016_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(lean_object* v_00_u03b1_3017_, lean_object* v_constName_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_3018_, v___y_3019_, v___y_3020_);
return v___x_3022_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_3018_ = stack[1].m_obj;
lean_object* v___y_3019_ = stack[2].m_obj;
lean_object* v___y_3020_ = stack[3].m_obj;
lean_object* v_res_3023_;
v_res_3023_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(lean_box(0), v_constName_3018_, v___y_3019_, v___y_3020_);
stack->m_obj
 = v_res_3023_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3024_, lean_object* v_constName_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(v_00_u03b1_3024_, v_constName_3025_, v___y_3026_, v___y_3027_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
return v_res_3029_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3030_, lean_object* v_ref_3031_, lean_object* v_constName_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_3031_, v_constName_3032_, v___y_3033_, v___y_3034_);
return v___x_3036_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3031_ = stack[1].m_obj;
lean_object* v_constName_3032_ = stack[2].m_obj;
lean_object* v___y_3033_ = stack[3].m_obj;
lean_object* v___y_3034_ = stack[4].m_obj;
lean_object* v_res_3037_;
v_res_3037_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(lean_box(0), v_ref_3031_, v_constName_3032_, v___y_3033_, v___y_3034_);
stack->m_obj
 = v_res_3037_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3038_, lean_object* v_ref_3039_, lean_object* v_constName_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(v_00_u03b1_3038_, v_ref_3039_, v_constName_3040_, v___y_3041_, v___y_3042_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v_ref_3039_);
return v_res_3044_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3045_, lean_object* v_ref_3046_, lean_object* v_msg_3047_, lean_object* v_declHint_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3046_, v_msg_3047_, v_declHint_3048_, v___y_3049_, v___y_3050_);
return v___x_3052_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3046_ = stack[1].m_obj;
lean_object* v_msg_3047_ = stack[2].m_obj;
lean_object* v_declHint_3048_ = stack[3].m_obj;
lean_object* v___y_3049_ = stack[4].m_obj;
lean_object* v___y_3050_ = stack[5].m_obj;
lean_object* v_res_3053_;
v_res_3053_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(lean_box(0), v_ref_3046_, v_msg_3047_, v_declHint_3048_, v___y_3049_, v___y_3050_);
stack->m_obj
 = v_res_3053_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3054_, lean_object* v_ref_3055_, lean_object* v_msg_3056_, lean_object* v_declHint_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3054_, v_ref_3055_, v_msg_3056_, v_declHint_3057_, v___y_3058_, v___y_3059_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v_ref_3055_);
return v_res_3061_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_3062_, lean_object* v_declHint_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
lean_object* v___x_3067_; 
v___x_3067_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_3062_, v_declHint_3063_, v___y_3065_);
return v___x_3067_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3062_ = stack[0].m_obj;
lean_object* v_declHint_3063_ = stack[1].m_obj;
lean_object* v___y_3064_ = stack[2].m_obj;
lean_object* v___y_3065_ = stack[3].m_obj;
lean_object* v_res_3068_;
v_res_3068_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_3062_, v_declHint_3063_, v___y_3064_, v___y_3065_);
stack->m_obj
 = v_res_3068_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_3069_, lean_object* v_declHint_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_3069_, v_declHint_3070_, v___y_3071_, v___y_3072_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
return v_res_3074_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_3075_, lean_object* v_ref_3076_, lean_object* v_msg_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
lean_object* v___x_3081_; 
v___x_3081_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3076_, v_msg_3077_, v___y_3078_, v___y_3079_);
return v___x_3081_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3076_ = stack[1].m_obj;
lean_object* v_msg_3077_ = stack[2].m_obj;
lean_object* v___y_3078_ = stack[3].m_obj;
lean_object* v___y_3079_ = stack[4].m_obj;
lean_object* v_res_3082_;
v_res_3082_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(lean_box(0), v_ref_3076_, v_msg_3077_, v___y_3078_, v___y_3079_);
stack->m_obj
 = v_res_3082_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_3083_, lean_object* v_ref_3084_, lean_object* v_msg_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_3083_, v_ref_3084_, v_msg_3085_, v___y_3086_, v___y_3087_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v_ref_3084_);
return v_res_3089_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_3090_, lean_object* v_msg_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v___x_3095_; 
v___x_3095_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_3091_, v___y_3092_, v___y_3093_);
return v___x_3095_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3091_ = stack[1].m_obj;
lean_object* v___y_3092_ = stack[2].m_obj;
lean_object* v___y_3093_ = stack[3].m_obj;
lean_object* v_res_3096_;
v_res_3096_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_box(0), v_msg_3091_, v___y_3092_, v___y_3093_);
stack->m_obj
 = v_res_3096_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_3097_, lean_object* v_msg_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_3097_, v_msg_3098_, v___y_3099_, v___y_3100_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
return v_res_3102_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(lean_object* v_goal_3103_, lean_object* v_fvarId_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_){
_start:
{
lean_object* v_toGoalState_3110_; lean_object* v_mvarId_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3147_; 
v_toGoalState_3110_ = lean_ctor_get(v_goal_3103_, 0);
v_mvarId_3111_ = lean_ctor_get(v_goal_3103_, 1);
v_isSharedCheck_3147_ = !lean_is_exclusive(v_goal_3103_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3113_ = v_goal_3103_;
v_isShared_3114_ = v_isSharedCheck_3147_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_mvarId_3111_);
lean_inc(v_toGoalState_3110_);
lean_dec(v_goal_3103_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3147_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3115_; 
v___x_3115_ = l_Lean_Meta_Grind_injection_x3f(v_mvarId_3111_, v_fvarId_3104_, v_a_3105_, v_a_3106_, v_a_3107_, v_a_3108_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3138_; 
v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3118_ = v___x_3115_;
v_isShared_3119_ = v_isSharedCheck_3138_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3115_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3138_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
if (lean_obj_tag(v_a_3116_) == 1)
{
lean_object* v_val_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3133_; 
v_val_3120_ = lean_ctor_get(v_a_3116_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v_a_3116_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3122_ = v_a_3116_;
v_isShared_3123_ = v_isSharedCheck_3133_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_val_3120_);
lean_dec(v_a_3116_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3133_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 1, v_val_3120_);
v___x_3125_ = v___x_3113_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_toGoalState_3110_);
lean_ctor_set(v_reuseFailAlloc_3132_, 1, v_val_3120_);
v___x_3125_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
lean_object* v___x_3127_; 
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 0, v___x_3125_);
v___x_3127_ = v___x_3122_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3125_);
v___x_3127_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
lean_object* v___x_3129_; 
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 0, v___x_3127_);
v___x_3129_ = v___x_3118_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v___x_3127_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
}
else
{
lean_object* v___x_3134_; lean_object* v___x_3136_; 
lean_dec(v_a_3116_);
lean_del_object(v___x_3113_);
lean_dec_ref(v_toGoalState_3110_);
v___x_3134_ = lean_box(0);
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 0, v___x_3134_);
v___x_3136_ = v___x_3118_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3134_);
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
lean_del_object(v___x_3113_);
lean_dec_ref(v_toGoalState_3110_);
v_a_3139_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3115_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3115_);
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
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_3103_ = stack[0].m_obj;
lean_object* v_fvarId_3104_ = stack[1].m_obj;
lean_object* v_a_3105_ = stack[2].m_obj;
lean_object* v_a_3106_ = stack[3].m_obj;
lean_object* v_a_3107_ = stack[4].m_obj;
lean_object* v_a_3108_ = stack[5].m_obj;
lean_object* v_res_3148_;
v_res_3148_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_3103_, v_fvarId_3104_, v_a_3105_, v_a_3106_, v_a_3107_, v_a_3108_);
stack->m_obj
 = v_res_3148_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f___boxed(lean_object* v_goal_3149_, lean_object* v_fvarId_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_3149_, v_fvarId_3150_, v_a_3151_, v_a_3152_, v_a_3153_, v_a_3154_);
lean_dec(v_a_3154_);
lean_dec_ref(v_a_3153_);
lean_dec(v_a_3152_);
lean_dec_ref(v_a_3151_);
return v_res_3156_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(lean_object* v_mvarId_3157_, lean_object* v_x_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
lean_object* v___x_3164_; 
v___x_3164_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3157_, v_x_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3172_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3167_ = v___x_3164_;
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3164_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3170_; 
if (v_isShared_3168_ == 0)
{
v___x_3170_ = v___x_3167_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_a_3165_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
}
else
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3180_; 
v_a_3173_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3175_ = v___x_3164_;
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3164_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3178_; 
if (v_isShared_3176_ == 0)
{
v___x_3178_ = v___x_3175_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_3173_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3157_ = stack[0].m_obj;
lean_object* v_x_3158_ = stack[1].m_obj;
lean_object* v___y_3159_ = stack[2].m_obj;
lean_object* v___y_3160_ = stack[3].m_obj;
lean_object* v___y_3161_ = stack[4].m_obj;
lean_object* v___y_3162_ = stack[5].m_obj;
lean_object* v_res_3181_;
v_res_3181_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3157_, v_x_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
stack->m_obj
 = v_res_3181_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg___boxed(lean_object* v_mvarId_3182_, lean_object* v_x_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v_res_3189_; 
v_res_3189_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3182_, v_x_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
return v_res_3189_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(lean_object* v_00_u03b1_3190_, lean_object* v_mvarId_3191_, lean_object* v_x_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v___x_3198_; 
v___x_3198_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3191_, v_x_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
return v___x_3198_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3191_ = stack[1].m_obj;
lean_object* v_x_3192_ = stack[2].m_obj;
lean_object* v___y_3193_ = stack[3].m_obj;
lean_object* v___y_3194_ = stack[4].m_obj;
lean_object* v___y_3195_ = stack[5].m_obj;
lean_object* v___y_3196_ = stack[6].m_obj;
lean_object* v_res_3199_;
v_res_3199_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(lean_box(0), v_mvarId_3191_, v_x_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
stack->m_obj
 = v_res_3199_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___boxed(lean_object* v_00_u03b1_3200_, lean_object* v_mvarId_3201_, lean_object* v_x_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(v_00_u03b1_3200_, v_mvarId_3201_, v_x_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
return v_res_3208_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(lean_object* v_mvarId_3209_, lean_object* v_toGoalState_3210_, lean_object* v_goal_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
lean_object* v___x_3217_; 
lean_inc(v_mvarId_3209_);
v___x_3217_ = l_Lean_MVarId_getType(v_mvarId_3209_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3219_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3218_);
lean_dec_ref_known(v___x_3217_, 1);
v___x_3219_ = l_Lean_Meta_isProp(v_a_3218_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3246_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3222_ = v___x_3219_;
v_isShared_3223_ = v_isSharedCheck_3246_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3219_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3246_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
uint8_t v___x_3224_; 
v___x_3224_ = lean_unbox(v_a_3220_);
lean_dec(v_a_3220_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3225_; 
lean_del_object(v___x_3222_);
lean_dec_ref(v_goal_3211_);
v___x_3225_ = l_Lean_MVarId_exfalso(v_mvarId_3209_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3234_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3228_ = v___x_3225_;
v_isShared_3229_ = v_isSharedCheck_3234_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3225_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3234_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3230_; lean_object* v___x_3232_; 
v___x_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3230_, 0, v_toGoalState_3210_);
lean_ctor_set(v___x_3230_, 1, v_a_3226_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v___x_3230_);
v___x_3232_ = v___x_3228_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3230_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
else
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3242_; 
lean_dec_ref(v_toGoalState_3210_);
v_a_3235_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3237_ = v___x_3225_;
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3225_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3240_; 
if (v_isShared_3238_ == 0)
{
v___x_3240_ = v___x_3237_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3235_);
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
lean_object* v___x_3244_; 
lean_dec_ref(v_toGoalState_3210_);
lean_dec(v_mvarId_3209_);
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 0, v_goal_3211_);
v___x_3244_ = v___x_3222_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_goal_3211_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
else
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3254_; 
lean_dec_ref(v_goal_3211_);
lean_dec_ref(v_toGoalState_3210_);
lean_dec(v_mvarId_3209_);
v_a_3247_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3249_ = v___x_3219_;
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3219_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3252_; 
if (v_isShared_3250_ == 0)
{
v___x_3252_ = v___x_3249_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3247_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
}
else
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_dec_ref(v_goal_3211_);
lean_dec_ref(v_toGoalState_3210_);
lean_dec(v_mvarId_3209_);
v_a_3255_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3257_ = v___x_3217_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3217_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3209_ = stack[0].m_obj;
lean_object* v_toGoalState_3210_ = stack[1].m_obj;
lean_object* v_goal_3211_ = stack[2].m_obj;
lean_object* v___y_3212_ = stack[3].m_obj;
lean_object* v___y_3213_ = stack[4].m_obj;
lean_object* v___y_3214_ = stack[5].m_obj;
lean_object* v___y_3215_ = stack[6].m_obj;
lean_object* v_res_3263_;
v_res_3263_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(v_mvarId_3209_, v_toGoalState_3210_, v_goal_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
stack->m_obj
 = v_res_3263_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed(lean_object* v_mvarId_3264_, lean_object* v_toGoalState_3265_, lean_object* v_goal_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(v_mvarId_3264_, v_toGoalState_3265_, v_goal_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
return v_res_3272_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(lean_object* v_goal_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_){
_start:
{
lean_object* v_toGoalState_3279_; lean_object* v_mvarId_3280_; lean_object* v___f_3281_; lean_object* v___x_3282_; 
v_toGoalState_3279_ = lean_ctor_get(v_goal_3273_, 0);
lean_inc_ref(v_toGoalState_3279_);
v_mvarId_3280_ = lean_ctor_get(v_goal_3273_, 1);
lean_inc_n(v_mvarId_3280_, 2);
v___f_3281_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3281_, 0, v_mvarId_3280_);
lean_closure_set(v___f_3281_, 1, v_toGoalState_3279_);
lean_closure_set(v___f_3281_, 2, v_goal_3273_);
v___x_3282_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3280_, v___f_3281_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_);
return v___x_3282_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_3273_ = stack[0].m_obj;
lean_object* v_a_3274_ = stack[1].m_obj;
lean_object* v_a_3275_ = stack[2].m_obj;
lean_object* v_a_3276_ = stack[3].m_obj;
lean_object* v_a_3277_ = stack[4].m_obj;
lean_object* v_res_3283_;
v_res_3283_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_);
stack->m_obj
 = v_res_3283_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___boxed(lean_object* v_goal_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
return v_res_3290_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___lam__0(lean_object* v_toGoalState_3291_, lean_object* v_mvarId_3292_, lean_object* v_goal_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
lean_object* v_mvarId_3305_; lean_object* v___x_3308_; 
lean_inc(v_mvarId_3292_);
v___x_3308_ = l_Lean_MVarId_getType(v_mvarId_3292_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v_a_3309_; lean_object* v___x_3310_; 
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
lean_inc_n(v_a_3309_, 2);
lean_dec_ref_known(v___x_3308_, 1);
v___x_3310_ = l_Lean_Meta_Grind_simpCore(v_a_3309_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3342_; 
v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3313_ = v___x_3310_;
v_isShared_3314_ = v_isSharedCheck_3342_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3310_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3342_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v_expr_3315_; lean_object* v_proof_x3f_3316_; uint8_t v___x_3317_; 
v_expr_3315_ = lean_ctor_get(v_a_3311_, 0);
lean_inc_ref(v_expr_3315_);
v_proof_x3f_3316_ = lean_ctor_get(v_a_3311_, 1);
lean_inc(v_proof_x3f_3316_);
lean_dec(v_a_3311_);
v___x_3317_ = lean_expr_eqv(v_expr_3315_, v_a_3309_);
lean_dec(v_a_3309_);
if (v___x_3317_ == 0)
{
lean_del_object(v___x_3313_);
lean_dec_ref(v_goal_3293_);
if (lean_obj_tag(v_proof_x3f_3316_) == 0)
{
lean_object* v___x_3318_; 
v___x_3318_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_3292_, v_expr_3315_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3319_);
lean_dec_ref_known(v___x_3318_, 1);
v_mvarId_3305_ = v_a_3319_;
goto v___jp_3304_;
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
lean_dec_ref(v_toGoalState_3291_);
v_a_3320_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v___x_3318_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3318_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
else
{
lean_object* v_val_3328_; lean_object* v___x_3329_; 
v_val_3328_ = lean_ctor_get(v_proof_x3f_3316_, 0);
lean_inc(v_val_3328_);
lean_dec_ref_known(v_proof_x3f_3316_, 1);
v___x_3329_ = l_Lean_MVarId_replaceTargetEq(v_mvarId_3292_, v_expr_3315_, v_val_3328_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v_a_3330_; 
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_a_3330_);
lean_dec_ref_known(v___x_3329_, 1);
v_mvarId_3305_ = v_a_3330_;
goto v___jp_3304_;
}
else
{
lean_object* v_a_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3338_; 
lean_dec_ref(v_toGoalState_3291_);
v_a_3331_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3333_ = v___x_3329_;
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_a_3331_);
lean_dec(v___x_3329_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3336_; 
if (v_isShared_3334_ == 0)
{
v___x_3336_ = v___x_3333_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_a_3331_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
}
}
else
{
lean_object* v___x_3340_; 
lean_dec(v_proof_x3f_3316_);
lean_dec_ref(v_expr_3315_);
lean_dec(v_mvarId_3292_);
lean_dec_ref(v_toGoalState_3291_);
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 0, v_goal_3293_);
v___x_3340_ = v___x_3313_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_goal_3293_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
}
else
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3350_; 
lean_dec(v_a_3309_);
lean_dec_ref(v_goal_3293_);
lean_dec(v_mvarId_3292_);
lean_dec_ref(v_toGoalState_3291_);
v_a_3343_ = lean_ctor_get(v___x_3310_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3345_ = v___x_3310_;
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3310_);
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
lean_dec_ref(v_goal_3293_);
lean_dec(v_mvarId_3292_);
lean_dec_ref(v_toGoalState_3291_);
v_a_3351_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3353_ = v___x_3308_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3308_);
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
v___jp_3304_:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3306_, 0, v_toGoalState_3291_);
lean_ctor_set(v___x_3306_, 1, v_mvarId_3305_);
v___x_3307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3306_);
return v___x_3307_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toGoalState_3291_ = stack[0].m_obj;
lean_object* v_mvarId_3292_ = stack[1].m_obj;
lean_object* v_goal_3293_ = stack[2].m_obj;
lean_object* v___y_3294_ = stack[3].m_obj;
lean_object* v___y_3295_ = stack[4].m_obj;
lean_object* v___y_3296_ = stack[5].m_obj;
lean_object* v___y_3297_ = stack[6].m_obj;
lean_object* v___y_3298_ = stack[7].m_obj;
lean_object* v___y_3299_ = stack[8].m_obj;
lean_object* v___y_3300_ = stack[9].m_obj;
lean_object* v___y_3301_ = stack[10].m_obj;
lean_object* v___y_3302_ = stack[11].m_obj;
lean_object* v_res_3359_;
v_res_3359_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___lam__0(v_toGoalState_3291_, v_mvarId_3292_, v_goal_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
stack->m_obj
 = v_res_3359_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___lam__0___boxed(lean_object* v_toGoalState_3360_, lean_object* v_mvarId_3361_, lean_object* v_goal_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___lam__0(v_toGoalState_3360_, v_mvarId_3361_, v_goal_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
lean_dec(v___y_3363_);
return v_res_3373_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget(lean_object* v_goal_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_){
_start:
{
lean_object* v_toGoalState_3385_; lean_object* v_mvarId_3386_; lean_object* v___f_3387_; lean_object* v___x_3388_; 
v_toGoalState_3385_ = lean_ctor_get(v_goal_3374_, 0);
lean_inc_ref(v_toGoalState_3385_);
v_mvarId_3386_ = lean_ctor_get(v_goal_3374_, 1);
lean_inc_n(v_mvarId_3386_, 2);
v___f_3387_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___lam__0___boxed), 13, 3);
lean_closure_set(v___f_3387_, 0, v_toGoalState_3385_);
lean_closure_set(v___f_3387_, 1, v_mvarId_3386_);
lean_closure_set(v___f_3387_, 2, v_goal_3374_);
v___x_3388_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3386_, v___f_3387_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
return v___x_3388_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_3374_ = stack[0].m_obj;
lean_object* v_a_3375_ = stack[1].m_obj;
lean_object* v_a_3376_ = stack[2].m_obj;
lean_object* v_a_3377_ = stack[3].m_obj;
lean_object* v_a_3378_ = stack[4].m_obj;
lean_object* v_a_3379_ = stack[5].m_obj;
lean_object* v_a_3380_ = stack[6].m_obj;
lean_object* v_a_3381_ = stack[7].m_obj;
lean_object* v_a_3382_ = stack[8].m_obj;
lean_object* v_a_3383_ = stack[9].m_obj;
lean_object* v_res_3389_;
v_res_3389_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget(v_goal_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
stack->m_obj
 = v_res_3389_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___boxed(lean_object* v_goal_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget(v_goal_3390_, v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
lean_dec(v_a_3399_);
lean_dec_ref(v_a_3398_);
lean_dec(v_a_3397_);
lean_dec_ref(v_a_3396_);
lean_dec(v_a_3395_);
lean_dec_ref(v_a_3394_);
lean_dec(v_a_3393_);
lean_dec_ref(v_a_3392_);
lean_dec(v_a_3391_);
return v_res_3401_;
}
}
lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f(lean_object* v_goal_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_){
_start:
{
lean_object* v_mvarId_3408_; lean_object* v___x_3409_; 
v_mvarId_3408_ = lean_ctor_get(v_goal_3402_, 1);
lean_inc(v_mvarId_3408_);
lean_dec_ref(v_goal_3402_);
v___x_3409_ = l_Lean_MVarId_getDecl(v_mvarId_3408_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3419_; 
v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3412_ = v___x_3409_;
v_isShared_3413_ = v_isSharedCheck_3419_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3409_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3419_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v_lctx_3414_; lean_object* v___x_3415_; lean_object* v___x_3417_; 
v_lctx_3414_ = lean_ctor_get(v_a_3410_, 1);
lean_inc_ref(v_lctx_3414_);
lean_dec(v_a_3410_);
v___x_3415_ = l_Lean_LocalContext_lastDecl(v_lctx_3414_);
lean_dec_ref(v_lctx_3414_);
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 0, v___x_3415_);
v___x_3417_ = v___x_3412_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v___x_3415_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
else
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3427_; 
v_a_3420_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3422_ = v___x_3409_;
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3409_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3423_ == 0)
{
v___x_3425_ = v___x_3422_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_a_3420_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Goal_lastDecl_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_3402_ = stack[0].m_obj;
lean_object* v_a_3403_ = stack[1].m_obj;
lean_object* v_a_3404_ = stack[2].m_obj;
lean_object* v_a_3405_ = stack[3].m_obj;
lean_object* v_a_3406_ = stack[4].m_obj;
lean_object* v_res_3428_;
v_res_3428_ = l_Lean_Meta_Grind_Goal_lastDecl_x3f(v_goal_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_);
stack->m_obj
 = v_res_3428_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f___boxed(lean_object* v_goal_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_){
_start:
{
lean_object* v_res_3435_; 
v_res_3435_ = l_Lean_Meta_Grind_Goal_lastDecl_x3f(v_goal_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_);
lean_dec(v_a_3433_);
lean_dec_ref(v_a_3432_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
return v_res_3435_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(lean_object* v_goal_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_){
_start:
{
if (lean_obj_tag(v_a_3437_) == 0)
{
lean_object* v___x_3439_; 
v___x_3439_ = l_List_reverse___redArg(v_a_3438_);
return v___x_3439_;
}
else
{
lean_object* v_head_3440_; lean_object* v_tail_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3451_; 
v_head_3440_ = lean_ctor_get(v_a_3437_, 0);
v_tail_3441_ = lean_ctor_get(v_a_3437_, 1);
v_isSharedCheck_3451_ = !lean_is_exclusive(v_a_3437_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3443_ = v_a_3437_;
v_isShared_3444_ = v_isSharedCheck_3451_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_tail_3441_);
lean_inc(v_head_3440_);
lean_dec(v_a_3437_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3451_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v_toGoalState_3445_; lean_object* v___x_3446_; lean_object* v___x_3448_; 
v_toGoalState_3445_ = lean_ctor_get(v_goal_3436_, 0);
lean_inc_ref(v_toGoalState_3445_);
v___x_3446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3446_, 0, v_toGoalState_3445_);
lean_ctor_set(v___x_3446_, 1, v_head_3440_);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 1, v_a_3438_);
lean_ctor_set(v___x_3443_, 0, v___x_3446_);
v___x_3448_ = v___x_3443_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v___x_3446_);
lean_ctor_set(v_reuseFailAlloc_3450_, 1, v_a_3438_);
v___x_3448_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
v_a_3437_ = v_tail_3441_;
v_a_3438_ = v___x_3448_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0___boxed(lean_object* v_goal_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v_goal_3452_, v_a_3453_, v_a_3454_);
lean_dec_ref(v_goal_3452_);
return v_res_3455_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(lean_object* v_kp_3456_, lean_object* v_as_x27_3457_, lean_object* v_b_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
if (lean_obj_tag(v_as_x27_3457_) == 0)
{
lean_object* v___x_3469_; 
lean_dec_ref(v_kp_3456_);
v___x_3469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3469_, 0, v_b_3458_);
return v___x_3469_;
}
else
{
lean_object* v_head_3470_; lean_object* v_tail_3471_; lean_object* v_fst_3472_; lean_object* v_snd_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3499_; 
v_head_3470_ = lean_ctor_get(v_as_x27_3457_, 0);
v_tail_3471_ = lean_ctor_get(v_as_x27_3457_, 1);
v_fst_3472_ = lean_ctor_get(v_b_3458_, 0);
v_snd_3473_ = lean_ctor_get(v_b_3458_, 1);
v_isSharedCheck_3499_ = !lean_is_exclusive(v_b_3458_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3475_ = v_b_3458_;
v_isShared_3476_ = v_isSharedCheck_3499_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_snd_3473_);
lean_inc(v_fst_3472_);
lean_dec(v_b_3458_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3499_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3477_; 
lean_inc_ref(v_kp_3456_);
lean_inc(v___y_3467_);
lean_inc_ref(v___y_3466_);
lean_inc(v___y_3465_);
lean_inc_ref(v___y_3464_);
lean_inc(v___y_3463_);
lean_inc_ref(v___y_3462_);
lean_inc(v___y_3461_);
lean_inc_ref(v___y_3460_);
lean_inc(v___y_3459_);
lean_inc(v_head_3470_);
v___x_3477_ = lean_apply_11(v_kp_3456_, v_head_3470_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, lean_box(0));
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref_known(v___x_3477_, 1);
if (lean_obj_tag(v_a_3478_) == 0)
{
lean_object* v_seq_3479_; lean_object* v___x_3480_; lean_object* v___x_3482_; 
v_seq_3479_ = lean_ctor_get(v_a_3478_, 0);
lean_inc(v_seq_3479_);
lean_dec_ref_known(v_a_3478_, 1);
v___x_3480_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_fst_3472_, v_seq_3479_);
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 0, v___x_3480_);
v___x_3482_ = v___x_3475_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v___x_3480_);
lean_ctor_set(v_reuseFailAlloc_3484_, 1, v_snd_3473_);
v___x_3482_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
v_as_x27_3457_ = v_tail_3471_;
v_b_3458_ = v___x_3482_;
goto _start;
}
}
else
{
lean_object* v_gs_3485_; lean_object* v___x_3486_; lean_object* v___x_3488_; 
v_gs_3485_ = lean_ctor_get(v_a_3478_, 0);
lean_inc(v_gs_3485_);
lean_dec_ref_known(v_a_3478_, 1);
v___x_3486_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_snd_3473_, v_gs_3485_);
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 1, v___x_3486_);
v___x_3488_ = v___x_3475_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_fst_3472_);
lean_ctor_set(v_reuseFailAlloc_3490_, 1, v___x_3486_);
v___x_3488_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
v_as_x27_3457_ = v_tail_3471_;
v_b_3458_ = v___x_3488_;
goto _start;
}
}
}
else
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3498_; 
lean_del_object(v___x_3475_);
lean_dec(v_snd_3473_);
lean_dec(v_fst_3472_);
lean_dec_ref(v_kp_3456_);
v_a_3491_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3493_ = v___x_3477_;
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3477_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3496_; 
if (v_isShared_3494_ == 0)
{
v___x_3496_ = v___x_3493_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3491_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_kp_3456_ = stack[0].m_obj;
lean_object* v_as_x27_3457_ = stack[1].m_obj;
lean_object* v_b_3458_ = stack[2].m_obj;
lean_object* v___y_3459_ = stack[3].m_obj;
lean_object* v___y_3460_ = stack[4].m_obj;
lean_object* v___y_3461_ = stack[5].m_obj;
lean_object* v___y_3462_ = stack[6].m_obj;
lean_object* v___y_3463_ = stack[7].m_obj;
lean_object* v___y_3464_ = stack[8].m_obj;
lean_object* v___y_3465_ = stack[9].m_obj;
lean_object* v___y_3466_ = stack[10].m_obj;
lean_object* v___y_3467_ = stack[11].m_obj;
lean_object* v_res_3500_;
v_res_3500_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3456_, v_as_x27_3457_, v_b_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_);
stack->m_obj
 = v_res_3500_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg___boxed(lean_object* v_kp_3501_, lean_object* v_as_x27_3502_, lean_object* v_b_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
lean_object* v_res_3514_; 
v_res_3514_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3501_, v_as_x27_3502_, v_b_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec(v_as_x27_3502_);
return v_res_3514_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(lean_object* v_fvarId_3519_, lean_object* v_mvarId_3520_, lean_object* v_goal_3521_, lean_object* v_kp_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_){
_start:
{
lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___x_3588_; 
lean_inc(v_fvarId_3519_);
v___x_3588_ = l_Lean_FVarId_getType___redArg(v_fvarId_3519_, v___y_3528_, v___y_3530_, v___y_3531_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_a_3589_; lean_object* v___x_3590_; 
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_a_3589_);
lean_dec_ref_known(v___x_3588_, 1);
lean_inc(v___y_3531_);
lean_inc_ref(v___y_3530_);
lean_inc(v___y_3529_);
lean_inc_ref(v___y_3528_);
v___x_3590_ = lean_whnf(v_a_3589_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v_a_3591_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___x_3613_; 
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
lean_inc(v_a_3591_);
lean_dec_ref_known(v___x_3590_, 1);
v___x_3613_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_a_3591_, v___y_3524_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3653_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3616_ = v___x_3613_;
v_isShared_3617_ = v_isSharedCheck_3653_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3613_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3653_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
uint8_t v___x_3618_; 
v___x_3618_ = lean_unbox(v_a_3614_);
lean_dec(v_a_3614_);
if (v___x_3618_ == 0)
{
lean_object* v___x_3619_; lean_object* v___x_3621_; 
lean_dec(v_a_3591_);
lean_dec_ref(v_kp_3522_);
lean_dec(v_mvarId_3520_);
lean_dec(v_fvarId_3519_);
v___x_3619_ = lean_box(0);
if (v_isShared_3617_ == 0)
{
lean_ctor_set(v___x_3616_, 0, v___x_3619_);
v___x_3621_ = v___x_3616_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3619_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
else
{
lean_object* v___x_3623_; 
lean_del_object(v___x_3616_);
v___x_3623_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3524_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_a_3624_; uint8_t v___x_3625_; 
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
lean_inc(v_a_3624_);
lean_dec_ref_known(v___x_3623_, 1);
v___x_3625_ = lean_unbox(v_a_3624_);
lean_dec(v_a_3624_);
if (v___x_3625_ == 0)
{
v___y_3593_ = v___y_3523_;
v___y_3594_ = v___y_3524_;
v___y_3595_ = v___y_3525_;
v___y_3596_ = v___y_3526_;
v___y_3597_ = v___y_3527_;
v___y_3598_ = v___y_3528_;
v___y_3599_ = v___y_3529_;
v___y_3600_ = v___y_3530_;
v___y_3601_ = v___y_3531_;
goto v___jp_3592_;
}
else
{
lean_object* v___x_3626_; 
v___x_3626_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_a_3591_, v___y_3530_, v___y_3531_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3636_; 
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3629_ = v___x_3626_;
v_isShared_3630_ = v_isSharedCheck_3636_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3626_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3636_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
uint8_t v___x_3631_; 
v___x_3631_ = lean_unbox(v_a_3627_);
lean_dec(v_a_3627_);
if (v___x_3631_ == 0)
{
lean_object* v___x_3632_; lean_object* v___x_3634_; 
lean_dec(v_a_3591_);
lean_dec_ref(v_kp_3522_);
lean_dec(v_mvarId_3520_);
lean_dec(v_fvarId_3519_);
v___x_3632_ = lean_box(0);
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 0, v___x_3632_);
v___x_3634_ = v___x_3629_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v___x_3632_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
else
{
lean_del_object(v___x_3629_);
v___y_3593_ = v___y_3523_;
v___y_3594_ = v___y_3524_;
v___y_3595_ = v___y_3525_;
v___y_3596_ = v___y_3526_;
v___y_3597_ = v___y_3527_;
v___y_3598_ = v___y_3528_;
v___y_3599_ = v___y_3529_;
v___y_3600_ = v___y_3530_;
v___y_3601_ = v___y_3531_;
goto v___jp_3592_;
}
}
}
else
{
lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3644_; 
lean_dec(v_a_3591_);
lean_dec_ref(v_kp_3522_);
lean_dec(v_mvarId_3520_);
lean_dec(v_fvarId_3519_);
v_a_3637_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3639_ = v___x_3626_;
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___x_3626_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3642_; 
if (v_isShared_3640_ == 0)
{
v___x_3642_ = v___x_3639_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_a_3637_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
}
}
else
{
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3652_; 
lean_dec(v_a_3591_);
lean_dec_ref(v_kp_3522_);
lean_dec(v_mvarId_3520_);
lean_dec(v_fvarId_3519_);
v_a_3645_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3647_ = v___x_3623_;
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3623_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3650_; 
if (v_isShared_3648_ == 0)
{
v___x_3650_ = v___x_3647_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3645_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
}
}
}
else
{
lean_object* v_a_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3661_; 
lean_dec(v_a_3591_);
lean_dec_ref(v_kp_3522_);
lean_dec(v_mvarId_3520_);
lean_dec(v_fvarId_3519_);
v_a_3654_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3656_ = v___x_3613_;
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_a_3654_);
lean_dec(v___x_3613_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3659_; 
if (v_isShared_3657_ == 0)
{
v___x_3659_ = v___x_3656_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3654_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
v___jp_3592_:
{
lean_object* v___x_3602_; 
v___x_3602_ = l_Lean_Expr_getAppFn(v_a_3591_);
lean_dec(v_a_3591_);
if (lean_obj_tag(v___x_3602_) == 4)
{
lean_object* v_declName_3603_; lean_object* v___x_3604_; 
v_declName_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_declName_3603_);
lean_dec_ref_known(v___x_3602_, 2);
v___x_3604_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_3603_, v___y_3595_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_dec_ref_known(v___x_3604_, 1);
v___y_3534_ = v___y_3593_;
v___y_3535_ = v___y_3594_;
v___y_3536_ = v___y_3595_;
v___y_3537_ = v___y_3596_;
v___y_3538_ = v___y_3597_;
v___y_3539_ = v___y_3598_;
v___y_3540_ = v___y_3599_;
v___y_3541_ = v___y_3600_;
v___y_3542_ = v___y_3601_;
goto v___jp_3533_;
}
else
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3612_; 
lean_dec_ref(v_kp_3522_);
lean_dec(v_mvarId_3520_);
lean_dec(v_fvarId_3519_);
v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3607_ = v___x_3604_;
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3604_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3610_; 
if (v_isShared_3608_ == 0)
{
v___x_3610_ = v___x_3607_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_a_3605_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
else
{
lean_dec_ref(v___x_3602_);
v___y_3534_ = v___y_3593_;
v___y_3535_ = v___y_3594_;
v___y_3536_ = v___y_3595_;
v___y_3537_ = v___y_3596_;
v___y_3538_ = v___y_3597_;
v___y_3539_ = v___y_3598_;
v___y_3540_ = v___y_3599_;
v___y_3541_ = v___y_3600_;
v___y_3542_ = v___y_3601_;
goto v___jp_3533_;
}
}
}
else
{
lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3669_; 
lean_dec_ref(v_kp_3522_);
lean_dec(v_mvarId_3520_);
lean_dec(v_fvarId_3519_);
v_a_3662_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3664_ = v___x_3590_;
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v___x_3590_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3667_; 
if (v_isShared_3665_ == 0)
{
v___x_3667_ = v___x_3664_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_a_3662_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
}
}
else
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
lean_dec_ref(v_kp_3522_);
lean_dec(v_mvarId_3520_);
lean_dec(v_fvarId_3519_);
v_a_3670_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3672_ = v___x_3588_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3588_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3670_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
v___jp_3533_:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3543_ = l_Lean_mkFVar(v_fvarId_3519_);
v___x_3544_ = l_Lean_Meta_Grind_cases(v_mvarId_3520_, v___x_3543_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v_a_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
lean_inc(v_a_3545_);
lean_dec_ref_known(v___x_3544_, 1);
v___x_3546_ = lean_box(0);
v___x_3547_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v_goal_3521_, v_a_3545_, v___x_3546_);
v___x_3548_ = lean_unsigned_to_nat(0u);
v___x_3549_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__1));
v___x_3550_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3522_, v___x_3547_, v___x_3549_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
lean_dec(v___x_3547_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3571_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3553_ = v___x_3550_;
v_isShared_3554_ = v_isSharedCheck_3571_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3550_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3571_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v_fst_3555_; lean_object* v_snd_3556_; lean_object* v___x_3557_; uint8_t v___x_3558_; 
v_fst_3555_ = lean_ctor_get(v_a_3551_, 0);
lean_inc(v_fst_3555_);
v_snd_3556_ = lean_ctor_get(v_a_3551_, 1);
lean_inc(v_snd_3556_);
lean_dec(v_a_3551_);
v___x_3557_ = lean_array_get_size(v_snd_3556_);
v___x_3558_ = lean_nat_dec_eq(v___x_3557_, v___x_3548_);
if (v___x_3558_ == 0)
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3563_; 
lean_dec(v_fst_3555_);
v___x_3559_ = lean_array_to_list(v_snd_3556_);
v___x_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3559_);
v___x_3561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3560_);
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 0, v___x_3561_);
v___x_3563_ = v___x_3553_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v___x_3561_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
else
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3569_; 
lean_dec(v_snd_3556_);
v___x_3565_ = lean_array_to_list(v_fst_3555_);
v___x_3566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3565_);
v___x_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3566_);
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 0, v___x_3567_);
v___x_3569_ = v___x_3553_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v___x_3567_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
}
else
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
v_a_3572_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3574_ = v___x_3550_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3550_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3577_; 
if (v_isShared_3575_ == 0)
{
v___x_3577_ = v___x_3574_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_a_3572_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
else
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
lean_dec_ref(v_kp_3522_);
v_a_3580_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3582_ = v___x_3544_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v___x_3544_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_3519_ = stack[0].m_obj;
lean_object* v_mvarId_3520_ = stack[1].m_obj;
lean_object* v_goal_3521_ = stack[2].m_obj;
lean_object* v_kp_3522_ = stack[3].m_obj;
lean_object* v___y_3523_ = stack[4].m_obj;
lean_object* v___y_3524_ = stack[5].m_obj;
lean_object* v___y_3525_ = stack[6].m_obj;
lean_object* v___y_3526_ = stack[7].m_obj;
lean_object* v___y_3527_ = stack[8].m_obj;
lean_object* v___y_3528_ = stack[9].m_obj;
lean_object* v___y_3529_ = stack[10].m_obj;
lean_object* v___y_3530_ = stack[11].m_obj;
lean_object* v___y_3531_ = stack[12].m_obj;
lean_object* v_res_3678_;
v_res_3678_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(v_fvarId_3519_, v_mvarId_3520_, v_goal_3521_, v_kp_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_);
stack->m_obj
 = v_res_3678_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed(lean_object* v_fvarId_3679_, lean_object* v_mvarId_3680_, lean_object* v_goal_3681_, lean_object* v_kp_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(v_fvarId_3679_, v_mvarId_3680_, v_goal_3681_, v_kp_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec(v___y_3683_);
lean_dec_ref(v_goal_3681_);
return v_res_3693_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(lean_object* v_goal_3694_, lean_object* v_fvarId_3695_, lean_object* v_kp_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_){
_start:
{
lean_object* v_mvarId_3707_; lean_object* v___f_3708_; lean_object* v___x_3709_; 
v_mvarId_3707_ = lean_ctor_get(v_goal_3694_, 1);
lean_inc_n(v_mvarId_3707_, 2);
v___f_3708_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed), 14, 4);
lean_closure_set(v___f_3708_, 0, v_fvarId_3695_);
lean_closure_set(v___f_3708_, 1, v_mvarId_3707_);
lean_closure_set(v___f_3708_, 2, v_goal_3694_);
lean_closure_set(v___f_3708_, 3, v_kp_3696_);
v___x_3709_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3707_, v___f_3708_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_);
return v___x_3709_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_3694_ = stack[0].m_obj;
lean_object* v_fvarId_3695_ = stack[1].m_obj;
lean_object* v_kp_3696_ = stack[2].m_obj;
lean_object* v_a_3697_ = stack[3].m_obj;
lean_object* v_a_3698_ = stack[4].m_obj;
lean_object* v_a_3699_ = stack[5].m_obj;
lean_object* v_a_3700_ = stack[6].m_obj;
lean_object* v_a_3701_ = stack[7].m_obj;
lean_object* v_a_3702_ = stack[8].m_obj;
lean_object* v_a_3703_ = stack[9].m_obj;
lean_object* v_a_3704_ = stack[10].m_obj;
lean_object* v_a_3705_ = stack[11].m_obj;
lean_object* v_res_3710_;
v_res_3710_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3694_, v_fvarId_3695_, v_kp_3696_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_);
stack->m_obj
 = v_res_3710_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___boxed(lean_object* v_goal_3711_, lean_object* v_fvarId_3712_, lean_object* v_kp_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_){
_start:
{
lean_object* v_res_3724_; 
v_res_3724_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3711_, v_fvarId_3712_, v_kp_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_, v_a_3722_);
lean_dec(v_a_3722_);
lean_dec_ref(v_a_3721_);
lean_dec(v_a_3720_);
lean_dec_ref(v_a_3719_);
lean_dec(v_a_3718_);
lean_dec_ref(v_a_3717_);
lean_dec(v_a_3716_);
lean_dec_ref(v_a_3715_);
lean_dec(v_a_3714_);
return v_res_3724_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(lean_object* v_kp_3725_, lean_object* v_as_3726_, lean_object* v_as_x27_3727_, lean_object* v_b_3728_, lean_object* v_a_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_){
_start:
{
lean_object* v___x_3740_; 
v___x_3740_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3725_, v_as_x27_3727_, v_b_3728_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_);
return v___x_3740_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_kp_3725_ = stack[0].m_obj;
lean_object* v_as_3726_ = stack[1].m_obj;
lean_object* v_as_x27_3727_ = stack[2].m_obj;
lean_object* v_b_3728_ = stack[3].m_obj;
lean_object* v___y_3730_ = stack[5].m_obj;
lean_object* v___y_3731_ = stack[6].m_obj;
lean_object* v___y_3732_ = stack[7].m_obj;
lean_object* v___y_3733_ = stack[8].m_obj;
lean_object* v___y_3734_ = stack[9].m_obj;
lean_object* v___y_3735_ = stack[10].m_obj;
lean_object* v___y_3736_ = stack[11].m_obj;
lean_object* v___y_3737_ = stack[12].m_obj;
lean_object* v___y_3738_ = stack[13].m_obj;
lean_object* v_res_3741_;
v_res_3741_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(v_kp_3725_, v_as_3726_, v_as_x27_3727_, v_b_3728_, lean_box(0), v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_);
stack->m_obj
 = v_res_3741_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___boxed(lean_object* v_kp_3742_, lean_object* v_as_3743_, lean_object* v_as_x27_3744_, lean_object* v_b_3745_, lean_object* v_a_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v_res_3757_; 
v_res_3757_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(v_kp_3742_, v_as_3743_, v_as_x27_3744_, v_b_3745_, v_a_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
lean_dec(v___y_3747_);
lean_dec(v_as_x27_3744_);
lean_dec(v_as_3743_);
return v_res_3757_;
}
}
lean_object* l_Lean_Meta_Grind_Action_intro___lam__0(lean_object* v_goal_3758_, lean_object* v_fvarId_3759_, lean_object* v_generation_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_){
_start:
{
lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3771_ = lean_st_mk_ref(v_goal_3758_);
v___x_3772_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_3759_, v_generation_3760_, v___x_3771_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3781_; 
v_isSharedCheck_3781_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3781_ == 0)
{
lean_object* v_unused_3782_; 
v_unused_3782_ = lean_ctor_get(v___x_3772_, 0);
lean_dec(v_unused_3782_);
v___x_3774_ = v___x_3772_;
v_isShared_3775_ = v_isSharedCheck_3781_;
goto v_resetjp_3773_;
}
else
{
lean_dec(v___x_3772_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3781_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3779_; 
v___x_3776_ = lean_st_ref_get(v___x_3771_);
v___x_3777_ = lean_st_ref_get(v___x_3771_);
lean_dec(v___x_3771_);
lean_dec(v___x_3777_);
if (v_isShared_3775_ == 0)
{
lean_ctor_set(v___x_3774_, 0, v___x_3776_);
v___x_3779_ = v___x_3774_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3776_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
else
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
lean_dec(v___x_3771_);
v_a_3783_ = lean_ctor_get(v___x_3772_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v___x_3772_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3772_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_intro___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_3758_ = stack[0].m_obj;
lean_object* v_fvarId_3759_ = stack[1].m_obj;
lean_object* v_generation_3760_ = stack[2].m_obj;
lean_object* v___y_3761_ = stack[3].m_obj;
lean_object* v___y_3762_ = stack[4].m_obj;
lean_object* v___y_3763_ = stack[5].m_obj;
lean_object* v___y_3764_ = stack[6].m_obj;
lean_object* v___y_3765_ = stack[7].m_obj;
lean_object* v___y_3766_ = stack[8].m_obj;
lean_object* v___y_3767_ = stack[9].m_obj;
lean_object* v___y_3768_ = stack[10].m_obj;
lean_object* v___y_3769_ = stack[11].m_obj;
lean_object* v_res_3791_;
v_res_3791_ = l_Lean_Meta_Grind_Action_intro___lam__0(v_goal_3758_, v_fvarId_3759_, v_generation_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
stack->m_obj
 = v_res_3791_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0___boxed(lean_object* v_goal_3792_, lean_object* v_fvarId_3793_, lean_object* v_generation_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
lean_object* v_res_3805_; 
v_res_3805_ = l_Lean_Meta_Grind_Action_intro___lam__0(v_goal_3792_, v_fvarId_3793_, v_generation_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
lean_dec(v___y_3801_);
lean_dec_ref(v___y_3800_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v___y_3795_);
return v_res_3805_;
}
}
lean_object* l_Lean_Meta_Grind_Action_intro(lean_object* v_generation_3808_, lean_object* v_goal_3809_, lean_object* v_kna_3810_, lean_object* v_kp_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_){
_start:
{
lean_object* v_toGoalState_3822_; uint8_t v_inconsistent_3823_; 
v_toGoalState_3822_ = lean_ctor_get(v_goal_3809_, 0);
v_inconsistent_3823_ = lean_ctor_get_uint8(v_toGoalState_3822_, sizeof(void*)*17);
if (v_inconsistent_3823_ == 0)
{
lean_object* v_mvarId_3824_; lean_object* v___x_3825_; 
v_mvarId_3824_ = lean_ctor_get(v_goal_3809_, 1);
lean_inc(v_mvarId_3824_);
v___x_3825_ = l_Lean_MVarId_getType(v_mvarId_3824_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_object* v_a_3826_; uint8_t v___x_3827_; 
v_a_3826_ = lean_ctor_get(v___x_3825_, 0);
lean_inc(v_a_3826_);
lean_dec_ref_known(v___x_3825_, 1);
v___x_3827_ = l_Lean_Expr_isFalse(v_a_3826_);
if (v___x_3827_ == 0)
{
lean_object* v___x_3828_; 
lean_dec_ref(v_kna_3810_);
lean_inc(v_generation_3808_);
v___x_3828_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_3809_, v_generation_3808_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_a_3829_);
lean_dec_ref_known(v___x_3828_, 1);
switch(lean_obj_tag(v_a_3829_))
{
case 0:
{
lean_object* v_goal_3830_; lean_object* v___x_3831_; 
lean_dec(v_generation_3808_);
v_goal_3830_ = lean_ctor_get(v_a_3829_, 0);
lean_inc_ref(v_goal_3830_);
lean_dec_ref_known(v_a_3829_, 1);
v___x_3831_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_3830_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v_a_3832_; lean_object* v___x_3833_; 
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
lean_inc(v_a_3832_);
lean_dec_ref_known(v___x_3831_, 1);
v___x_3833_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget(v_a_3832_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
if (lean_obj_tag(v___x_3833_) == 0)
{
lean_object* v_a_3834_; lean_object* v_toGoalState_3835_; lean_object* v_mvarId_3836_; lean_object* v___x_3837_; 
v_a_3834_ = lean_ctor_get(v___x_3833_, 0);
lean_inc(v_a_3834_);
lean_dec_ref_known(v___x_3833_, 1);
v_toGoalState_3835_ = lean_ctor_get(v_a_3834_, 0);
v_mvarId_3836_ = lean_ctor_get(v_a_3834_, 1);
lean_inc(v_mvarId_3836_);
v___x_3837_ = l_Lean_MVarId_getType(v_mvarId_3836_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v_a_3838_; uint8_t v___x_3839_; 
v_a_3838_ = lean_ctor_get(v___x_3837_, 0);
lean_inc(v_a_3838_);
lean_dec_ref_known(v___x_3837_, 1);
v___x_3839_ = l_Lean_Expr_isForall(v_a_3838_);
if (v___x_3839_ == 0)
{
uint8_t v___x_3840_; 
v___x_3840_ = l_Lean_Expr_isLet(v_a_3838_);
lean_dec(v_a_3838_);
if (v___x_3840_ == 0)
{
lean_object* v___x_3841_; 
lean_inc(v_mvarId_3836_);
v___x_3841_ = l_Lean_MVarId_byContra_x3f(v_mvarId_3836_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
if (lean_obj_tag(v___x_3841_) == 0)
{
lean_object* v_a_3842_; 
v_a_3842_ = lean_ctor_get(v___x_3841_, 0);
lean_inc(v_a_3842_);
lean_dec_ref_known(v___x_3841_, 1);
if (lean_obj_tag(v_a_3842_) == 1)
{
lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3851_; 
lean_inc_ref(v_toGoalState_3835_);
v_isSharedCheck_3851_ = !lean_is_exclusive(v_a_3834_);
if (v_isSharedCheck_3851_ == 0)
{
lean_object* v_unused_3852_; lean_object* v_unused_3853_; 
v_unused_3852_ = lean_ctor_get(v_a_3834_, 1);
lean_dec(v_unused_3852_);
v_unused_3853_ = lean_ctor_get(v_a_3834_, 0);
lean_dec(v_unused_3853_);
v___x_3844_ = v_a_3834_;
v_isShared_3845_ = v_isSharedCheck_3851_;
goto v_resetjp_3843_;
}
else
{
lean_dec(v_a_3834_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3851_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v_val_3846_; lean_object* v___x_3848_; 
v_val_3846_ = lean_ctor_get(v_a_3842_, 0);
lean_inc(v_val_3846_);
lean_dec_ref_known(v_a_3842_, 1);
if (v_isShared_3845_ == 0)
{
lean_ctor_set(v___x_3844_, 1, v_val_3846_);
v___x_3848_ = v___x_3844_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_toGoalState_3835_);
lean_ctor_set(v_reuseFailAlloc_3850_, 1, v_val_3846_);
v___x_3848_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
lean_object* v___x_3849_; 
lean_inc(v_a_3820_);
lean_inc_ref(v_a_3819_);
lean_inc(v_a_3818_);
lean_inc_ref(v_a_3817_);
lean_inc(v_a_3816_);
lean_inc_ref(v_a_3815_);
lean_inc(v_a_3814_);
lean_inc_ref(v_a_3813_);
lean_inc(v_a_3812_);
v___x_3849_ = lean_apply_11(v_kp_3811_, v___x_3848_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, lean_box(0));
return v___x_3849_;
}
}
}
else
{
lean_object* v___x_3854_; 
lean_dec(v_a_3842_);
lean_inc(v_a_3820_);
lean_inc_ref(v_a_3819_);
lean_inc(v_a_3818_);
lean_inc_ref(v_a_3817_);
lean_inc(v_a_3816_);
lean_inc_ref(v_a_3815_);
lean_inc(v_a_3814_);
lean_inc_ref(v_a_3813_);
lean_inc(v_a_3812_);
v___x_3854_ = lean_apply_11(v_kp_3811_, v_a_3834_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, lean_box(0));
return v___x_3854_;
}
}
else
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
lean_dec(v_a_3834_);
lean_dec_ref(v_kp_3811_);
v_a_3855_ = lean_ctor_get(v___x_3841_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3857_ = v___x_3841_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3841_);
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
else
{
lean_object* v___x_3863_; 
lean_inc(v_a_3820_);
lean_inc_ref(v_a_3819_);
lean_inc(v_a_3818_);
lean_inc_ref(v_a_3817_);
lean_inc(v_a_3816_);
lean_inc_ref(v_a_3815_);
lean_inc(v_a_3814_);
lean_inc_ref(v_a_3813_);
lean_inc(v_a_3812_);
v___x_3863_ = lean_apply_11(v_kp_3811_, v_a_3834_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, lean_box(0));
return v___x_3863_;
}
}
else
{
lean_object* v___x_3864_; 
lean_dec(v_a_3838_);
lean_inc(v_a_3820_);
lean_inc_ref(v_a_3819_);
lean_inc(v_a_3818_);
lean_inc_ref(v_a_3817_);
lean_inc(v_a_3816_);
lean_inc_ref(v_a_3815_);
lean_inc(v_a_3814_);
lean_inc_ref(v_a_3813_);
lean_inc(v_a_3812_);
v___x_3864_ = lean_apply_11(v_kp_3811_, v_a_3834_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, lean_box(0));
return v___x_3864_;
}
}
else
{
lean_object* v_a_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3872_; 
lean_dec(v_a_3834_);
lean_dec_ref(v_kp_3811_);
v_a_3865_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3867_ = v___x_3837_;
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_a_3865_);
lean_dec(v___x_3837_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3870_; 
if (v_isShared_3868_ == 0)
{
v___x_3870_ = v___x_3867_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_a_3865_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
}
else
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3880_; 
lean_dec_ref(v_kp_3811_);
v_a_3873_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3875_ = v___x_3833_;
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3833_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3878_; 
if (v_isShared_3876_ == 0)
{
v___x_3878_ = v___x_3875_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_a_3873_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
else
{
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3888_; 
lean_dec_ref(v_kp_3811_);
v_a_3881_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3883_ = v___x_3831_;
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v___x_3831_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3886_; 
if (v_isShared_3884_ == 0)
{
v___x_3886_ = v___x_3883_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_a_3881_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3889_; lean_object* v_goal_3890_; lean_object* v___f_3891_; lean_object* v___x_3892_; 
v_fvarId_3889_ = lean_ctor_get(v_a_3829_, 0);
lean_inc_n(v_fvarId_3889_, 3);
v_goal_3890_ = lean_ctor_get(v_a_3829_, 1);
lean_inc_ref_n(v_goal_3890_, 3);
lean_dec_ref_known(v_a_3829_, 2);
v___f_3891_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intro___lam__0___boxed), 13, 3);
lean_closure_set(v___f_3891_, 0, v_goal_3890_);
lean_closure_set(v___f_3891_, 1, v_fvarId_3889_);
lean_closure_set(v___f_3891_, 2, v_generation_3808_);
v___x_3892_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_3890_, v_fvarId_3889_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_a_3893_);
lean_dec_ref_known(v___x_3892_, 1);
if (lean_obj_tag(v_a_3893_) == 1)
{
lean_object* v_val_3894_; lean_object* v___x_3895_; 
lean_dec_ref(v___f_3891_);
lean_dec_ref(v_goal_3890_);
lean_dec(v_fvarId_3889_);
v_val_3894_ = lean_ctor_get(v_a_3893_, 0);
lean_inc(v_val_3894_);
lean_dec_ref_known(v_a_3893_, 1);
lean_inc(v_a_3820_);
lean_inc_ref(v_a_3819_);
lean_inc(v_a_3818_);
lean_inc_ref(v_a_3817_);
lean_inc(v_a_3816_);
lean_inc_ref(v_a_3815_);
lean_inc(v_a_3814_);
lean_inc_ref(v_a_3813_);
lean_inc(v_a_3812_);
v___x_3895_ = lean_apply_11(v_kp_3811_, v_val_3894_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, lean_box(0));
return v___x_3895_;
}
else
{
lean_object* v___x_3896_; 
lean_dec(v_a_3893_);
lean_inc_ref(v_kp_3811_);
lean_inc_ref(v_goal_3890_);
v___x_3896_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3890_, v_fvarId_3889_, v_kp_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3917_; 
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3899_ = v___x_3896_;
v_isShared_3900_ = v_isSharedCheck_3917_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3896_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3917_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
if (lean_obj_tag(v_a_3897_) == 1)
{
lean_object* v_val_3901_; lean_object* v___x_3903_; 
lean_dec_ref(v___f_3891_);
lean_dec_ref(v_goal_3890_);
lean_dec_ref(v_kp_3811_);
v_val_3901_ = lean_ctor_get(v_a_3897_, 0);
lean_inc(v_val_3901_);
lean_dec_ref_known(v_a_3897_, 1);
if (v_isShared_3900_ == 0)
{
lean_ctor_set(v___x_3899_, 0, v_val_3901_);
v___x_3903_ = v___x_3899_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_val_3901_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
else
{
lean_object* v_mvarId_3905_; lean_object* v___x_3906_; 
lean_del_object(v___x_3899_);
lean_dec(v_a_3897_);
v_mvarId_3905_ = lean_ctor_get(v_goal_3890_, 1);
lean_inc(v_mvarId_3905_);
lean_dec_ref(v_goal_3890_);
v___x_3906_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3905_, v___f_3891_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v_a_3907_; lean_object* v___x_3908_; 
v_a_3907_ = lean_ctor_get(v___x_3906_, 0);
lean_inc(v_a_3907_);
lean_dec_ref_known(v___x_3906_, 1);
lean_inc(v_a_3820_);
lean_inc_ref(v_a_3819_);
lean_inc(v_a_3818_);
lean_inc_ref(v_a_3817_);
lean_inc(v_a_3816_);
lean_inc_ref(v_a_3815_);
lean_inc(v_a_3814_);
lean_inc_ref(v_a_3813_);
lean_inc(v_a_3812_);
v___x_3908_ = lean_apply_11(v_kp_3811_, v_a_3907_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, lean_box(0));
return v___x_3908_;
}
else
{
lean_object* v_a_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3916_; 
lean_dec_ref(v_kp_3811_);
v_a_3909_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3916_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3911_ = v___x_3906_;
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_a_3909_);
lean_dec(v___x_3906_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v___x_3914_; 
if (v_isShared_3912_ == 0)
{
v___x_3914_ = v___x_3911_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_a_3909_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
}
}
}
}
else
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3925_; 
lean_dec_ref(v___f_3891_);
lean_dec_ref(v_goal_3890_);
lean_dec_ref(v_kp_3811_);
v_a_3918_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3920_ = v___x_3896_;
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3896_);
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
}
else
{
lean_object* v_a_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3933_; 
lean_dec_ref(v___f_3891_);
lean_dec_ref(v_goal_3890_);
lean_dec(v_fvarId_3889_);
lean_dec_ref(v_kp_3811_);
v_a_3926_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3928_ = v___x_3892_;
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_a_3926_);
lean_dec(v___x_3892_);
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
case 2:
{
lean_object* v_goal_3934_; lean_object* v___x_3935_; 
lean_dec(v_generation_3808_);
v_goal_3934_ = lean_ctor_get(v_a_3829_, 0);
lean_inc_ref(v_goal_3934_);
lean_dec_ref_known(v_a_3829_, 1);
lean_inc(v_a_3820_);
lean_inc_ref(v_a_3819_);
lean_inc(v_a_3818_);
lean_inc_ref(v_a_3817_);
lean_inc(v_a_3816_);
lean_inc_ref(v_a_3815_);
lean_inc(v_a_3814_);
lean_inc_ref(v_a_3813_);
lean_inc(v_a_3812_);
v___x_3935_ = lean_apply_11(v_kp_3811_, v_goal_3934_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, lean_box(0));
return v___x_3935_;
}
default: 
{
lean_object* v_fvarId_3936_; lean_object* v_goal_3937_; lean_object* v___x_3938_; 
lean_dec(v_generation_3808_);
v_fvarId_3936_ = lean_ctor_get(v_a_3829_, 0);
lean_inc(v_fvarId_3936_);
v_goal_3937_ = lean_ctor_get(v_a_3829_, 1);
lean_inc_ref_n(v_goal_3937_, 2);
lean_dec_ref_known(v_a_3829_, 2);
lean_inc_ref(v_kp_3811_);
v___x_3938_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_3937_, v_fvarId_3936_, v_kp_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
if (lean_obj_tag(v___x_3938_) == 0)
{
lean_object* v_a_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3948_; 
v_a_3939_ = lean_ctor_get(v___x_3938_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3938_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3941_ = v___x_3938_;
v_isShared_3942_ = v_isSharedCheck_3948_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_a_3939_);
lean_dec(v___x_3938_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3948_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
if (lean_obj_tag(v_a_3939_) == 1)
{
lean_object* v_val_3943_; lean_object* v___x_3945_; 
lean_dec_ref(v_goal_3937_);
lean_dec_ref(v_kp_3811_);
v_val_3943_ = lean_ctor_get(v_a_3939_, 0);
lean_inc(v_val_3943_);
lean_dec_ref_known(v_a_3939_, 1);
if (v_isShared_3942_ == 0)
{
lean_ctor_set(v___x_3941_, 0, v_val_3943_);
v___x_3945_ = v___x_3941_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_val_3943_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
else
{
lean_object* v___x_3947_; 
lean_del_object(v___x_3941_);
lean_dec(v_a_3939_);
lean_inc(v_a_3820_);
lean_inc_ref(v_a_3819_);
lean_inc(v_a_3818_);
lean_inc_ref(v_a_3817_);
lean_inc(v_a_3816_);
lean_inc_ref(v_a_3815_);
lean_inc(v_a_3814_);
lean_inc_ref(v_a_3813_);
lean_inc(v_a_3812_);
v___x_3947_ = lean_apply_11(v_kp_3811_, v_goal_3937_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, lean_box(0));
return v___x_3947_;
}
}
}
else
{
lean_object* v_a_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3956_; 
lean_dec_ref(v_goal_3937_);
lean_dec_ref(v_kp_3811_);
v_a_3949_ = lean_ctor_get(v___x_3938_, 0);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___x_3938_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3951_ = v___x_3938_;
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_a_3949_);
lean_dec(v___x_3938_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3954_; 
if (v_isShared_3952_ == 0)
{
v___x_3954_ = v___x_3951_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_a_3949_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
return v___x_3954_;
}
}
}
}
}
}
else
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3964_; 
lean_dec_ref(v_kp_3811_);
lean_dec(v_generation_3808_);
v_a_3957_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3959_ = v___x_3828_;
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3828_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3962_; 
if (v_isShared_3960_ == 0)
{
v___x_3962_ = v___x_3959_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_a_3957_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
}
else
{
lean_object* v___x_3965_; 
lean_dec_ref(v_kp_3811_);
lean_dec(v_generation_3808_);
lean_inc(v_a_3820_);
lean_inc_ref(v_a_3819_);
lean_inc(v_a_3818_);
lean_inc_ref(v_a_3817_);
lean_inc(v_a_3816_);
lean_inc_ref(v_a_3815_);
lean_inc(v_a_3814_);
lean_inc_ref(v_a_3813_);
lean_inc(v_a_3812_);
v___x_3965_ = lean_apply_11(v_kna_3810_, v_goal_3809_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, lean_box(0));
return v___x_3965_;
}
}
else
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3973_; 
lean_dec_ref(v_kp_3811_);
lean_dec_ref(v_kna_3810_);
lean_dec_ref(v_goal_3809_);
lean_dec(v_generation_3808_);
v_a_3966_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3973_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3968_ = v___x_3825_;
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3825_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3971_; 
if (v_isShared_3969_ == 0)
{
v___x_3971_ = v___x_3968_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_a_3966_);
v___x_3971_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
return v___x_3971_;
}
}
}
}
else
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
lean_dec_ref(v_kp_3811_);
lean_dec_ref(v_kna_3810_);
lean_dec_ref(v_goal_3809_);
lean_dec(v_generation_3808_);
v___x_3974_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intro___closed__0));
v___x_3975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3975_, 0, v___x_3974_);
return v___x_3975_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_intro_0interp(lean_interpreter_value* stack)
{
lean_object* v_generation_3808_ = stack[0].m_obj;
lean_object* v_goal_3809_ = stack[1].m_obj;
lean_object* v_kna_3810_ = stack[2].m_obj;
lean_object* v_kp_3811_ = stack[3].m_obj;
lean_object* v_a_3812_ = stack[4].m_obj;
lean_object* v_a_3813_ = stack[5].m_obj;
lean_object* v_a_3814_ = stack[6].m_obj;
lean_object* v_a_3815_ = stack[7].m_obj;
lean_object* v_a_3816_ = stack[8].m_obj;
lean_object* v_a_3817_ = stack[9].m_obj;
lean_object* v_a_3818_ = stack[10].m_obj;
lean_object* v_a_3819_ = stack[11].m_obj;
lean_object* v_a_3820_ = stack[12].m_obj;
lean_object* v_res_3976_;
v_res_3976_ = l_Lean_Meta_Grind_Action_intro(v_generation_3808_, v_goal_3809_, v_kna_3810_, v_kp_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
stack->m_obj
 = v_res_3976_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___boxed(lean_object* v_generation_3977_, lean_object* v_goal_3978_, lean_object* v_kna_3979_, lean_object* v_kp_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_){
_start:
{
lean_object* v_res_3991_; 
v_res_3991_ = l_Lean_Meta_Grind_Action_intro(v_generation_3977_, v_goal_3978_, v_kna_3979_, v_kp_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_);
lean_dec(v_a_3989_);
lean_dec_ref(v_a_3988_);
lean_dec(v_a_3987_);
lean_dec_ref(v_a_3986_);
lean_dec(v_a_3985_);
lean_dec_ref(v_a_3984_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
lean_dec(v_a_3981_);
return v_res_3991_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_hugeNumber(void){
_start:
{
lean_object* v___x_3992_; 
v___x_3992_ = lean_unsigned_to_nat(1000000u);
return v___x_3992_;
}
}
lean_object* l_Lean_Meta_Grind_Action_intros___lam__0(lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
lean_object* v___x_4006_; 
v___x_4006_ = l_Lean_Meta_Grind_Action_group___redArg(v___y_3993_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
return v___x_4006_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_intros___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3993_ = stack[0].m_obj;
lean_object* v___y_3994_ = stack[1].m_obj;
lean_object* v___y_3995_ = stack[2].m_obj;
lean_object* v___y_3996_ = stack[3].m_obj;
lean_object* v___y_3997_ = stack[4].m_obj;
lean_object* v___y_3998_ = stack[5].m_obj;
lean_object* v___y_3999_ = stack[6].m_obj;
lean_object* v___y_4000_ = stack[7].m_obj;
lean_object* v___y_4001_ = stack[8].m_obj;
lean_object* v___y_4002_ = stack[9].m_obj;
lean_object* v___y_4003_ = stack[10].m_obj;
lean_object* v___y_4004_ = stack[11].m_obj;
lean_object* v_res_4007_;
v_res_4007_ = l_Lean_Meta_Grind_Action_intros___lam__0(v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
stack->m_obj
 = v_res_4007_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0___boxed(lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = l_Lean_Meta_Grind_Action_intros___lam__0(v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec(v___y_4015_);
lean_dec_ref(v___y_4014_);
lean_dec(v___y_4013_);
lean_dec_ref(v___y_4012_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4009_);
return v_res_4021_;
}
}
lean_object* l_Lean_Meta_Grind_Action_intros___lam__1(lean_object* v_generation_4022_, lean_object* v___f_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_){
_start:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; 
v___x_4037_ = lean_unsigned_to_nat(1000000u);
v___x_4038_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intro___boxed), 14, 1);
lean_closure_set(v___x_4038_, 0, v_generation_4022_);
v___x_4039_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_loop___boxed), 15, 2);
lean_closure_set(v___x_4039_, 0, v___x_4037_);
lean_closure_set(v___x_4039_, 1, v___x_4038_);
v___x_4040_ = l_Lean_Meta_Grind_Action_andThen(v___x_4039_, v___f_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
return v___x_4040_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_intros___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_generation_4022_ = stack[0].m_obj;
lean_object* v___f_4023_ = stack[1].m_obj;
lean_object* v___y_4024_ = stack[2].m_obj;
lean_object* v___y_4025_ = stack[3].m_obj;
lean_object* v___y_4026_ = stack[4].m_obj;
lean_object* v___y_4027_ = stack[5].m_obj;
lean_object* v___y_4028_ = stack[6].m_obj;
lean_object* v___y_4029_ = stack[7].m_obj;
lean_object* v___y_4030_ = stack[8].m_obj;
lean_object* v___y_4031_ = stack[9].m_obj;
lean_object* v___y_4032_ = stack[10].m_obj;
lean_object* v___y_4033_ = stack[11].m_obj;
lean_object* v___y_4034_ = stack[12].m_obj;
lean_object* v___y_4035_ = stack[13].m_obj;
lean_object* v_res_4041_;
v_res_4041_ = l_Lean_Meta_Grind_Action_intros___lam__1(v_generation_4022_, v___f_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
stack->m_obj
 = v_res_4041_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1___boxed(lean_object* v_generation_4042_, lean_object* v___f_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_){
_start:
{
lean_object* v_res_4057_; 
v_res_4057_ = l_Lean_Meta_Grind_Action_intros___lam__1(v_generation_4042_, v___f_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_);
lean_dec(v___y_4055_);
lean_dec_ref(v___y_4054_);
lean_dec(v___y_4053_);
lean_dec_ref(v___y_4052_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
lean_dec(v___y_4049_);
lean_dec_ref(v___y_4048_);
lean_dec(v___y_4047_);
return v_res_4057_;
}
}
lean_object* l_Lean_Meta_Grind_Action_intros(lean_object* v_generation_4060_, lean_object* v_a_4061_, lean_object* v_kna_4062_, lean_object* v_kp_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_){
_start:
{
lean_object* v___f_4074_; lean_object* v___f_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___f_4074_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intros___closed__0));
v___f_4075_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___lam__1___boxed), 15, 2);
lean_closure_set(v___f_4075_, 0, v_generation_4060_);
lean_closure_set(v___f_4075_, 1, v___f_4074_);
v___x_4076_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intros___closed__1));
v___x_4077_ = l_Lean_Meta_Grind_Action_andThen(v___x_4076_, v___f_4075_, v_a_4061_, v_kna_4062_, v_kp_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_);
return v___x_4077_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_intros_0interp(lean_interpreter_value* stack)
{
lean_object* v_generation_4060_ = stack[0].m_obj;
lean_object* v_a_4061_ = stack[1].m_obj;
lean_object* v_kna_4062_ = stack[2].m_obj;
lean_object* v_kp_4063_ = stack[3].m_obj;
lean_object* v_a_4064_ = stack[4].m_obj;
lean_object* v_a_4065_ = stack[5].m_obj;
lean_object* v_a_4066_ = stack[6].m_obj;
lean_object* v_a_4067_ = stack[7].m_obj;
lean_object* v_a_4068_ = stack[8].m_obj;
lean_object* v_a_4069_ = stack[9].m_obj;
lean_object* v_a_4070_ = stack[10].m_obj;
lean_object* v_a_4071_ = stack[11].m_obj;
lean_object* v_a_4072_ = stack[12].m_obj;
lean_object* v_res_4078_;
v_res_4078_ = l_Lean_Meta_Grind_Action_intros(v_generation_4060_, v_a_4061_, v_kna_4062_, v_kp_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_);
stack->m_obj
 = v_res_4078_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___boxed(lean_object* v_generation_4079_, lean_object* v_a_4080_, lean_object* v_kna_4081_, lean_object* v_kp_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_){
_start:
{
lean_object* v_res_4093_; 
v_res_4093_ = l_Lean_Meta_Grind_Action_intros(v_generation_4079_, v_a_4080_, v_kna_4081_, v_kp_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_, v_a_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_);
lean_dec(v_a_4091_);
lean_dec_ref(v_a_4090_);
lean_dec(v_a_4089_);
lean_dec_ref(v_a_4088_);
lean_dec(v_a_4087_);
lean_dec_ref(v_a_4086_);
lean_dec(v_a_4085_);
lean_dec_ref(v_a_4084_);
lean_dec(v_a_4083_);
return v_res_4093_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
v___x_4101_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__2));
v___x_4102_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1));
v___x_4103_ = l_Lean_mkConst(v___x_4102_, v___x_4101_);
return v___x_4103_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(lean_object* v_goal_4104_, lean_object* v_prop_4105_, lean_object* v_proof_4106_, lean_object* v_generation_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_){
_start:
{
lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4118_ = lean_st_mk_ref(v_goal_4104_);
lean_inc(v___y_4116_);
lean_inc_ref(v___y_4115_);
lean_inc(v___y_4114_);
lean_inc_ref(v___y_4113_);
lean_inc(v___y_4112_);
lean_inc_ref(v___y_4111_);
lean_inc(v___y_4110_);
lean_inc_ref(v___y_4109_);
lean_inc(v___y_4108_);
lean_inc(v___x_4118_);
lean_inc_ref(v_prop_4105_);
v___x_4119_ = lean_grind_preprocess(v_prop_4105_, v___x_4118_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v_a_4120_; lean_object* v_expr_4121_; lean_object* v___x_4122_; 
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
lean_inc(v_a_4120_);
lean_dec_ref_known(v___x_4119_, 1);
v_expr_4121_ = lean_ctor_get(v_a_4120_, 0);
lean_inc_ref(v_expr_4121_);
v___x_4122_ = l_Lean_Meta_Simp_Result_getProof(v_a_4120_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
if (lean_obj_tag(v___x_4122_) == 0)
{
lean_object* v_a_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; 
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
lean_inc(v_a_4123_);
lean_dec_ref_known(v___x_4122_, 1);
v___x_4124_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3);
lean_inc_ref(v_expr_4121_);
v___x_4125_ = l_Lean_mkApp4(v___x_4124_, v_prop_4105_, v_expr_4121_, v_a_4123_, v_proof_4106_);
v___x_4126_ = l_Lean_Meta_Grind_add(v_expr_4121_, v___x_4125_, v_generation_4107_, v___x_4118_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4135_; 
v_isSharedCheck_4135_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4135_ == 0)
{
lean_object* v_unused_4136_; 
v_unused_4136_ = lean_ctor_get(v___x_4126_, 0);
lean_dec(v_unused_4136_);
v___x_4128_ = v___x_4126_;
v_isShared_4129_ = v_isSharedCheck_4135_;
goto v_resetjp_4127_;
}
else
{
lean_dec(v___x_4126_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4135_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4133_; 
v___x_4130_ = lean_st_ref_get(v___x_4118_);
v___x_4131_ = lean_st_ref_get(v___x_4118_);
lean_dec(v___x_4118_);
lean_dec(v___x_4131_);
if (v_isShared_4129_ == 0)
{
lean_ctor_set(v___x_4128_, 0, v___x_4130_);
v___x_4133_ = v___x_4128_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v___x_4130_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
}
else
{
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4144_; 
lean_dec(v___x_4118_);
v_a_4137_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4139_ = v___x_4126_;
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v___x_4126_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4142_; 
if (v_isShared_4140_ == 0)
{
v___x_4142_ = v___x_4139_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_a_4137_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
}
else
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4152_; 
lean_dec_ref(v_expr_4121_);
lean_dec(v___x_4118_);
lean_dec(v_generation_4107_);
lean_dec_ref(v_proof_4106_);
lean_dec_ref(v_prop_4105_);
v_a_4145_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4147_ = v___x_4122_;
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v___x_4122_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4150_; 
if (v_isShared_4148_ == 0)
{
v___x_4150_ = v___x_4147_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_a_4145_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
}
}
else
{
lean_object* v_a_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4160_; 
lean_dec(v___x_4118_);
lean_dec(v_generation_4107_);
lean_dec_ref(v_proof_4106_);
lean_dec_ref(v_prop_4105_);
v_a_4153_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4155_ = v___x_4119_;
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_a_4153_);
lean_dec(v___x_4119_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4158_; 
if (v_isShared_4156_ == 0)
{
v___x_4158_ = v___x_4155_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_a_4153_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_4104_ = stack[0].m_obj;
lean_object* v_prop_4105_ = stack[1].m_obj;
lean_object* v_proof_4106_ = stack[2].m_obj;
lean_object* v_generation_4107_ = stack[3].m_obj;
lean_object* v___y_4108_ = stack[4].m_obj;
lean_object* v___y_4109_ = stack[5].m_obj;
lean_object* v___y_4110_ = stack[6].m_obj;
lean_object* v___y_4111_ = stack[7].m_obj;
lean_object* v___y_4112_ = stack[8].m_obj;
lean_object* v___y_4113_ = stack[9].m_obj;
lean_object* v___y_4114_ = stack[10].m_obj;
lean_object* v___y_4115_ = stack[11].m_obj;
lean_object* v___y_4116_ = stack[12].m_obj;
lean_object* v_res_4161_;
v_res_4161_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(v_goal_4104_, v_prop_4105_, v_proof_4106_, v_generation_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
stack->m_obj
 = v_res_4161_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed(lean_object* v_goal_4162_, lean_object* v_prop_4163_, lean_object* v_proof_4164_, lean_object* v_generation_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_){
_start:
{
lean_object* v_res_4176_; 
v_res_4176_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(v_goal_4162_, v_prop_4163_, v_proof_4164_, v_generation_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
lean_dec(v___y_4166_);
return v_res_4176_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(lean_object* v_goal_4177_, lean_object* v___f_4178_, lean_object* v_kp_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_){
_start:
{
lean_object* v_mvarId_4190_; lean_object* v___x_4191_; 
v_mvarId_4190_ = lean_ctor_get(v_goal_4177_, 1);
lean_inc(v_mvarId_4190_);
lean_dec_ref(v_goal_4177_);
v___x_4191_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_4190_, v___f_4178_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_);
if (lean_obj_tag(v___x_4191_) == 0)
{
lean_object* v_a_4192_; lean_object* v___x_4193_; 
v_a_4192_ = lean_ctor_get(v___x_4191_, 0);
lean_inc(v_a_4192_);
lean_dec_ref_known(v___x_4191_, 1);
lean_inc(v___y_4188_);
lean_inc_ref(v___y_4187_);
lean_inc(v___y_4186_);
lean_inc_ref(v___y_4185_);
lean_inc(v___y_4184_);
lean_inc_ref(v___y_4183_);
lean_inc(v___y_4182_);
lean_inc_ref(v___y_4181_);
lean_inc(v___y_4180_);
v___x_4193_ = lean_apply_11(v_kp_4179_, v_a_4192_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, lean_box(0));
return v___x_4193_;
}
else
{
lean_object* v_a_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4201_; 
lean_dec_ref(v_kp_4179_);
v_a_4194_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4196_ = v___x_4191_;
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_a_4194_);
lean_dec(v___x_4191_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v___x_4199_; 
if (v_isShared_4197_ == 0)
{
v___x_4199_ = v___x_4196_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_a_4194_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_4177_ = stack[0].m_obj;
lean_object* v___f_4178_ = stack[1].m_obj;
lean_object* v_kp_4179_ = stack[2].m_obj;
lean_object* v___y_4180_ = stack[3].m_obj;
lean_object* v___y_4181_ = stack[4].m_obj;
lean_object* v___y_4182_ = stack[5].m_obj;
lean_object* v___y_4183_ = stack[6].m_obj;
lean_object* v___y_4184_ = stack[7].m_obj;
lean_object* v___y_4185_ = stack[8].m_obj;
lean_object* v___y_4186_ = stack[9].m_obj;
lean_object* v___y_4187_ = stack[10].m_obj;
lean_object* v___y_4188_ = stack[11].m_obj;
lean_object* v_res_4202_;
v_res_4202_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(v_goal_4177_, v___f_4178_, v_kp_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_);
stack->m_obj
 = v_res_4202_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed(lean_object* v_goal_4203_, lean_object* v___f_4204_, lean_object* v_kp_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
lean_object* v_res_4216_; 
v_res_4216_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(v_goal_4203_, v___f_4204_, v_kp_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4207_);
lean_dec(v___y_4206_);
return v_res_4216_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(lean_object* v_proof_4217_, lean_object* v_prop_4218_, lean_object* v_generation_4219_, lean_object* v_goal_4220_, lean_object* v_kna_4221_, lean_object* v_kp_4222_, lean_object* v_a_4223_, lean_object* v_a_4224_, lean_object* v_a_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_){
_start:
{
lean_object* v___f_4233_; lean_object* v___f_4234_; lean_object* v___x_4235_; 
lean_inc(v_generation_4219_);
lean_inc_ref(v_proof_4217_);
lean_inc_ref(v_prop_4218_);
lean_inc_ref_n(v_goal_4220_, 2);
v___f_4233_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed), 14, 4);
lean_closure_set(v___f_4233_, 0, v_goal_4220_);
lean_closure_set(v___f_4233_, 1, v_prop_4218_);
lean_closure_set(v___f_4233_, 2, v_proof_4217_);
lean_closure_set(v___f_4233_, 3, v_generation_4219_);
lean_inc_ref(v_kp_4222_);
v___f_4234_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed), 13, 3);
lean_closure_set(v___f_4234_, 0, v_goal_4220_);
lean_closure_set(v___f_4234_, 1, v___f_4233_);
lean_closure_set(v___f_4234_, 2, v_kp_4222_);
v___x_4235_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_prop_4218_, v_a_4224_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v_a_4236_; uint8_t v___x_4237_; 
v_a_4236_ = lean_ctor_get(v___x_4235_, 0);
lean_inc(v_a_4236_);
lean_dec_ref_known(v___x_4235_, 1);
v___x_4237_ = lean_unbox(v_a_4236_);
lean_dec(v_a_4236_);
if (v___x_4237_ == 0)
{
lean_object* v_mvarId_4238_; lean_object* v___x_4239_; 
lean_dec_ref(v_kp_4222_);
lean_dec_ref(v_kna_4221_);
lean_dec(v_generation_4219_);
lean_dec_ref(v_prop_4218_);
lean_dec_ref(v_proof_4217_);
v_mvarId_4238_ = lean_ctor_get(v_goal_4220_, 1);
lean_inc(v_mvarId_4238_);
lean_dec_ref(v_goal_4220_);
v___x_4239_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_4238_, v___f_4234_, v_a_4223_, v_a_4224_, v_a_4225_, v_a_4226_, v_a_4227_, v_a_4228_, v_a_4229_, v_a_4230_, v_a_4231_);
return v___x_4239_;
}
else
{
lean_object* v___x_4240_; lean_object* v___x_4241_; 
lean_dec_ref(v___f_4234_);
v___x_4240_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v___x_4241_ = l_Lean_Core_mkFreshUserName(v___x_4240_, v_a_4230_, v_a_4231_);
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_object* v_a_4242_; lean_object* v_toGoalState_4243_; lean_object* v_mvarId_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4262_; 
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
lean_inc(v_a_4242_);
lean_dec_ref_known(v___x_4241_, 1);
v_toGoalState_4243_ = lean_ctor_get(v_goal_4220_, 0);
v_mvarId_4244_ = lean_ctor_get(v_goal_4220_, 1);
v_isSharedCheck_4262_ = !lean_is_exclusive(v_goal_4220_);
if (v_isSharedCheck_4262_ == 0)
{
v___x_4246_ = v_goal_4220_;
v_isShared_4247_ = v_isSharedCheck_4262_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_mvarId_4244_);
lean_inc(v_toGoalState_4243_);
lean_dec(v_goal_4220_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4262_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4248_; 
v___x_4248_ = l_Lean_MVarId_assert(v_mvarId_4244_, v_a_4242_, v_prop_4218_, v_proof_4217_, v_a_4228_, v_a_4229_, v_a_4230_, v_a_4231_);
if (lean_obj_tag(v___x_4248_) == 0)
{
lean_object* v_a_4249_; lean_object* v___x_4251_; 
v_a_4249_ = lean_ctor_get(v___x_4248_, 0);
lean_inc(v_a_4249_);
lean_dec_ref_known(v___x_4248_, 1);
if (v_isShared_4247_ == 0)
{
lean_ctor_set(v___x_4246_, 1, v_a_4249_);
v___x_4251_ = v___x_4246_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_toGoalState_4243_);
lean_ctor_set(v_reuseFailAlloc_4253_, 1, v_a_4249_);
v___x_4251_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
lean_object* v___x_4252_; 
v___x_4252_ = l_Lean_Meta_Grind_Action_intros(v_generation_4219_, v___x_4251_, v_kna_4221_, v_kp_4222_, v_a_4223_, v_a_4224_, v_a_4225_, v_a_4226_, v_a_4227_, v_a_4228_, v_a_4229_, v_a_4230_, v_a_4231_);
return v___x_4252_;
}
}
else
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4261_; 
lean_del_object(v___x_4246_);
lean_dec_ref(v_toGoalState_4243_);
lean_dec_ref(v_kp_4222_);
lean_dec_ref(v_kna_4221_);
lean_dec(v_generation_4219_);
v_a_4254_ = lean_ctor_get(v___x_4248_, 0);
v_isSharedCheck_4261_ = !lean_is_exclusive(v___x_4248_);
if (v_isSharedCheck_4261_ == 0)
{
v___x_4256_ = v___x_4248_;
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___x_4248_);
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
lean_object* v_a_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4270_; 
lean_dec_ref(v_kp_4222_);
lean_dec_ref(v_kna_4221_);
lean_dec_ref(v_goal_4220_);
lean_dec(v_generation_4219_);
lean_dec_ref(v_prop_4218_);
lean_dec_ref(v_proof_4217_);
v_a_4263_ = lean_ctor_get(v___x_4241_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4265_ = v___x_4241_;
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_a_4263_);
lean_dec(v___x_4241_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v___x_4268_; 
if (v_isShared_4266_ == 0)
{
v___x_4268_ = v___x_4265_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4263_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
}
}
}
else
{
lean_object* v_a_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4278_; 
lean_dec_ref(v___f_4234_);
lean_dec_ref(v_kp_4222_);
lean_dec_ref(v_kna_4221_);
lean_dec_ref(v_goal_4220_);
lean_dec(v_generation_4219_);
lean_dec_ref(v_prop_4218_);
lean_dec_ref(v_proof_4217_);
v_a_4271_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4273_ = v___x_4235_;
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_a_4271_);
lean_dec(v___x_4235_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4276_; 
if (v_isShared_4274_ == 0)
{
v___x_4276_ = v___x_4273_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_a_4271_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt_0interp(lean_interpreter_value* stack)
{
lean_object* v_proof_4217_ = stack[0].m_obj;
lean_object* v_prop_4218_ = stack[1].m_obj;
lean_object* v_generation_4219_ = stack[2].m_obj;
lean_object* v_goal_4220_ = stack[3].m_obj;
lean_object* v_kna_4221_ = stack[4].m_obj;
lean_object* v_kp_4222_ = stack[5].m_obj;
lean_object* v_a_4223_ = stack[6].m_obj;
lean_object* v_a_4224_ = stack[7].m_obj;
lean_object* v_a_4225_ = stack[8].m_obj;
lean_object* v_a_4226_ = stack[9].m_obj;
lean_object* v_a_4227_ = stack[10].m_obj;
lean_object* v_a_4228_ = stack[11].m_obj;
lean_object* v_a_4229_ = stack[12].m_obj;
lean_object* v_a_4230_ = stack[13].m_obj;
lean_object* v_a_4231_ = stack[14].m_obj;
lean_object* v_res_4279_;
v_res_4279_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(v_proof_4217_, v_prop_4218_, v_generation_4219_, v_goal_4220_, v_kna_4221_, v_kp_4222_, v_a_4223_, v_a_4224_, v_a_4225_, v_a_4226_, v_a_4227_, v_a_4228_, v_a_4229_, v_a_4230_, v_a_4231_);
stack->m_obj
 = v_res_4279_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___boxed(lean_object* v_proof_4280_, lean_object* v_prop_4281_, lean_object* v_generation_4282_, lean_object* v_goal_4283_, lean_object* v_kna_4284_, lean_object* v_kp_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_){
_start:
{
lean_object* v_res_4296_; 
v_res_4296_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(v_proof_4280_, v_prop_4281_, v_generation_4282_, v_goal_4283_, v_kna_4284_, v_kp_4285_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_);
lean_dec(v_a_4294_);
lean_dec_ref(v_a_4293_);
lean_dec(v_a_4292_);
lean_dec_ref(v_a_4291_);
lean_dec(v_a_4290_);
lean_dec_ref(v_a_4289_);
lean_dec(v_a_4288_);
lean_dec_ref(v_a_4287_);
lean_dec(v_a_4286_);
return v_res_4296_;
}
}
lean_object* l_Lean_Meta_Grind_Action_assertNext(lean_object* v_goal_4297_, lean_object* v_kna_4298_, lean_object* v_kp_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_){
_start:
{
lean_object* v_toGoalState_4310_; uint8_t v_inconsistent_4311_; 
v_toGoalState_4310_ = lean_ctor_get(v_goal_4297_, 0);
lean_inc_ref(v_toGoalState_4310_);
v_inconsistent_4311_ = lean_ctor_get_uint8(v_toGoalState_4310_, sizeof(void*)*17);
if (v_inconsistent_4311_ == 0)
{
lean_object* v_mvarId_4312_; lean_object* v_nextDeclIdx_4313_; lean_object* v_enodeMap_4314_; lean_object* v_exprs_4315_; lean_object* v_parents_4316_; lean_object* v_congrTable_4317_; lean_object* v_appMap_4318_; lean_object* v_indicesFound_4319_; lean_object* v_toProcess_4320_; lean_object* v_nextIdx_4321_; lean_object* v_newRawFacts_4322_; lean_object* v_facts_4323_; lean_object* v_extThms_4324_; lean_object* v_ematch_4325_; lean_object* v_inj_4326_; lean_object* v_split_4327_; lean_object* v_clean_4328_; lean_object* v_sstates_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4369_; 
v_mvarId_4312_ = lean_ctor_get(v_goal_4297_, 1);
v_nextDeclIdx_4313_ = lean_ctor_get(v_toGoalState_4310_, 0);
v_enodeMap_4314_ = lean_ctor_get(v_toGoalState_4310_, 1);
v_exprs_4315_ = lean_ctor_get(v_toGoalState_4310_, 2);
v_parents_4316_ = lean_ctor_get(v_toGoalState_4310_, 3);
v_congrTable_4317_ = lean_ctor_get(v_toGoalState_4310_, 4);
v_appMap_4318_ = lean_ctor_get(v_toGoalState_4310_, 5);
v_indicesFound_4319_ = lean_ctor_get(v_toGoalState_4310_, 6);
v_toProcess_4320_ = lean_ctor_get(v_toGoalState_4310_, 7);
v_nextIdx_4321_ = lean_ctor_get(v_toGoalState_4310_, 8);
v_newRawFacts_4322_ = lean_ctor_get(v_toGoalState_4310_, 9);
v_facts_4323_ = lean_ctor_get(v_toGoalState_4310_, 10);
v_extThms_4324_ = lean_ctor_get(v_toGoalState_4310_, 11);
v_ematch_4325_ = lean_ctor_get(v_toGoalState_4310_, 12);
v_inj_4326_ = lean_ctor_get(v_toGoalState_4310_, 13);
v_split_4327_ = lean_ctor_get(v_toGoalState_4310_, 14);
v_clean_4328_ = lean_ctor_get(v_toGoalState_4310_, 15);
v_sstates_4329_ = lean_ctor_get(v_toGoalState_4310_, 16);
v_isSharedCheck_4369_ = !lean_is_exclusive(v_toGoalState_4310_);
if (v_isSharedCheck_4369_ == 0)
{
v___x_4331_ = v_toGoalState_4310_;
v_isShared_4332_ = v_isSharedCheck_4369_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_sstates_4329_);
lean_inc(v_clean_4328_);
lean_inc(v_split_4327_);
lean_inc(v_inj_4326_);
lean_inc(v_ematch_4325_);
lean_inc(v_extThms_4324_);
lean_inc(v_facts_4323_);
lean_inc(v_newRawFacts_4322_);
lean_inc(v_nextIdx_4321_);
lean_inc(v_toProcess_4320_);
lean_inc(v_indicesFound_4319_);
lean_inc(v_appMap_4318_);
lean_inc(v_congrTable_4317_);
lean_inc(v_parents_4316_);
lean_inc(v_exprs_4315_);
lean_inc(v_enodeMap_4314_);
lean_inc(v_nextDeclIdx_4313_);
lean_dec(v_toGoalState_4310_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4369_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4333_; 
v___x_4333_ = l_Std_Queue_dequeue_x3f___redArg(v_newRawFacts_4322_);
if (lean_obj_tag(v___x_4333_) == 1)
{
lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4365_; 
lean_inc(v_mvarId_4312_);
v_isSharedCheck_4365_ = !lean_is_exclusive(v_goal_4297_);
if (v_isSharedCheck_4365_ == 0)
{
lean_object* v_unused_4366_; lean_object* v_unused_4367_; 
v_unused_4366_ = lean_ctor_get(v_goal_4297_, 1);
lean_dec(v_unused_4366_);
v_unused_4367_ = lean_ctor_get(v_goal_4297_, 0);
lean_dec(v_unused_4367_);
v___x_4335_ = v_goal_4297_;
v_isShared_4336_ = v_isSharedCheck_4365_;
goto v_resetjp_4334_;
}
else
{
lean_dec(v_goal_4297_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4365_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v_val_4337_; lean_object* v_fst_4338_; lean_object* v_snd_4339_; lean_object* v_proof_4340_; lean_object* v_prop_4341_; lean_object* v_generation_4342_; lean_object* v_splitSource_4343_; lean_object* v_ematchDiagSource_4344_; lean_object* v_simp_4345_; lean_object* v_simpMethods_4346_; lean_object* v_symSimpMethods_4347_; lean_object* v_symDSimpMethods_4348_; lean_object* v_config_4349_; lean_object* v_anchorRefs_x3f_4350_; uint8_t v_cheapCases_4351_; uint8_t v_reportMVarIssue_4352_; lean_object* v_symPrios_4353_; lean_object* v_extensions_4354_; uint8_t v_debug_4355_; uint8_t v_ematchDiag_4356_; lean_object* v___x_4358_; 
v_val_4337_ = lean_ctor_get(v___x_4333_, 0);
lean_inc(v_val_4337_);
lean_dec_ref_known(v___x_4333_, 1);
v_fst_4338_ = lean_ctor_get(v_val_4337_, 0);
lean_inc(v_fst_4338_);
v_snd_4339_ = lean_ctor_get(v_val_4337_, 1);
lean_inc(v_snd_4339_);
lean_dec(v_val_4337_);
v_proof_4340_ = lean_ctor_get(v_fst_4338_, 0);
lean_inc_ref(v_proof_4340_);
v_prop_4341_ = lean_ctor_get(v_fst_4338_, 1);
lean_inc_ref(v_prop_4341_);
v_generation_4342_ = lean_ctor_get(v_fst_4338_, 2);
lean_inc(v_generation_4342_);
v_splitSource_4343_ = lean_ctor_get(v_fst_4338_, 3);
lean_inc(v_splitSource_4343_);
v_ematchDiagSource_4344_ = lean_ctor_get(v_fst_4338_, 4);
lean_inc(v_ematchDiagSource_4344_);
lean_dec(v_fst_4338_);
v_simp_4345_ = lean_ctor_get(v_a_4301_, 0);
v_simpMethods_4346_ = lean_ctor_get(v_a_4301_, 1);
v_symSimpMethods_4347_ = lean_ctor_get(v_a_4301_, 2);
v_symDSimpMethods_4348_ = lean_ctor_get(v_a_4301_, 3);
v_config_4349_ = lean_ctor_get(v_a_4301_, 4);
v_anchorRefs_x3f_4350_ = lean_ctor_get(v_a_4301_, 5);
v_cheapCases_4351_ = lean_ctor_get_uint8(v_a_4301_, sizeof(void*)*10);
v_reportMVarIssue_4352_ = lean_ctor_get_uint8(v_a_4301_, sizeof(void*)*10 + 1);
v_symPrios_4353_ = lean_ctor_get(v_a_4301_, 8);
v_extensions_4354_ = lean_ctor_get(v_a_4301_, 9);
v_debug_4355_ = lean_ctor_get_uint8(v_a_4301_, sizeof(void*)*10 + 2);
v_ematchDiag_4356_ = lean_ctor_get_uint8(v_a_4301_, sizeof(void*)*10 + 3);
if (v_isShared_4332_ == 0)
{
lean_ctor_set(v___x_4331_, 9, v_snd_4339_);
v___x_4358_ = v___x_4331_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v_nextDeclIdx_4313_);
lean_ctor_set(v_reuseFailAlloc_4364_, 1, v_enodeMap_4314_);
lean_ctor_set(v_reuseFailAlloc_4364_, 2, v_exprs_4315_);
lean_ctor_set(v_reuseFailAlloc_4364_, 3, v_parents_4316_);
lean_ctor_set(v_reuseFailAlloc_4364_, 4, v_congrTable_4317_);
lean_ctor_set(v_reuseFailAlloc_4364_, 5, v_appMap_4318_);
lean_ctor_set(v_reuseFailAlloc_4364_, 6, v_indicesFound_4319_);
lean_ctor_set(v_reuseFailAlloc_4364_, 7, v_toProcess_4320_);
lean_ctor_set(v_reuseFailAlloc_4364_, 8, v_nextIdx_4321_);
lean_ctor_set(v_reuseFailAlloc_4364_, 9, v_snd_4339_);
lean_ctor_set(v_reuseFailAlloc_4364_, 10, v_facts_4323_);
lean_ctor_set(v_reuseFailAlloc_4364_, 11, v_extThms_4324_);
lean_ctor_set(v_reuseFailAlloc_4364_, 12, v_ematch_4325_);
lean_ctor_set(v_reuseFailAlloc_4364_, 13, v_inj_4326_);
lean_ctor_set(v_reuseFailAlloc_4364_, 14, v_split_4327_);
lean_ctor_set(v_reuseFailAlloc_4364_, 15, v_clean_4328_);
lean_ctor_set(v_reuseFailAlloc_4364_, 16, v_sstates_4329_);
lean_ctor_set_uint8(v_reuseFailAlloc_4364_, sizeof(void*)*17, v_inconsistent_4311_);
v___x_4358_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
lean_object* v_goal_4360_; 
if (v_isShared_4336_ == 0)
{
lean_ctor_set(v___x_4335_, 0, v___x_4358_);
v_goal_4360_ = v___x_4335_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v___x_4358_);
lean_ctor_set(v_reuseFailAlloc_4363_, 1, v_mvarId_4312_);
v_goal_4360_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
lean_object* v___x_4361_; lean_object* v___x_4362_; 
lean_inc_ref(v_extensions_4354_);
lean_inc_ref(v_symPrios_4353_);
lean_inc(v_anchorRefs_x3f_4350_);
lean_inc_ref(v_config_4349_);
lean_inc_ref(v_symDSimpMethods_4348_);
lean_inc_ref(v_symSimpMethods_4347_);
lean_inc_ref(v_simpMethods_4346_);
lean_inc_ref(v_simp_4345_);
v___x_4361_ = lean_alloc_ctor(0, 10, 4);
lean_ctor_set(v___x_4361_, 0, v_simp_4345_);
lean_ctor_set(v___x_4361_, 1, v_simpMethods_4346_);
lean_ctor_set(v___x_4361_, 2, v_symSimpMethods_4347_);
lean_ctor_set(v___x_4361_, 3, v_symDSimpMethods_4348_);
lean_ctor_set(v___x_4361_, 4, v_config_4349_);
lean_ctor_set(v___x_4361_, 5, v_anchorRefs_x3f_4350_);
lean_ctor_set(v___x_4361_, 6, v_splitSource_4343_);
lean_ctor_set(v___x_4361_, 7, v_ematchDiagSource_4344_);
lean_ctor_set(v___x_4361_, 8, v_symPrios_4353_);
lean_ctor_set(v___x_4361_, 9, v_extensions_4354_);
lean_ctor_set_uint8(v___x_4361_, sizeof(void*)*10, v_cheapCases_4351_);
lean_ctor_set_uint8(v___x_4361_, sizeof(void*)*10 + 1, v_reportMVarIssue_4352_);
lean_ctor_set_uint8(v___x_4361_, sizeof(void*)*10 + 2, v_debug_4355_);
lean_ctor_set_uint8(v___x_4361_, sizeof(void*)*10 + 3, v_ematchDiag_4356_);
v___x_4362_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(v_proof_4340_, v_prop_4341_, v_generation_4342_, v_goal_4360_, v_kna_4298_, v_kp_4299_, v_a_4300_, v___x_4361_, v_a_4302_, v_a_4303_, v_a_4304_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_);
lean_dec_ref_known(v___x_4361_, 10);
return v___x_4362_;
}
}
}
}
else
{
lean_object* v___x_4368_; 
lean_dec(v___x_4333_);
lean_del_object(v___x_4331_);
lean_dec_ref(v_sstates_4329_);
lean_dec_ref(v_clean_4328_);
lean_dec_ref(v_split_4327_);
lean_dec_ref(v_inj_4326_);
lean_dec_ref(v_ematch_4325_);
lean_dec_ref(v_extThms_4324_);
lean_dec_ref(v_facts_4323_);
lean_dec(v_nextIdx_4321_);
lean_dec_ref(v_toProcess_4320_);
lean_dec_ref(v_indicesFound_4319_);
lean_dec_ref(v_appMap_4318_);
lean_dec_ref(v_congrTable_4317_);
lean_dec_ref(v_parents_4316_);
lean_dec_ref(v_exprs_4315_);
lean_dec_ref(v_enodeMap_4314_);
lean_dec(v_nextDeclIdx_4313_);
lean_dec_ref(v_kp_4299_);
lean_inc(v_a_4308_);
lean_inc_ref(v_a_4307_);
lean_inc(v_a_4306_);
lean_inc_ref(v_a_4305_);
lean_inc(v_a_4304_);
lean_inc_ref(v_a_4303_);
lean_inc(v_a_4302_);
lean_inc_ref(v_a_4301_);
lean_inc(v_a_4300_);
v___x_4368_ = lean_apply_11(v_kna_4298_, v_goal_4297_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, lean_box(0));
return v___x_4368_;
}
}
}
else
{
lean_object* v___x_4370_; lean_object* v___x_4371_; 
lean_dec_ref(v_toGoalState_4310_);
lean_dec_ref(v_kp_4299_);
lean_dec_ref(v_kna_4298_);
lean_dec_ref(v_goal_4297_);
v___x_4370_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intro___closed__0));
v___x_4371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4371_, 0, v___x_4370_);
return v___x_4371_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_assertNext_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_4297_ = stack[0].m_obj;
lean_object* v_kna_4298_ = stack[1].m_obj;
lean_object* v_kp_4299_ = stack[2].m_obj;
lean_object* v_a_4300_ = stack[3].m_obj;
lean_object* v_a_4301_ = stack[4].m_obj;
lean_object* v_a_4302_ = stack[5].m_obj;
lean_object* v_a_4303_ = stack[6].m_obj;
lean_object* v_a_4304_ = stack[7].m_obj;
lean_object* v_a_4305_ = stack[8].m_obj;
lean_object* v_a_4306_ = stack[9].m_obj;
lean_object* v_a_4307_ = stack[10].m_obj;
lean_object* v_a_4308_ = stack[11].m_obj;
lean_object* v_res_4372_;
v_res_4372_ = l_Lean_Meta_Grind_Action_assertNext(v_goal_4297_, v_kna_4298_, v_kp_4299_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_);
stack->m_obj
 = v_res_4372_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext___boxed(lean_object* v_goal_4373_, lean_object* v_kna_4374_, lean_object* v_kp_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_){
_start:
{
lean_object* v_res_4386_; 
v_res_4386_ = l_Lean_Meta_Grind_Action_assertNext(v_goal_4373_, v_kna_4374_, v_kp_4375_, v_a_4376_, v_a_4377_, v_a_4378_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_);
lean_dec(v_a_4384_);
lean_dec_ref(v_a_4383_);
lean_dec(v_a_4382_);
lean_dec_ref(v_a_4381_);
lean_dec(v_a_4380_);
lean_dec_ref(v_a_4379_);
lean_dec(v_a_4378_);
lean_dec_ref(v_a_4377_);
lean_dec(v_a_4376_);
return v_res_4386_;
}
}
lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg(lean_object* v_a_4387_, lean_object* v_kp_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_){
_start:
{
lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; 
v___x_4399_ = lean_unsigned_to_nat(1000000u);
v___x_4400_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_assertNext___boxed), 13, 0);
v___x_4401_ = l_Lean_Meta_Grind_Action_loop___redArg(v___x_4399_, v___x_4400_, v_a_4387_, v_kp_4388_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_);
return v___x_4401_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_assertAll___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4387_ = stack[0].m_obj;
lean_object* v_kp_4388_ = stack[1].m_obj;
lean_object* v_a_4389_ = stack[2].m_obj;
lean_object* v_a_4390_ = stack[3].m_obj;
lean_object* v_a_4391_ = stack[4].m_obj;
lean_object* v_a_4392_ = stack[5].m_obj;
lean_object* v_a_4393_ = stack[6].m_obj;
lean_object* v_a_4394_ = stack[7].m_obj;
lean_object* v_a_4395_ = stack[8].m_obj;
lean_object* v_a_4396_ = stack[9].m_obj;
lean_object* v_a_4397_ = stack[10].m_obj;
lean_object* v_res_4402_;
v_res_4402_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4387_, v_kp_4388_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_);
stack->m_obj
 = v_res_4402_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg___boxed(lean_object* v_a_4403_, lean_object* v_kp_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_){
_start:
{
lean_object* v_res_4415_; 
v_res_4415_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4403_, v_kp_4404_, v_a_4405_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_);
lean_dec(v_a_4413_);
lean_dec_ref(v_a_4412_);
lean_dec(v_a_4411_);
lean_dec_ref(v_a_4410_);
lean_dec(v_a_4409_);
lean_dec_ref(v_a_4408_);
lean_dec(v_a_4407_);
lean_dec_ref(v_a_4406_);
lean_dec(v_a_4405_);
return v_res_4415_;
}
}
lean_object* l_Lean_Meta_Grind_Action_assertAll(lean_object* v_a_4416_, lean_object* v_kna_4417_, lean_object* v_kp_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_){
_start:
{
lean_object* v___x_4429_; 
v___x_4429_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4416_, v_kp_4418_, v_a_4419_, v_a_4420_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_, v_a_4427_);
return v___x_4429_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_assertAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4416_ = stack[0].m_obj;
lean_object* v_kna_4417_ = stack[1].m_obj;
lean_object* v_kp_4418_ = stack[2].m_obj;
lean_object* v_a_4419_ = stack[3].m_obj;
lean_object* v_a_4420_ = stack[4].m_obj;
lean_object* v_a_4421_ = stack[5].m_obj;
lean_object* v_a_4422_ = stack[6].m_obj;
lean_object* v_a_4423_ = stack[7].m_obj;
lean_object* v_a_4424_ = stack[8].m_obj;
lean_object* v_a_4425_ = stack[9].m_obj;
lean_object* v_a_4426_ = stack[10].m_obj;
lean_object* v_a_4427_ = stack[11].m_obj;
lean_object* v_res_4430_;
v_res_4430_ = l_Lean_Meta_Grind_Action_assertAll(v_a_4416_, v_kna_4417_, v_kp_4418_, v_a_4419_, v_a_4420_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_, v_a_4427_);
stack->m_obj
 = v_res_4430_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___boxed(lean_object* v_a_4431_, lean_object* v_kna_4432_, lean_object* v_kp_4433_, lean_object* v_a_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_){
_start:
{
lean_object* v_res_4444_; 
v_res_4444_ = l_Lean_Meta_Grind_Action_assertAll(v_a_4431_, v_kna_4432_, v_kp_4433_, v_a_4434_, v_a_4435_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_);
lean_dec(v_a_4442_);
lean_dec_ref(v_a_4441_);
lean_dec(v_a_4440_);
lean_dec_ref(v_a_4439_);
lean_dec(v_a_4438_);
lean_dec_ref(v_a_4437_);
lean_dec(v_a_4436_);
lean_dec_ref(v_a_4435_);
lean_dec(v_a_4434_);
lean_dec_ref(v_kna_4432_);
return v_res_4444_;
}
}
lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__0(lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_){
_start:
{
lean_object* v___x_4458_; 
v___x_4458_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_4445_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
return v___x_4458_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Solvers_mkAction___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4445_ = stack[0].m_obj;
lean_object* v___y_4446_ = stack[1].m_obj;
lean_object* v___y_4447_ = stack[2].m_obj;
lean_object* v___y_4448_ = stack[3].m_obj;
lean_object* v___y_4449_ = stack[4].m_obj;
lean_object* v___y_4450_ = stack[5].m_obj;
lean_object* v___y_4451_ = stack[6].m_obj;
lean_object* v___y_4452_ = stack[7].m_obj;
lean_object* v___y_4453_ = stack[8].m_obj;
lean_object* v___y_4454_ = stack[9].m_obj;
lean_object* v___y_4455_ = stack[10].m_obj;
lean_object* v___y_4456_ = stack[11].m_obj;
lean_object* v_res_4459_;
v_res_4459_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__0(v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
stack->m_obj
 = v_res_4459_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__0___boxed(lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_){
_start:
{
lean_object* v_res_4473_; 
v_res_4473_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__0(v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_);
lean_dec(v___y_4471_);
lean_dec_ref(v___y_4470_);
lean_dec(v___y_4469_);
lean_dec_ref(v___y_4468_);
lean_dec(v___y_4467_);
lean_dec_ref(v___y_4466_);
lean_dec(v___y_4465_);
lean_dec_ref(v___y_4464_);
lean_dec(v___y_4463_);
lean_dec_ref(v___y_4461_);
return v_res_4473_;
}
}
lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__1(lean_object* v_a_4474_, lean_object* v___f_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_){
_start:
{
lean_object* v___x_4489_; 
v___x_4489_ = l_Lean_Meta_Grind_Action_andThen(v_a_4474_, v___f_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_);
return v___x_4489_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Solvers_mkAction___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4474_ = stack[0].m_obj;
lean_object* v___f_4475_ = stack[1].m_obj;
lean_object* v___y_4476_ = stack[2].m_obj;
lean_object* v___y_4477_ = stack[3].m_obj;
lean_object* v___y_4478_ = stack[4].m_obj;
lean_object* v___y_4479_ = stack[5].m_obj;
lean_object* v___y_4480_ = stack[6].m_obj;
lean_object* v___y_4481_ = stack[7].m_obj;
lean_object* v___y_4482_ = stack[8].m_obj;
lean_object* v___y_4483_ = stack[9].m_obj;
lean_object* v___y_4484_ = stack[10].m_obj;
lean_object* v___y_4485_ = stack[11].m_obj;
lean_object* v___y_4486_ = stack[12].m_obj;
lean_object* v___y_4487_ = stack[13].m_obj;
lean_object* v_res_4490_;
v_res_4490_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__1(v_a_4474_, v___f_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_);
stack->m_obj
 = v_res_4490_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed(lean_object* v_a_4491_, lean_object* v___f_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__1(v_a_4491_, v___f_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
lean_dec(v___y_4504_);
lean_dec_ref(v___y_4503_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
lean_dec(v___y_4496_);
return v_res_4506_;
}
}
lean_object* l_Lean_Meta_Grind_Solvers_mkAction(){
_start:
{
lean_object* v___f_4509_; lean_object* v___x_4510_; 
v___f_4509_ = ((lean_object*)(l_Lean_Meta_Grind_Solvers_mkAction___closed__0));
v___x_4510_ = l_Lean_Meta_Grind_Solvers_mkActionCore();
if (lean_obj_tag(v___x_4510_) == 0)
{
lean_object* v_a_4511_; lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4519_; 
v_a_4511_ = lean_ctor_get(v___x_4510_, 0);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4510_);
if (v_isSharedCheck_4519_ == 0)
{
v___x_4513_ = v___x_4510_;
v_isShared_4514_ = v_isSharedCheck_4519_;
goto v_resetjp_4512_;
}
else
{
lean_inc(v_a_4511_);
lean_dec(v___x_4510_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4519_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v___f_4515_; lean_object* v___x_4517_; 
v___f_4515_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed), 15, 2);
lean_closure_set(v___f_4515_, 0, v_a_4511_);
lean_closure_set(v___f_4515_, 1, v___f_4509_);
if (v_isShared_4514_ == 0)
{
lean_ctor_set(v___x_4513_, 0, v___f_4515_);
v___x_4517_ = v___x_4513_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v___f_4515_);
v___x_4517_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
return v___x_4517_;
}
}
}
else
{
return v___x_4510_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Solvers_mkAction_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4520_;
v_res_4520_ = l_Lean_Meta_Grind_Solvers_mkAction();
stack->m_obj
 = v_res_4520_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___boxed(lean_object* v_a_4521_){
_start:
{
lean_object* v_res_4522_; 
v_res_4522_ = l_Lean_Meta_Grind_Solvers_mkAction();
return v_res_4522_;
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
