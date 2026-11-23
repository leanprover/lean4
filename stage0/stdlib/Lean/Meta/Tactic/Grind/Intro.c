// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Intro
// Imports: public import Init.Grind.Lemmas public import Lean.Meta.Tactic.Grind.Action import Lean.Meta.Tactic.Apply import Lean.Meta.Tactic.Grind.Util import Lean.Meta.Tactic.Grind.CasesMatch import Lean.Meta.Tactic.Grind.Injection import Lean.Meta.Tactic.Grind.Core import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.MarkAccessible import Lean.Meta.Tactic.Grind.Anchor import Init.Data.List.MapIdx import Init.Grind.Util
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_Queue_dequeue_x3f___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_getAnchor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_setIntroBase(lean_object*, uint64_t);
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
lean_object* l_Lean_Meta_Grind_registerFVarAnchor___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_value(lean_object*, uint8_t);
uint8_t l_Lean_Meta_Grind_isMatchCondCandidate(lean_object*);
uint8_t l_Lean_Expr_isBVar(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
lean_object* l_Lean_Meta_Grind_isInterpreted(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_byContra_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_injection_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markCaseSplitAsResolved(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getAnchor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_saveCases___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isBuiltinEagerCases(lean_object*);
lean_object* l_Lean_Meta_Grind_cheapCasesOnly___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Int8"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int16"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int32"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__4_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int64"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__6_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__7_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__4_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__5_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPatternLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPatternLitValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__0;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__1_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__2_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mpr_prop"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(169, 177, 76, 157, 211, 15, 217, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(lean_object*, uint8_t, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
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
lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_74_ = l_Lean_Expr_appFnCleanup___redArg(v___x_71_);
v___x_75_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3));
v___x_76_ = l_Lean_Expr_isConstOf(v___x_74_, v___x_75_);
lean_dec_ref(v___x_74_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; 
lean_dec_ref(v___x_71_);
v___x_77_ = lean_box(0);
return v___x_77_;
}
else
{
lean_object* v_arg_78_; lean_object* v___x_79_; 
v_arg_78_ = lean_ctor_get(v___x_71_, 1);
lean_inc_ref(v_arg_78_);
lean_dec_ref(v___x_71_);
v___x_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_79_, 0, v_arg_78_);
return v___x_79_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___boxed(lean_object* v_e_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f(v_e_80_);
lean_dec_ref(v_e_80_);
return v_res_81_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType(lean_object* v_type_94_){
_start:
{
lean_object* v_type_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v_type_95_ = l_Lean_Expr_consumeMData(v_type_94_);
v___x_96_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__1));
v___x_97_ = l_Lean_Expr_isConstOf(v_type_95_, v___x_96_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__3));
v___x_99_ = l_Lean_Expr_isConstOf(v_type_95_, v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__5));
v___x_101_ = l_Lean_Expr_isConstOf(v_type_95_, v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___closed__7));
v___x_103_ = l_Lean_Expr_isConstOf(v_type_95_, v___x_102_);
lean_dec_ref(v_type_95_);
return v___x_103_;
}
else
{
lean_dec_ref(v_type_95_);
return v___x_101_;
}
}
else
{
lean_dec_ref(v_type_95_);
return v___x_99_;
}
}
else
{
lean_dec_ref(v_type_95_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType___boxed(lean_object* v_type_104_){
_start:
{
uint8_t v_res_105_; lean_object* v_r_106_; 
v_res_105_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType(v_type_104_);
lean_dec_ref(v_type_104_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue(lean_object* v_e_117_){
_start:
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = l_Lean_Expr_cleanupAnnotations(v_e_117_);
v___x_119_ = l_Lean_Expr_isApp(v___x_118_);
if (v___x_119_ == 0)
{
lean_dec_ref(v___x_118_);
return v___x_119_;
}
else
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = l_Lean_Expr_appFnCleanup___redArg(v___x_118_);
v___x_121_ = l_Lean_Expr_isApp(v___x_120_);
if (v___x_121_ == 0)
{
lean_dec_ref(v___x_120_);
lean_dec_ref(v___x_118_);
return v___x_121_;
}
else
{
lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_122_ = l_Lean_Expr_appFnCleanup___redArg(v___x_120_);
v___x_123_ = l_Lean_Expr_isApp(v___x_122_);
if (v___x_123_ == 0)
{
lean_dec_ref(v___x_122_);
lean_dec_ref(v___x_120_);
lean_dec_ref(v___x_118_);
return v___x_123_;
}
else
{
lean_object* v_arg_124_; lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v_arg_124_ = lean_ctor_get(v___x_122_, 1);
lean_inc_ref(v_arg_124_);
v___x_125_ = l_Lean_Expr_appFnCleanup___redArg(v___x_122_);
lean_dec_ref(v___x_122_);
v___x_126_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__2));
v___x_127_ = l_Lean_Expr_isConstOf(v___x_125_, v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; uint8_t v___x_129_; 
lean_dec_ref(v___x_118_);
v___x_128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__5));
v___x_129_ = l_Lean_Expr_isConstOf(v___x_125_, v___x_128_);
lean_dec_ref(v___x_125_);
if (v___x_129_ == 0)
{
lean_dec_ref(v_arg_124_);
lean_dec_ref(v___x_120_);
return v___x_129_;
}
else
{
uint8_t v___x_130_; 
v___x_130_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType(v_arg_124_);
lean_dec_ref(v_arg_124_);
if (v___x_130_ == 0)
{
lean_dec_ref(v___x_120_);
return v___x_130_;
}
else
{
lean_object* v_arg_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v_arg_131_ = lean_ctor_get(v___x_120_, 1);
lean_inc_ref(v_arg_131_);
lean_dec_ref(v___x_120_);
v___x_132_ = l_Lean_Expr_consumeMData(v_arg_131_);
lean_dec_ref(v_arg_131_);
v___x_133_ = l_Lean_Expr_isRawNatLit(v___x_132_);
lean_dec_ref(v___x_132_);
return v___x_133_;
}
}
}
else
{
lean_object* v_arg_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
lean_dec_ref(v___x_125_);
lean_dec_ref(v___x_120_);
v_arg_134_ = lean_ctor_get(v___x_118_, 1);
lean_inc_ref(v_arg_134_);
lean_dec_ref(v___x_118_);
v___x_135_ = l_Lean_Expr_cleanupAnnotations(v_arg_134_);
lean_dec_ref(v_arg_134_);
v___x_136_ = l_Lean_Expr_isApp(v___x_135_);
if (v___x_136_ == 0)
{
lean_dec_ref(v___x_135_);
lean_dec_ref(v_arg_124_);
return v___x_136_;
}
else
{
lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_137_ = l_Lean_Expr_appFnCleanup___redArg(v___x_135_);
lean_dec_ref(v___x_135_);
v___x_138_ = l_Lean_Expr_isApp(v___x_137_);
if (v___x_138_ == 0)
{
lean_dec_ref(v___x_137_);
lean_dec_ref(v_arg_124_);
return v___x_138_;
}
else
{
lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_139_ = l_Lean_Expr_appFnCleanup___redArg(v___x_137_);
v___x_140_ = l_Lean_Expr_isApp(v___x_139_);
if (v___x_140_ == 0)
{
lean_dec_ref(v___x_139_);
lean_dec_ref(v___x_137_);
lean_dec_ref(v_arg_124_);
return v___x_140_;
}
else
{
lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_141_ = l_Lean_Expr_appFnCleanup___redArg(v___x_139_);
v___x_142_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___closed__5));
v___x_143_ = l_Lean_Expr_isConstOf(v___x_141_, v___x_142_);
lean_dec_ref(v___x_141_);
if (v___x_143_ == 0)
{
lean_dec_ref(v___x_139_);
lean_dec_ref(v___x_137_);
lean_dec_ref(v_arg_124_);
return v___x_143_;
}
else
{
lean_object* v_arg_144_; lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v_arg_144_ = lean_ctor_get(v___x_139_, 1);
lean_inc_ref(v_arg_144_);
lean_dec_ref(v___x_139_);
v___x_145_ = l_Lean_Expr_consumeMData(v_arg_124_);
v___x_146_ = l_Lean_Expr_consumeMData(v_arg_144_);
lean_dec_ref(v_arg_144_);
v___x_147_ = lean_expr_eqv(v___x_145_, v___x_146_);
lean_dec_ref(v___x_146_);
lean_dec_ref(v___x_145_);
if (v___x_147_ == 0)
{
lean_dec_ref(v___x_137_);
lean_dec_ref(v_arg_124_);
return v___x_147_;
}
else
{
uint8_t v___x_148_; 
v___x_148_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue_isSIntType(v_arg_124_);
lean_dec_ref(v_arg_124_);
if (v___x_148_ == 0)
{
lean_dec_ref(v___x_137_);
return v___x_148_;
}
else
{
lean_object* v_arg_149_; lean_object* v___x_150_; uint8_t v___x_151_; 
v_arg_149_ = lean_ctor_get(v___x_137_, 1);
lean_inc_ref(v_arg_149_);
lean_dec_ref(v___x_137_);
v___x_150_ = l_Lean_Expr_consumeMData(v_arg_149_);
lean_dec_ref(v_arg_149_);
v___x_151_ = l_Lean_Expr_isRawNatLit(v___x_150_);
lean_dec_ref(v___x_150_);
return v___x_151_;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue___boxed(lean_object* v_e_152_){
_start:
{
uint8_t v_res_153_; lean_object* v_r_154_; 
v_res_153_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue(v_e_152_);
lean_dec_ref(v_e_152_);
v_r_154_ = lean_box(v_res_153_);
return v_r_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPatternLitValue(lean_object* v_e_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
uint8_t v___x_165_; 
v___x_165_ = l_Lean_Expr_hasLooseBVars(v_e_155_);
if (v___x_165_ == 0)
{
uint8_t v___x_166_; 
v___x_166_ = l_Lean_Expr_isTrue(v_e_155_);
if (v___x_166_ == 0)
{
uint8_t v___x_167_; 
v___x_167_ = l_Lean_Expr_isFalse(v_e_155_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; 
lean_inc_ref(v_e_155_);
v___x_168_ = l_Lean_Meta_Grind_isInterpreted(v_e_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; uint8_t v___x_170_; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
v___x_170_ = lean_unbox(v_a_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_179_; 
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_179_ == 0)
{
lean_object* v_unused_180_; 
v_unused_180_ = lean_ctor_get(v___x_168_, 0);
lean_dec(v_unused_180_);
v___x_172_ = v___x_168_;
v_isShared_173_ = v_isSharedCheck_179_;
goto v_resetjp_171_;
}
else
{
lean_dec(v___x_168_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_179_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
uint8_t v___x_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_174_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue(v_e_155_);
lean_dec_ref(v_e_155_);
v___x_175_ = lean_box(v___x_174_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_175_);
v___x_177_ = v___x_172_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
else
{
lean_dec_ref(v_e_155_);
return v___x_168_;
}
}
else
{
lean_dec_ref(v_e_155_);
return v___x_168_;
}
}
else
{
lean_dec_ref(v_e_155_);
goto v___jp_161_;
}
}
else
{
lean_dec_ref(v_e_155_);
goto v___jp_161_;
}
}
else
{
lean_dec_ref(v_e_155_);
goto v___jp_161_;
}
v___jp_161_:
{
uint8_t v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = 0;
v___x_163_ = lean_box(v___x_162_);
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPatternLitValue___boxed(lean_object* v_e_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPatternLitValue(v_e_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_);
lean_dec(v_a_185_);
lean_dec_ref(v_a_184_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
return v_res_187_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__0(void){
_start:
{
lean_object* v___x_191_; lean_object* v_dummy_192_; 
v___x_191_ = lean_box(0);
v_dummy_192_ = l_Lean_Expr_sort___override(v___x_191_);
return v_dummy_192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern(lean_object* v_e_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
lean_object* v___x_204_; uint8_t v___x_205_; uint8_t v___x_206_; 
v___x_204_ = l_Lean_Expr_getAppFn(v_e_198_);
v___x_205_ = l_Lean_Expr_isBVar(v___x_204_);
v___x_206_ = 1;
if (v___x_205_ == 0)
{
lean_object* v___x_207_; 
lean_inc_ref(v_e_198_);
v___x_207_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPatternLitValue(v_e_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_314_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_314_ == 0)
{
v___x_210_ = v___x_207_;
v_isShared_211_ = v_isSharedCheck_314_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_207_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_314_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; uint8_t v___x_272_; 
v___x_272_ = lean_unbox(v_a_208_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; 
lean_inc_ref(v_e_198_);
v___x_273_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_198_, v_a_200_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_303_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_303_ == 0)
{
v___x_276_ = v___x_273_;
v_isShared_277_ = v_isSharedCheck_303_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_273_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_303_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_278_ = l_Lean_Expr_cleanupAnnotations(v_a_274_);
lean_dec(v_a_274_);
v___x_279_ = l_Lean_Expr_isApp(v___x_278_);
if (v___x_279_ == 0)
{
lean_dec_ref(v___x_278_);
lean_del_object(v___x_276_);
v___y_213_ = v_a_199_;
v___y_214_ = v_a_200_;
v___y_215_ = v_a_201_;
v___y_216_ = v_a_202_;
goto v___jp_212_;
}
else
{
lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_280_ = l_Lean_Expr_appFnCleanup___redArg(v___x_278_);
v___x_281_ = l_Lean_Expr_isApp(v___x_280_);
if (v___x_281_ == 0)
{
lean_dec_ref(v___x_280_);
lean_dec_ref(v___x_278_);
lean_del_object(v___x_276_);
v___y_213_ = v_a_199_;
v___y_214_ = v_a_200_;
v___y_215_ = v_a_201_;
v___y_216_ = v_a_202_;
goto v___jp_212_;
}
else
{
lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_282_ = l_Lean_Expr_appFnCleanup___redArg(v___x_280_);
v___x_283_ = l_Lean_Expr_isApp(v___x_282_);
if (v___x_283_ == 0)
{
lean_dec_ref(v___x_282_);
lean_dec_ref(v___x_280_);
lean_dec_ref(v___x_278_);
lean_del_object(v___x_276_);
v___y_213_ = v_a_199_;
v___y_214_ = v_a_200_;
v___y_215_ = v_a_201_;
v___y_216_ = v_a_202_;
goto v___jp_212_;
}
else
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = l_Lean_Expr_appFnCleanup___redArg(v___x_282_);
lean_dec_ref(v___x_282_);
v___x_285_ = l_Lean_Expr_isApp(v___x_284_);
if (v___x_285_ == 0)
{
lean_dec_ref(v___x_284_);
lean_dec_ref(v___x_280_);
lean_dec_ref(v___x_278_);
lean_del_object(v___x_276_);
v___y_213_ = v_a_199_;
v___y_214_ = v_a_200_;
v___y_215_ = v_a_201_;
v___y_216_ = v_a_202_;
goto v___jp_212_;
}
else
{
lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = l_Lean_Expr_appFnCleanup___redArg(v___x_284_);
lean_dec_ref(v___x_284_);
v___x_287_ = l_Lean_Expr_isApp(v___x_286_);
if (v___x_287_ == 0)
{
lean_dec_ref(v___x_286_);
lean_dec_ref(v___x_280_);
lean_dec_ref(v___x_278_);
lean_del_object(v___x_276_);
v___y_213_ = v_a_199_;
v___y_214_ = v_a_200_;
v___y_215_ = v_a_201_;
v___y_216_ = v_a_202_;
goto v___jp_212_;
}
else
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = l_Lean_Expr_appFnCleanup___redArg(v___x_286_);
lean_dec_ref(v___x_286_);
v___x_289_ = l_Lean_Expr_isApp(v___x_288_);
if (v___x_289_ == 0)
{
lean_dec_ref(v___x_288_);
lean_dec_ref(v___x_280_);
lean_dec_ref(v___x_278_);
lean_del_object(v___x_276_);
v___y_213_ = v_a_199_;
v___y_214_ = v_a_200_;
v___y_215_ = v_a_201_;
v___y_216_ = v_a_202_;
goto v___jp_212_;
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_290_ = l_Lean_Expr_appFnCleanup___redArg(v___x_288_);
lean_dec_ref(v___x_288_);
v___x_291_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__3));
v___x_292_ = l_Lean_Expr_isConstOf(v___x_290_, v___x_291_);
lean_dec_ref(v___x_290_);
if (v___x_292_ == 0)
{
lean_dec_ref(v___x_280_);
lean_dec_ref(v___x_278_);
lean_del_object(v___x_276_);
v___y_213_ = v_a_199_;
v___y_214_ = v_a_200_;
v___y_215_ = v_a_201_;
v___y_216_ = v_a_202_;
goto v___jp_212_;
}
else
{
lean_object* v_arg_293_; uint8_t v___x_294_; 
lean_del_object(v___x_210_);
lean_dec_ref(v___x_204_);
lean_dec_ref(v_e_198_);
v_arg_293_ = lean_ctor_get(v___x_278_, 1);
lean_inc_ref(v_arg_293_);
lean_dec_ref(v___x_278_);
v___x_294_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isSIntPatternLitValue(v_arg_293_);
if (v___x_294_ == 0)
{
lean_object* v_arg_295_; lean_object* v___x_296_; 
lean_del_object(v___x_276_);
lean_dec(v_a_208_);
v_arg_295_ = lean_ctor_get(v___x_280_, 1);
lean_inc_ref(v_arg_295_);
lean_dec_ref(v___x_280_);
v___x_296_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPatternLitValue(v_arg_293_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; uint8_t v___x_298_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
v___x_298_ = lean_unbox(v_a_297_);
if (v___x_298_ == 0)
{
lean_dec_ref(v_arg_295_);
return v___x_296_;
}
else
{
lean_dec_ref_known(v___x_296_, 1);
v_e_198_ = v_arg_295_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_295_);
return v___x_296_;
}
}
else
{
lean_object* v___x_301_; 
lean_dec_ref(v_arg_293_);
lean_dec_ref(v___x_280_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v_a_208_);
v___x_301_ = v___x_276_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_208_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
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
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
lean_del_object(v___x_210_);
lean_dec(v_a_208_);
lean_dec_ref(v___x_204_);
lean_dec_ref(v_e_198_);
v_a_304_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v___x_273_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_273_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_304_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; 
lean_del_object(v___x_210_);
lean_dec(v_a_208_);
lean_dec_ref(v___x_204_);
lean_dec_ref(v_e_198_);
v___x_312_ = lean_box(v___x_206_);
v___x_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
v___jp_212_:
{
if (lean_obj_tag(v___x_204_) == 4)
{
lean_object* v_declName_217_; lean_object* v___x_218_; lean_object* v_env_219_; uint8_t v___x_220_; lean_object* v___x_221_; 
v_declName_217_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_declName_217_);
lean_dec_ref_known(v___x_204_, 2);
v___x_218_ = lean_st_ref_get(v___y_216_);
v_env_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc_ref(v_env_219_);
lean_dec(v___x_218_);
v___x_220_ = lean_unbox(v_a_208_);
v___x_221_ = l_Lean_Environment_find_x3f(v_env_219_, v_declName_217_, v___x_220_);
if (lean_obj_tag(v___x_221_) == 1)
{
lean_object* v_val_222_; 
v_val_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_val_222_);
lean_dec_ref_known(v___x_221_, 1);
if (lean_obj_tag(v_val_222_) == 6)
{
lean_object* v_val_223_; lean_object* v_numParams_224_; lean_object* v_numFields_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
lean_dec(v_a_208_);
v_val_223_ = lean_ctor_get(v_val_222_, 0);
lean_inc_ref(v_val_223_);
lean_dec_ref_known(v_val_222_, 1);
v_numParams_224_ = lean_ctor_get(v_val_223_, 3);
lean_inc(v_numParams_224_);
v_numFields_225_ = lean_ctor_get(v_val_223_, 4);
lean_inc(v_numFields_225_);
lean_dec_ref(v_val_223_);
v___x_226_ = l_Lean_Expr_getAppNumArgs(v_e_198_);
v___x_227_ = lean_nat_add(v_numParams_224_, v_numFields_225_);
lean_dec(v_numFields_225_);
v___x_228_ = lean_nat_dec_eq(v___x_226_, v___x_227_);
lean_dec(v___x_227_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; lean_object* v___x_231_; 
lean_dec(v___x_226_);
lean_dec(v_numParams_224_);
lean_dec_ref(v_e_198_);
v___x_229_ = lean_box(v___x_228_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 0, v___x_229_);
v___x_231_ = v___x_210_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
else
{
lean_object* v_dummy_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
lean_del_object(v___x_210_);
v_dummy_233_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__0, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___closed__0);
lean_inc(v___x_226_);
v___x_234_ = lean_mk_array(v___x_226_, v_dummy_233_);
v___x_235_ = lean_unsigned_to_nat(1u);
v___x_236_ = lean_nat_sub(v___x_226_, v___x_235_);
lean_dec(v___x_226_);
v___x_237_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_198_, v___x_234_, v___x_236_);
v___x_238_ = lean_array_get_size(v___x_237_);
v___x_239_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___redArg___closed__0));
v___x_240_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___redArg(v___x_238_, v___x_237_, v_numParams_224_, v___x_239_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
lean_dec_ref(v___x_237_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_254_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_254_ == 0)
{
v___x_243_ = v___x_240_;
v_isShared_244_ = v_isSharedCheck_254_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_240_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_254_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v_fst_245_; 
v_fst_245_ = lean_ctor_get(v_a_241_, 0);
lean_inc(v_fst_245_);
lean_dec(v_a_241_);
if (lean_obj_tag(v_fst_245_) == 0)
{
lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_246_ = lean_box(v___x_206_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v___x_246_);
v___x_248_ = v___x_243_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
else
{
lean_object* v_val_250_; lean_object* v___x_252_; 
v_val_250_ = lean_ctor_get(v_fst_245_, 0);
lean_inc(v_val_250_);
lean_dec_ref_known(v_fst_245_, 1);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v_val_250_);
v___x_252_ = v___x_243_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_val_250_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
else
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
v_a_255_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_240_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_240_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
}
else
{
lean_object* v___x_264_; 
lean_dec(v_val_222_);
lean_dec_ref(v_e_198_);
if (v_isShared_211_ == 0)
{
v___x_264_ = v___x_210_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_208_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
else
{
lean_object* v___x_267_; 
lean_dec(v___x_221_);
lean_dec_ref(v_e_198_);
if (v_isShared_211_ == 0)
{
v___x_267_ = v___x_210_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_208_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
else
{
lean_object* v___x_270_; 
lean_dec_ref(v___x_204_);
lean_dec_ref(v_e_198_);
if (v_isShared_211_ == 0)
{
v___x_270_ = v___x_210_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_208_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_204_);
lean_dec_ref(v_e_198_);
return v___x_207_;
}
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec_ref(v___x_204_);
lean_dec_ref(v_e_198_);
v___x_315_ = lean_box(v___x_206_);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___redArg(lean_object* v_upperBound_317_, lean_object* v___x_318_, lean_object* v_a_319_, lean_object* v_b_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
uint8_t v___x_326_; 
v___x_326_ = lean_nat_dec_lt(v_a_319_, v_upperBound_317_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; 
lean_dec(v_a_319_);
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v_b_320_);
return v___x_327_;
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec_ref(v_b_320_);
v___x_328_ = l_Lean_instInhabitedExpr;
v___x_329_ = lean_box(0);
v___x_330_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___redArg___closed__0));
v___x_331_ = lean_array_get_borrowed(v___x_328_, v___x_318_, v_a_319_);
lean_inc(v___x_331_);
v___x_332_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern(v___x_331_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_346_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_346_ == 0)
{
v___x_335_ = v___x_332_;
v_isShared_336_ = v_isSharedCheck_346_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_332_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_346_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
uint8_t v___x_337_; 
v___x_337_ = lean_unbox(v_a_333_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_341_; 
lean_dec(v_a_319_);
v___x_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_338_, 0, v_a_333_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_329_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_339_);
v___x_341_ = v___x_335_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; 
lean_del_object(v___x_335_);
lean_dec(v_a_333_);
v___x_343_ = lean_unsigned_to_nat(1u);
v___x_344_ = lean_nat_add(v_a_319_, v___x_343_);
lean_dec(v_a_319_);
v_a_319_ = v___x_344_;
v_b_320_ = v___x_330_;
goto _start;
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec(v_a_319_);
v_a_347_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_332_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_332_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___redArg___boxed(lean_object* v_upperBound_355_, lean_object* v___x_356_, lean_object* v_a_357_, lean_object* v_b_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___redArg(v_upperBound_355_, v___x_356_, v_a_357_, v_b_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec_ref(v___x_356_);
lean_dec(v_upperBound_355_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern___boxed(lean_object* v_e_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern(v_e_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0(lean_object* v_upperBound_372_, lean_object* v___x_373_, lean_object* v_inst_374_, lean_object* v_R_375_, lean_object* v_a_376_, lean_object* v_b_377_, lean_object* v_c_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___redArg(v_upperBound_372_, v___x_373_, v_a_376_, v_b_377_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0___boxed(lean_object* v_upperBound_385_, lean_object* v___x_386_, lean_object* v_inst_387_, lean_object* v_R_388_, lean_object* v_a_389_, lean_object* v_b_390_, lean_object* v_c_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern_spec__0(v_upperBound_385_, v___x_386_, v_inst_387_, v_R_388_, v_a_389_, v_b_390_, v_c_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec_ref(v___x_386_);
lean_dec(v_upperBound_385_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go(lean_object* v_e_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
if (lean_obj_tag(v_e_404_) == 7)
{
lean_object* v_binderType_410_; lean_object* v_body_411_; lean_object* v_rhs_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v___x_422_; 
v_binderType_410_ = lean_ctor_get(v_e_404_, 1);
lean_inc_ref(v_binderType_410_);
v_body_411_ = lean_ctor_get(v_e_404_, 2);
lean_inc_ref(v_body_411_);
lean_dec_ref_known(v_e_404_, 3);
v___x_422_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_410_, v_a_406_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_a_423_);
lean_dec_ref_known(v___x_422_, 1);
v___x_424_ = l_Lean_Expr_cleanupAnnotations(v_a_423_);
lean_dec(v_a_423_);
v___x_425_ = l_Lean_Expr_isApp(v___x_424_);
if (v___x_425_ == 0)
{
lean_dec_ref(v___x_424_);
v_e_404_ = v_body_411_;
goto _start;
}
else
{
lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_427_ = l_Lean_Expr_appFnCleanup___redArg(v___x_424_);
v___x_428_ = l_Lean_Expr_isApp(v___x_427_);
if (v___x_428_ == 0)
{
lean_dec_ref(v___x_427_);
lean_dec_ref(v___x_424_);
v_e_404_ = v_body_411_;
goto _start;
}
else
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = l_Lean_Expr_appFnCleanup___redArg(v___x_427_);
lean_dec_ref(v___x_427_);
v___x_431_ = l_Lean_Expr_isApp(v___x_430_);
if (v___x_431_ == 0)
{
lean_dec_ref(v___x_430_);
lean_dec_ref(v___x_424_);
v_e_404_ = v_body_411_;
goto _start;
}
else
{
lean_object* v_arg_433_; lean_object* v___x_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v_arg_433_ = lean_ctor_get(v___x_424_, 1);
lean_inc_ref(v_arg_433_);
lean_dec_ref(v___x_424_);
v___x_434_ = l_Lean_Expr_appFnCleanup___redArg(v___x_430_);
lean_dec_ref(v___x_430_);
v___x_435_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__1));
v___x_436_ = l_Lean_Expr_isConstOf(v___x_434_, v___x_435_);
if (v___x_436_ == 0)
{
uint8_t v___x_437_; 
v___x_437_ = l_Lean_Expr_isApp(v___x_434_);
if (v___x_437_ == 0)
{
lean_dec_ref(v___x_434_);
lean_dec_ref(v_arg_433_);
v_e_404_ = v_body_411_;
goto _start;
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_439_ = l_Lean_Expr_appFnCleanup___redArg(v___x_434_);
lean_dec_ref(v___x_434_);
v___x_440_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___closed__3));
v___x_441_ = l_Lean_Expr_isConstOf(v___x_439_, v___x_440_);
lean_dec_ref(v___x_439_);
if (v___x_441_ == 0)
{
lean_dec_ref(v_arg_433_);
v_e_404_ = v_body_411_;
goto _start;
}
else
{
v_rhs_413_ = v_arg_433_;
v___y_414_ = v_a_405_;
v___y_415_ = v_a_406_;
v___y_416_ = v_a_407_;
v___y_417_ = v_a_408_;
goto v___jp_412_;
}
}
}
else
{
lean_dec_ref(v___x_434_);
v_rhs_413_ = v_arg_433_;
v___y_414_ = v_a_405_;
v___y_415_ = v_a_406_;
v___y_416_ = v_a_407_;
v___y_417_ = v_a_408_;
goto v___jp_412_;
}
}
}
}
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_dec_ref(v_body_411_);
v_a_443_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_422_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_422_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
v___jp_412_:
{
lean_object* v___x_418_; 
v___x_418_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isPattern(v_rhs_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; uint8_t v___x_420_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
v___x_420_ = lean_unbox(v_a_419_);
if (v___x_420_ == 0)
{
lean_dec_ref(v_body_411_);
return v___x_418_;
}
else
{
lean_dec_ref_known(v___x_418_, 1);
v_e_404_ = v_body_411_;
v_a_405_ = v___y_414_;
v_a_406_ = v___y_415_;
v_a_407_ = v___y_416_;
v_a_408_ = v___y_417_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_411_);
return v___x_418_;
}
}
}
else
{
uint8_t v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
lean_dec_ref(v_e_404_);
v___x_451_ = 1;
v___x_452_ = lean_box(v___x_451_);
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go___boxed(lean_object* v_e_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go(v_e_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp(lean_object* v_e_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
uint8_t v___x_467_; 
v___x_467_ = l_Lean_Meta_Grind_isMatchCondCandidate(v_e_461_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec_ref(v_e_461_);
v___x_468_ = lean_box(v___x_467_);
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
else
{
lean_object* v___x_470_; 
v___x_470_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp_go(v_e_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp___boxed(lean_object* v_e_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp(v_e_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessHypothesis(lean_object* v_e_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v___x_490_; 
lean_inc_ref(v_e_478_);
v___x_490_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isMatchCondHyp(v_e_478_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; uint8_t v___x_492_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_490_, 1);
v___x_492_ = lean_unbox(v_a_491_);
lean_dec(v_a_491_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; 
v___x_493_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f(v_e_478_);
if (lean_obj_tag(v___x_493_) == 1)
{
lean_object* v_val_494_; uint8_t v___x_495_; lean_object* v___x_496_; 
lean_dec_ref(v_e_478_);
v_val_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_val_494_);
lean_dec_ref_known(v___x_493_, 1);
v___x_495_ = 1;
v___x_496_ = l_Lean_Meta_Sym_canon(v_val_494_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_498_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref_known(v___x_496_, 1);
v___x_498_ = l_Lean_Meta_Sym_shareCommon(v_a_497_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_508_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_508_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_508_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_508_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_503_ = lean_box(0);
v___x_504_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_504_, 0, v_a_499_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*2, v___x_495_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_504_);
v___x_506_ = v___x_501_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
v_a_509_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_498_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_498_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
v_a_517_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_496_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_496_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
else
{
lean_object* v___x_525_; 
lean_dec(v___x_493_);
lean_inc(v_a_488_);
lean_inc_ref(v_a_487_);
lean_inc(v_a_486_);
lean_inc_ref(v_a_485_);
lean_inc(v_a_484_);
lean_inc_ref(v_a_483_);
lean_inc(v_a_482_);
lean_inc_ref(v_a_481_);
lean_inc(v_a_480_);
lean_inc(v_a_479_);
v___x_525_ = lean_grind_preprocess(v_e_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
return v___x_525_;
}
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = l_Lean_Meta_Grind_markAsPreMatchCond(v_e_478_);
lean_inc(v_a_488_);
lean_inc_ref(v_a_487_);
lean_inc(v_a_486_);
lean_inc_ref(v_a_485_);
lean_inc(v_a_484_);
lean_inc_ref(v_a_483_);
lean_inc(v_a_482_);
lean_inc_ref(v_a_481_);
lean_inc(v_a_480_);
lean_inc(v_a_479_);
v___x_527_ = lean_grind_preprocess(v___x_526_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
return v___x_527_;
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_dec_ref(v_e_478_);
v_a_528_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_490_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_490_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessHypothesis___boxed(lean_object* v_e_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_Meta_Grind_preprocessHypothesis(v_e_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec(v_a_538_);
lean_dec(v_a_537_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(lean_object* v___x_549_, lean_object* v_str_550_, lean_object* v_a_551_, lean_object* v_b_552_){
_start:
{
uint8_t v_decide_553_; 
v_decide_553_ = lean_nat_dec_eq(v_a_551_, v___x_549_);
if (v_decide_553_ == 0)
{
uint32_t v___x_554_; uint32_t v___x_555_; uint8_t v___x_556_; 
v___x_554_ = lean_string_utf8_get_fast(v_str_550_, v_a_551_);
v___x_555_ = 95;
v___x_556_ = lean_uint32_dec_eq(v___x_554_, v___x_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_box(0);
v___x_558_ = lean_string_utf8_next_fast(v_str_550_, v_a_551_);
lean_dec(v_a_551_);
v_a_551_ = v___x_558_;
v_b_552_ = v___x_557_;
goto _start;
}
else
{
lean_object* v___x_560_; 
v___x_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_560_, 0, v_a_551_);
return v___x_560_;
}
}
else
{
lean_dec(v_a_551_);
lean_inc(v_b_552_);
return v_b_552_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg___boxed(lean_object* v___x_561_, lean_object* v_str_562_, lean_object* v_a_563_, lean_object* v_b_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_561_, v_str_562_, v_a_563_, v_b_564_);
lean_dec(v_b_564_);
lean_dec_ref(v_str_562_);
lean_dec(v___x_561_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(lean_object* v_name_572_, lean_object* v_type_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; 
if (lean_obj_tag(v_name_572_) == 1)
{
lean_object* v_str_607_; lean_object* v___y_609_; lean_object* v_searcher_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v_str_607_ = lean_ctor_get(v_name_572_, 1);
lean_inc_ref(v_str_607_);
lean_dec_ref_known(v_name_572_, 2);
v_searcher_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = lean_string_utf8_byte_size(v_str_607_);
v___x_629_ = lean_box(0);
v___x_630_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_628_, v_str_607_, v_searcher_627_, v___x_629_);
if (lean_obj_tag(v___x_630_) == 0)
{
v___y_609_ = v___x_628_;
goto v___jp_608_;
}
else
{
lean_object* v_val_631_; 
v_val_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_val_631_);
lean_dec_ref_known(v___x_630_, 1);
v___y_609_ = v_val_631_;
goto v___jp_608_;
}
v___jp_608_:
{
lean_object* v___x_610_; uint8_t v_decide_611_; 
v___x_610_ = lean_string_utf8_byte_size(v_str_607_);
v_decide_611_ = lean_nat_dec_eq(v___y_609_, v___x_610_);
if (v_decide_611_ == 0)
{
lean_object* v___x_612_; lean_object* v_suffix_613_; uint8_t v___x_614_; 
v___x_612_ = lean_string_utf8_next_fast(v_str_607_, v___y_609_);
lean_inc_ref(v_str_607_);
v_suffix_613_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_suffix_613_, 0, v_str_607_);
lean_ctor_set(v_suffix_613_, 1, v___x_612_);
lean_ctor_set(v_suffix_613_, 2, v___x_610_);
v___x_614_ = l_String_Slice_isNat(v_suffix_613_);
lean_dec_ref_known(v_suffix_613_, 3);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
lean_dec(v___y_609_);
lean_dec_ref(v_type_573_);
v___x_615_ = lean_box(0);
v___x_616_ = l_Lean_Name_str___override(v___x_615_, v_str_607_);
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
return v___x_617_;
}
else
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = lean_nat_dec_eq(v___y_609_, v___x_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
lean_dec_ref(v_type_573_);
v___x_620_ = lean_string_utf8_extract_fast(v_str_607_, v___x_618_, v___y_609_);
lean_dec(v___y_609_);
lean_dec_ref(v_str_607_);
v___x_621_ = lean_box(0);
v___x_622_ = l_Lean_Name_str___override(v___x_621_, v___x_620_);
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
else
{
lean_dec(v___y_609_);
lean_dec_ref(v_str_607_);
v___y_580_ = v_a_574_;
v___y_581_ = v_a_575_;
v___y_582_ = v_a_576_;
v___y_583_ = v_a_577_;
goto v___jp_579_;
}
}
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
lean_dec(v___y_609_);
lean_dec_ref(v_type_573_);
v___x_624_ = lean_box(0);
v___x_625_ = l_Lean_Name_str___override(v___x_624_, v_str_607_);
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
return v___x_626_;
}
}
}
else
{
lean_dec(v_name_572_);
v___y_580_ = v_a_574_;
v___y_581_ = v_a_575_;
v___y_582_ = v_a_576_;
v___y_583_ = v_a_577_;
goto v___jp_579_;
}
v___jp_579_:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_Meta_isProp(v_type_573_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_598_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_598_ == 0)
{
v___x_587_ = v___x_584_;
v_isShared_588_ = v_isSharedCheck_598_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_584_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_598_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
uint8_t v___x_589_; 
v___x_589_ = lean_unbox(v_a_585_);
lean_dec(v_a_585_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_590_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_590_);
v___x_592_ = v___x_587_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
else
{
lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_594_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_594_);
v___x_596_ = v___x_587_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_594_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
else
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
v_a_599_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_584_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_584_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___boxed(lean_object* v_name_632_, lean_object* v_type_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(v_name_632_, v_type_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0(lean_object* v___x_640_, lean_object* v___x_641_, lean_object* v_str_642_, lean_object* v_inst_643_, lean_object* v_R_644_, lean_object* v_a_645_, lean_object* v_b_646_, lean_object* v_c_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_640_, v_str_642_, v_a_645_, v_b_646_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___boxed(lean_object* v___x_649_, lean_object* v___x_650_, lean_object* v_str_651_, lean_object* v_inst_652_, lean_object* v_R_653_, lean_object* v_a_654_, lean_object* v_b_655_, lean_object* v_c_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0(v___x_649_, v___x_650_, v_str_651_, v_inst_652_, v_R_653_, v_a_654_, v_b_655_, v_c_656_);
lean_dec(v_b_655_);
lean_dec_ref(v_str_651_);
lean_dec_ref(v___x_650_);
lean_dec(v___x_649_);
return v_res_657_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(lean_object* v_keys_658_, lean_object* v_i_659_, lean_object* v_k_660_){
_start:
{
lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_661_ = lean_array_get_size(v_keys_658_);
v___x_662_ = lean_nat_dec_lt(v_i_659_, v___x_661_);
if (v___x_662_ == 0)
{
lean_dec(v_i_659_);
return v___x_662_;
}
else
{
lean_object* v_k_x27_663_; uint8_t v___x_664_; 
v_k_x27_663_ = lean_array_fget_borrowed(v_keys_658_, v_i_659_);
v___x_664_ = lean_name_eq(v_k_660_, v_k_x27_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_unsigned_to_nat(1u);
v___x_666_ = lean_nat_add(v_i_659_, v___x_665_);
lean_dec(v_i_659_);
v_i_659_ = v___x_666_;
goto _start;
}
else
{
lean_dec(v_i_659_);
return v___x_662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_keys_668_, lean_object* v_i_669_, lean_object* v_k_670_){
_start:
{
uint8_t v_res_671_; lean_object* v_r_672_; 
v_res_671_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_keys_668_, v_i_669_, v_k_670_);
lean_dec(v_k_670_);
lean_dec_ref(v_keys_668_);
v_r_672_ = lean_box(v_res_671_);
return v_r_672_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(lean_object* v_x_673_, size_t v_x_674_, lean_object* v_x_675_){
_start:
{
if (lean_obj_tag(v_x_673_) == 0)
{
lean_object* v_es_676_; lean_object* v___x_677_; size_t v___x_678_; size_t v___x_679_; lean_object* v_j_680_; lean_object* v___x_681_; 
v_es_676_ = lean_ctor_get(v_x_673_, 0);
v___x_677_ = lean_box(2);
v___x_678_ = ((size_t)31ULL);
v___x_679_ = lean_usize_land(v_x_674_, v___x_678_);
v_j_680_ = lean_usize_to_nat(v___x_679_);
v___x_681_ = lean_array_get_borrowed(v___x_677_, v_es_676_, v_j_680_);
lean_dec(v_j_680_);
switch(lean_obj_tag(v___x_681_))
{
case 0:
{
lean_object* v_key_682_; uint8_t v___x_683_; 
v_key_682_ = lean_ctor_get(v___x_681_, 0);
v___x_683_ = lean_name_eq(v_x_675_, v_key_682_);
return v___x_683_;
}
case 1:
{
lean_object* v_node_684_; size_t v___x_685_; size_t v___x_686_; 
v_node_684_ = lean_ctor_get(v___x_681_, 0);
v___x_685_ = ((size_t)5ULL);
v___x_686_ = lean_usize_shift_right(v_x_674_, v___x_685_);
v_x_673_ = v_node_684_;
v_x_674_ = v___x_686_;
goto _start;
}
default: 
{
uint8_t v___x_688_; 
v___x_688_ = 0;
return v___x_688_;
}
}
}
else
{
lean_object* v_ks_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v_ks_689_ = lean_ctor_get(v_x_673_, 0);
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_ks_689_, v___x_690_, v_x_675_);
return v___x_691_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___boxed(lean_object* v_x_692_, lean_object* v_x_693_, lean_object* v_x_694_){
_start:
{
size_t v_x_33592__boxed_695_; uint8_t v_res_696_; lean_object* v_r_697_; 
v_x_33592__boxed_695_ = lean_unbox_usize(v_x_693_);
lean_dec(v_x_693_);
v_res_696_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_692_, v_x_33592__boxed_695_, v_x_694_);
lean_dec(v_x_694_);
lean_dec_ref(v_x_692_);
v_r_697_ = lean_box(v_res_696_);
return v_r_697_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(lean_object* v_x_698_, lean_object* v_x_699_){
_start:
{
uint64_t v___y_701_; 
if (lean_obj_tag(v_x_699_) == 0)
{
uint64_t v___x_704_; 
v___x_704_ = 1723ULL;
v___y_701_ = v___x_704_;
goto v___jp_700_;
}
else
{
uint64_t v_hash_705_; 
v_hash_705_ = lean_ctor_get_uint64(v_x_699_, sizeof(void*)*2);
v___y_701_ = v_hash_705_;
goto v___jp_700_;
}
v___jp_700_:
{
size_t v___x_702_; uint8_t v___x_703_; 
v___x_702_ = lean_uint64_to_usize(v___y_701_);
v___x_703_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_698_, v___x_702_, v_x_699_);
return v___x_703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___boxed(lean_object* v_x_706_, lean_object* v_x_707_){
_start:
{
uint8_t v_res_708_; lean_object* v_r_709_; 
v_res_708_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_x_706_, v_x_707_);
lean_dec(v_x_707_);
lean_dec_ref(v_x_706_);
v_r_709_ = lean_box(v_res_708_);
return v_r_709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_snd_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_734_; 
v_snd_714_ = lean_ctor_get(v_a_711_, 1);
v_isSharedCheck_734_ = !lean_is_exclusive(v_a_711_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; 
v_unused_735_ = lean_ctor_get(v_a_711_, 0);
lean_dec(v_unused_735_);
v___x_716_ = v_a_711_;
v_isShared_717_ = v_isSharedCheck_734_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_snd_714_);
lean_dec(v_a_711_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_734_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v_toGoalState_722_; lean_object* v_clean_723_; lean_object* v_used_724_; uint8_t v___x_725_; 
lean_inc(v_snd_714_);
lean_inc(v_a_710_);
v___x_718_ = lean_name_append_index_after(v_a_710_, v_snd_714_);
v___x_719_ = lean_unsigned_to_nat(1u);
v___x_720_ = lean_nat_add(v_snd_714_, v___x_719_);
lean_dec(v_snd_714_);
v___x_721_ = lean_st_ref_get(v___y_712_);
v_toGoalState_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc_ref(v_toGoalState_722_);
lean_dec(v___x_721_);
v_clean_723_ = lean_ctor_get(v_toGoalState_722_, 16);
lean_inc_ref(v_clean_723_);
lean_dec_ref(v_toGoalState_722_);
v_used_724_ = lean_ctor_get(v_clean_723_, 0);
lean_inc_ref(v_used_724_);
lean_dec_ref(v_clean_723_);
v___x_725_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_used_724_, v___x_718_);
lean_dec_ref(v_used_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_727_; 
lean_dec(v_a_710_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 1, v___x_720_);
lean_ctor_set(v___x_716_, 0, v___x_718_);
v___x_727_ = v___x_716_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v___x_720_);
v___x_727_ = v_reuseFailAlloc_729_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_728_; 
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
return v___x_728_;
}
}
else
{
lean_object* v___x_731_; 
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 1, v___x_720_);
lean_ctor_set(v___x_716_, 0, v___x_718_);
v___x_731_ = v___x_716_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v___x_720_);
v___x_731_ = v_reuseFailAlloc_733_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
v_a_711_ = v___x_731_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg___boxed(lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v_a_736_, v_a_737_, v___y_738_);
lean_dec(v___y_738_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_741_, lean_object* v_x_742_, lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
lean_object* v_ks_745_; lean_object* v_vs_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_770_; 
v_ks_745_ = lean_ctor_get(v_x_741_, 0);
v_vs_746_ = lean_ctor_get(v_x_741_, 1);
v_isSharedCheck_770_ = !lean_is_exclusive(v_x_741_);
if (v_isSharedCheck_770_ == 0)
{
v___x_748_ = v_x_741_;
v_isShared_749_ = v_isSharedCheck_770_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_vs_746_);
lean_inc(v_ks_745_);
lean_dec(v_x_741_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_770_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_750_ = lean_array_get_size(v_ks_745_);
v___x_751_ = lean_nat_dec_lt(v_x_742_, v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
lean_dec(v_x_742_);
v___x_752_ = lean_array_push(v_ks_745_, v_x_743_);
v___x_753_ = lean_array_push(v_vs_746_, v_x_744_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v___x_753_);
lean_ctor_set(v___x_748_, 0, v___x_752_);
v___x_755_ = v___x_748_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v___x_753_);
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
lean_object* v_k_x27_757_; uint8_t v___x_758_; 
v_k_x27_757_ = lean_array_fget_borrowed(v_ks_745_, v_x_742_);
v___x_758_ = lean_name_eq(v_x_743_, v_k_x27_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_760_; 
if (v_isShared_749_ == 0)
{
v___x_760_ = v___x_748_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_ks_745_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_vs_746_);
v___x_760_ = v_reuseFailAlloc_764_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_unsigned_to_nat(1u);
v___x_762_ = lean_nat_add(v_x_742_, v___x_761_);
lean_dec(v_x_742_);
v_x_741_ = v___x_760_;
v_x_742_ = v___x_762_;
goto _start;
}
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_765_ = lean_array_fset(v_ks_745_, v_x_742_, v_x_743_);
v___x_766_ = lean_array_fset(v_vs_746_, v_x_742_, v_x_744_);
lean_dec(v_x_742_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v___x_766_);
lean_ctor_set(v___x_748_, 0, v___x_765_);
v___x_768_ = v___x_748_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(lean_object* v_n_771_, lean_object* v_k_772_, lean_object* v_v_773_){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(v_n_771_, v___x_774_, v_k_772_, v_v_773_);
return v___x_775_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(lean_object* v_x_777_, size_t v_x_778_, size_t v_x_779_, lean_object* v_x_780_, lean_object* v_x_781_){
_start:
{
if (lean_obj_tag(v_x_777_) == 0)
{
lean_object* v_es_782_; size_t v___x_783_; size_t v___x_784_; lean_object* v_j_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v_es_782_ = lean_ctor_get(v_x_777_, 0);
v___x_783_ = ((size_t)31ULL);
v___x_784_ = lean_usize_land(v_x_778_, v___x_783_);
v_j_785_ = lean_usize_to_nat(v___x_784_);
v___x_786_ = lean_array_get_size(v_es_782_);
v___x_787_ = lean_nat_dec_lt(v_j_785_, v___x_786_);
if (v___x_787_ == 0)
{
lean_dec(v_j_785_);
lean_dec(v_x_781_);
lean_dec(v_x_780_);
return v_x_777_;
}
else
{
lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_826_; 
lean_inc_ref(v_es_782_);
v_isSharedCheck_826_ = !lean_is_exclusive(v_x_777_);
if (v_isSharedCheck_826_ == 0)
{
lean_object* v_unused_827_; 
v_unused_827_ = lean_ctor_get(v_x_777_, 0);
lean_dec(v_unused_827_);
v___x_789_ = v_x_777_;
v_isShared_790_ = v_isSharedCheck_826_;
goto v_resetjp_788_;
}
else
{
lean_dec(v_x_777_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_826_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v_v_791_; lean_object* v___x_792_; lean_object* v_xs_x27_793_; lean_object* v___y_795_; 
v_v_791_ = lean_array_fget(v_es_782_, v_j_785_);
v___x_792_ = lean_box(0);
v_xs_x27_793_ = lean_array_fset(v_es_782_, v_j_785_, v___x_792_);
switch(lean_obj_tag(v_v_791_))
{
case 0:
{
lean_object* v_key_800_; lean_object* v_val_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_811_; 
v_key_800_ = lean_ctor_get(v_v_791_, 0);
v_val_801_ = lean_ctor_get(v_v_791_, 1);
v_isSharedCheck_811_ = !lean_is_exclusive(v_v_791_);
if (v_isSharedCheck_811_ == 0)
{
v___x_803_ = v_v_791_;
v_isShared_804_ = v_isSharedCheck_811_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_val_801_);
lean_inc(v_key_800_);
lean_dec(v_v_791_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_811_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
uint8_t v___x_805_; 
v___x_805_ = lean_name_eq(v_x_780_, v_key_800_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; lean_object* v___x_807_; 
lean_del_object(v___x_803_);
v___x_806_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_800_, v_val_801_, v_x_780_, v_x_781_);
v___x_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
v___y_795_ = v___x_807_;
goto v___jp_794_;
}
else
{
lean_object* v___x_809_; 
lean_dec(v_val_801_);
lean_dec(v_key_800_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 1, v_x_781_);
lean_ctor_set(v___x_803_, 0, v_x_780_);
v___x_809_ = v___x_803_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_x_780_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_x_781_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
v___y_795_ = v___x_809_;
goto v___jp_794_;
}
}
}
}
case 1:
{
lean_object* v_node_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_824_; 
v_node_812_ = lean_ctor_get(v_v_791_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v_v_791_);
if (v_isSharedCheck_824_ == 0)
{
v___x_814_ = v_v_791_;
v_isShared_815_ = v_isSharedCheck_824_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_node_812_);
lean_dec(v_v_791_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_824_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
size_t v___x_816_; size_t v___x_817_; size_t v___x_818_; size_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_816_ = ((size_t)5ULL);
v___x_817_ = lean_usize_shift_right(v_x_778_, v___x_816_);
v___x_818_ = ((size_t)1ULL);
v___x_819_ = lean_usize_add(v_x_779_, v___x_818_);
v___x_820_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_node_812_, v___x_817_, v___x_819_, v_x_780_, v_x_781_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_820_);
v___x_822_ = v___x_814_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
v___y_795_ = v___x_822_;
goto v___jp_794_;
}
}
}
default: 
{
lean_object* v___x_825_; 
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v_x_780_);
lean_ctor_set(v___x_825_, 1, v_x_781_);
v___y_795_ = v___x_825_;
goto v___jp_794_;
}
}
v___jp_794_:
{
lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_796_ = lean_array_fset(v_xs_x27_793_, v_j_785_, v___y_795_);
lean_dec(v_j_785_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_796_);
v___x_798_ = v___x_789_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_796_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
else
{
lean_object* v_ks_828_; lean_object* v_vs_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_847_; 
v_ks_828_ = lean_ctor_get(v_x_777_, 0);
v_vs_829_ = lean_ctor_get(v_x_777_, 1);
v_isSharedCheck_847_ = !lean_is_exclusive(v_x_777_);
if (v_isSharedCheck_847_ == 0)
{
v___x_831_ = v_x_777_;
v_isShared_832_ = v_isSharedCheck_847_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_vs_829_);
lean_inc(v_ks_828_);
lean_dec(v_x_777_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_847_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_ks_828_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_vs_829_);
v___x_834_ = v_reuseFailAlloc_846_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
lean_object* v_newNode_835_; size_t v___x_836_; uint8_t v___x_837_; 
v_newNode_835_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(v___x_834_, v_x_780_, v_x_781_);
v___x_836_ = ((size_t)7ULL);
v___x_837_ = lean_usize_dec_le(v___x_836_, v_x_779_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_838_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_835_);
v___x_839_ = lean_unsigned_to_nat(4u);
v___x_840_ = lean_nat_dec_lt(v___x_838_, v___x_839_);
lean_dec(v___x_838_);
if (v___x_840_ == 0)
{
lean_object* v_ks_841_; lean_object* v_vs_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v_ks_841_ = lean_ctor_get(v_newNode_835_, 0);
lean_inc_ref(v_ks_841_);
v_vs_842_ = lean_ctor_get(v_newNode_835_, 1);
lean_inc_ref(v_vs_842_);
lean_dec_ref(v_newNode_835_);
v___x_843_ = lean_unsigned_to_nat(0u);
v___x_844_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0);
v___x_845_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_x_779_, v_ks_841_, v_vs_842_, v___x_843_, v___x_844_);
lean_dec_ref(v_vs_842_);
lean_dec_ref(v_ks_841_);
return v___x_845_;
}
else
{
return v_newNode_835_;
}
}
else
{
return v_newNode_835_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(size_t v_depth_848_, lean_object* v_keys_849_, lean_object* v_vals_850_, lean_object* v_i_851_, lean_object* v_entries_852_){
_start:
{
lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_853_ = lean_array_get_size(v_keys_849_);
v___x_854_ = lean_nat_dec_lt(v_i_851_, v___x_853_);
if (v___x_854_ == 0)
{
lean_dec(v_i_851_);
return v_entries_852_;
}
else
{
lean_object* v_k_855_; lean_object* v_v_856_; uint64_t v___y_858_; 
v_k_855_ = lean_array_fget_borrowed(v_keys_849_, v_i_851_);
v_v_856_ = lean_array_fget_borrowed(v_vals_850_, v_i_851_);
if (lean_obj_tag(v_k_855_) == 0)
{
uint64_t v___x_869_; 
v___x_869_ = 1723ULL;
v___y_858_ = v___x_869_;
goto v___jp_857_;
}
else
{
uint64_t v_hash_870_; 
v_hash_870_ = lean_ctor_get_uint64(v_k_855_, sizeof(void*)*2);
v___y_858_ = v_hash_870_;
goto v___jp_857_;
}
v___jp_857_:
{
size_t v_h_859_; size_t v___x_860_; lean_object* v___x_861_; size_t v___x_862_; size_t v___x_863_; size_t v___x_864_; size_t v_h_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_h_859_ = lean_uint64_to_usize(v___y_858_);
v___x_860_ = ((size_t)5ULL);
v___x_861_ = lean_unsigned_to_nat(1u);
v___x_862_ = ((size_t)1ULL);
v___x_863_ = lean_usize_sub(v_depth_848_, v___x_862_);
v___x_864_ = lean_usize_mul(v___x_860_, v___x_863_);
v_h_865_ = lean_usize_shift_right(v_h_859_, v___x_864_);
v___x_866_ = lean_nat_add(v_i_851_, v___x_861_);
lean_dec(v_i_851_);
lean_inc(v_v_856_);
lean_inc(v_k_855_);
v___x_867_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_entries_852_, v_h_865_, v_depth_848_, v_k_855_, v_v_856_);
v_i_851_ = v___x_866_;
v_entries_852_ = v___x_867_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_871_, lean_object* v_keys_872_, lean_object* v_vals_873_, lean_object* v_i_874_, lean_object* v_entries_875_){
_start:
{
size_t v_depth_boxed_876_; lean_object* v_res_877_; 
v_depth_boxed_876_ = lean_unbox_usize(v_depth_871_);
lean_dec(v_depth_871_);
v_res_877_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_depth_boxed_876_, v_keys_872_, v_vals_873_, v_i_874_, v_entries_875_);
lean_dec_ref(v_vals_873_);
lean_dec_ref(v_keys_872_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___boxed(lean_object* v_x_878_, lean_object* v_x_879_, lean_object* v_x_880_, lean_object* v_x_881_, lean_object* v_x_882_){
_start:
{
size_t v_x_33772__boxed_883_; size_t v_x_33773__boxed_884_; lean_object* v_res_885_; 
v_x_33772__boxed_883_ = lean_unbox_usize(v_x_879_);
lean_dec(v_x_879_);
v_x_33773__boxed_884_ = lean_unbox_usize(v_x_880_);
lean_dec(v_x_880_);
v_res_885_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_878_, v_x_33772__boxed_883_, v_x_33773__boxed_884_, v_x_881_, v_x_882_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(lean_object* v_x_886_, lean_object* v_x_887_, lean_object* v_x_888_){
_start:
{
uint64_t v___y_890_; 
if (lean_obj_tag(v_x_887_) == 0)
{
uint64_t v___x_894_; 
v___x_894_ = 1723ULL;
v___y_890_ = v___x_894_;
goto v___jp_889_;
}
else
{
uint64_t v_hash_895_; 
v_hash_895_ = lean_ctor_get_uint64(v_x_887_, sizeof(void*)*2);
v___y_890_ = v_hash_895_;
goto v___jp_889_;
}
v___jp_889_:
{
size_t v___x_891_; size_t v___x_892_; lean_object* v___x_893_; 
v___x_891_ = lean_uint64_to_usize(v___y_890_);
v___x_892_ = ((size_t)1ULL);
v___x_893_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_886_, v___x_891_, v___x_892_, v_x_887_, v_x_888_);
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(lean_object* v_keys_896_, lean_object* v_vals_897_, lean_object* v_i_898_, lean_object* v_k_899_){
_start:
{
lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_900_ = lean_array_get_size(v_keys_896_);
v___x_901_ = lean_nat_dec_lt(v_i_898_, v___x_900_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; 
lean_dec(v_i_898_);
v___x_902_ = lean_box(0);
return v___x_902_;
}
else
{
lean_object* v_k_x27_903_; uint8_t v___x_904_; 
v_k_x27_903_ = lean_array_fget_borrowed(v_keys_896_, v_i_898_);
v___x_904_ = lean_name_eq(v_k_899_, v_k_x27_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = lean_unsigned_to_nat(1u);
v___x_906_ = lean_nat_add(v_i_898_, v___x_905_);
lean_dec(v_i_898_);
v_i_898_ = v___x_906_;
goto _start;
}
else
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = lean_array_fget_borrowed(v_vals_897_, v_i_898_);
lean_dec(v_i_898_);
lean_inc(v___x_908_);
v___x_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
return v___x_909_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_keys_910_, lean_object* v_vals_911_, lean_object* v_i_912_, lean_object* v_k_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_keys_910_, v_vals_911_, v_i_912_, v_k_913_);
lean_dec(v_k_913_);
lean_dec_ref(v_vals_911_);
lean_dec_ref(v_keys_910_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(lean_object* v_x_915_, size_t v_x_916_, lean_object* v_x_917_){
_start:
{
if (lean_obj_tag(v_x_915_) == 0)
{
lean_object* v_es_918_; lean_object* v___x_919_; size_t v___x_920_; size_t v___x_921_; lean_object* v_j_922_; lean_object* v___x_923_; 
v_es_918_ = lean_ctor_get(v_x_915_, 0);
v___x_919_ = lean_box(2);
v___x_920_ = ((size_t)31ULL);
v___x_921_ = lean_usize_land(v_x_916_, v___x_920_);
v_j_922_ = lean_usize_to_nat(v___x_921_);
v___x_923_ = lean_array_get_borrowed(v___x_919_, v_es_918_, v_j_922_);
lean_dec(v_j_922_);
switch(lean_obj_tag(v___x_923_))
{
case 0:
{
lean_object* v_key_924_; lean_object* v_val_925_; uint8_t v___x_926_; 
v_key_924_ = lean_ctor_get(v___x_923_, 0);
v_val_925_ = lean_ctor_get(v___x_923_, 1);
v___x_926_ = lean_name_eq(v_x_917_, v_key_924_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; 
v___x_927_ = lean_box(0);
return v___x_927_;
}
else
{
lean_object* v___x_928_; 
lean_inc(v_val_925_);
v___x_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_928_, 0, v_val_925_);
return v___x_928_;
}
}
case 1:
{
lean_object* v_node_929_; size_t v___x_930_; size_t v___x_931_; 
v_node_929_ = lean_ctor_get(v___x_923_, 0);
v___x_930_ = ((size_t)5ULL);
v___x_931_ = lean_usize_shift_right(v_x_916_, v___x_930_);
v_x_915_ = v_node_929_;
v_x_916_ = v___x_931_;
goto _start;
}
default: 
{
lean_object* v___x_933_; 
v___x_933_ = lean_box(0);
return v___x_933_;
}
}
}
else
{
lean_object* v_ks_934_; lean_object* v_vs_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v_ks_934_ = lean_ctor_get(v_x_915_, 0);
v_vs_935_ = lean_ctor_get(v_x_915_, 1);
v___x_936_ = lean_unsigned_to_nat(0u);
v___x_937_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_ks_934_, v_vs_935_, v___x_936_, v_x_917_);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg___boxed(lean_object* v_x_938_, lean_object* v_x_939_, lean_object* v_x_940_){
_start:
{
size_t v_x_33962__boxed_941_; lean_object* v_res_942_; 
v_x_33962__boxed_941_ = lean_unbox_usize(v_x_939_);
lean_dec(v_x_939_);
v_res_942_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_938_, v_x_33962__boxed_941_, v_x_940_);
lean_dec(v_x_940_);
lean_dec_ref(v_x_938_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(lean_object* v_x_943_, lean_object* v_x_944_){
_start:
{
uint64_t v___y_946_; 
if (lean_obj_tag(v_x_944_) == 0)
{
uint64_t v___x_949_; 
v___x_949_ = 1723ULL;
v___y_946_ = v___x_949_;
goto v___jp_945_;
}
else
{
uint64_t v_hash_950_; 
v_hash_950_ = lean_ctor_get_uint64(v_x_944_, sizeof(void*)*2);
v___y_946_ = v_hash_950_;
goto v___jp_945_;
}
v___jp_945_:
{
size_t v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_uint64_to_usize(v___y_946_);
v___x_948_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_943_, v___x_947_, v_x_944_);
return v___x_948_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg___boxed(lean_object* v_x_951_, lean_object* v_x_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_x_951_, v_x_952_);
lean_dec(v_x_952_);
lean_dec_ref(v_x_951_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(lean_object* v_name_957_, lean_object* v_type_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_name_971_; lean_object* v___y_972_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v_name_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_961_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1193_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1193_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1193_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
uint8_t v_clean_1158_; 
v_clean_1158_ = lean_ctor_get_uint8(v_a_1133_, sizeof(void*)*18 + 16);
lean_dec(v_a_1133_);
if (v_clean_1158_ == 0)
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Lean_Meta_Grind_getOriginalName_x3f(v_name_957_);
if (lean_obj_tag(v___x_1159_) == 1)
{
lean_object* v_val_1160_; lean_object* v___x_1162_; 
lean_dec_ref(v_type_958_);
lean_dec(v_name_957_);
v_val_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_val_1160_);
lean_dec_ref_known(v___x_1159_, 1);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v_val_1160_);
v___x_1162_ = v___x_1135_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_val_1160_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
else
{
uint8_t v___x_1164_; 
lean_dec(v___x_1159_);
v___x_1164_ = l_Lean_Name_hasMacroScopes(v_name_957_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; 
lean_del_object(v___x_1135_);
lean_dec_ref(v_type_958_);
v___x_1165_ = l_Lean_Core_mkFreshUserName(v_name_957_, v_a_967_, v_a_968_);
return v___x_1165_;
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1166_ = l_Lean_Name_eraseMacroScopes(v_name_957_);
v___x_1167_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
v___x_1168_ = lean_name_eq(v___x_1166_, v___x_1167_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1));
v___x_1170_ = lean_name_eq(v___x_1166_, v___x_1169_);
lean_dec(v___x_1166_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1172_; 
lean_dec_ref(v_type_958_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v_name_957_);
v___x_1172_ = v___x_1135_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_name_957_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
else
{
lean_del_object(v___x_1135_);
goto v___jp_1137_;
}
}
else
{
lean_dec(v___x_1166_);
lean_del_object(v___x_1135_);
goto v___jp_1137_;
}
}
}
}
else
{
uint8_t v___x_1174_; 
lean_del_object(v___x_1135_);
v___x_1174_ = l_Lean_Name_hasMacroScopes(v_name_957_);
if (v___x_1174_ == 0)
{
v_name_1107_ = v_name_957_;
v___y_1108_ = v_a_959_;
v___y_1109_ = v_a_960_;
v___y_1110_ = v_a_961_;
v___y_1111_ = v_a_962_;
v___y_1112_ = v_a_963_;
v___y_1113_ = v_a_964_;
v___y_1114_ = v_a_965_;
v___y_1115_ = v_a_966_;
v___y_1116_ = v_a_967_;
v___y_1117_ = v_a_968_;
goto v___jp_1106_;
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1189_; uint8_t v___x_1190_; 
v___x_1175_ = l_Lean_Name_eraseMacroScopes(v_name_957_);
lean_dec(v_name_957_);
v___x_1189_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1));
v___x_1190_ = lean_name_eq(v___x_1175_, v___x_1189_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1));
v___x_1192_ = lean_name_eq(v___x_1175_, v___x_1191_);
if (v___x_1192_ == 0)
{
v_name_1107_ = v___x_1175_;
v___y_1108_ = v_a_959_;
v___y_1109_ = v_a_960_;
v___y_1110_ = v_a_961_;
v___y_1111_ = v_a_962_;
v___y_1112_ = v_a_963_;
v___y_1113_ = v_a_964_;
v___y_1114_ = v_a_965_;
v___y_1115_ = v_a_966_;
v___y_1116_ = v_a_967_;
v___y_1117_ = v_a_968_;
goto v___jp_1106_;
}
else
{
goto v___jp_1176_;
}
}
else
{
goto v___jp_1176_;
}
v___jp_1176_:
{
lean_object* v___x_1177_; 
lean_inc_ref(v_type_958_);
v___x_1177_ = l_Lean_Meta_isProp(v_type_958_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; uint8_t v___x_1179_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref_known(v___x_1177_, 1);
v___x_1179_ = lean_unbox(v_a_1178_);
lean_dec(v_a_1178_);
if (v___x_1179_ == 0)
{
v_name_1107_ = v___x_1175_;
v___y_1108_ = v_a_959_;
v___y_1109_ = v_a_960_;
v___y_1110_ = v_a_961_;
v___y_1111_ = v_a_962_;
v___y_1112_ = v_a_963_;
v___y_1113_ = v_a_964_;
v___y_1114_ = v_a_965_;
v___y_1115_ = v_a_966_;
v___y_1116_ = v_a_967_;
v___y_1117_ = v_a_968_;
goto v___jp_1106_;
}
else
{
lean_object* v___x_1180_; 
lean_dec(v___x_1175_);
v___x_1180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v_name_1107_ = v___x_1180_;
v___y_1108_ = v_a_959_;
v___y_1109_ = v_a_960_;
v___y_1110_ = v_a_961_;
v___y_1111_ = v_a_962_;
v___y_1112_ = v_a_963_;
v___y_1113_ = v_a_964_;
v___y_1114_ = v_a_965_;
v___y_1115_ = v_a_966_;
v___y_1116_ = v_a_967_;
v___y_1117_ = v_a_968_;
goto v___jp_1106_;
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec(v___x_1175_);
lean_dec_ref(v_type_958_);
v_a_1181_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1177_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1177_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
}
v___jp_1137_:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_Meta_isProp(v_type_958_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1149_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1141_ = v___x_1138_;
v_isShared_1142_ = v_isSharedCheck_1149_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1138_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1149_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
uint8_t v___x_1143_; 
v___x_1143_ = lean_unbox(v_a_1139_);
lean_dec(v_a_1139_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1145_; 
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v_name_957_);
v___x_1145_ = v___x_1141_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_name_957_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
else
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_del_object(v___x_1141_);
lean_dec(v_name_957_);
v___x_1147_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v___x_1148_ = l_Lean_Core_mkFreshUserName(v___x_1147_, v_a_967_, v_a_968_);
return v___x_1148_;
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec(v_name_957_);
v_a_1150_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1138_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1138_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec_ref(v_type_958_);
lean_dec(v_name_957_);
v_a_1194_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1132_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1132_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
v___jp_970_:
{
lean_object* v___x_973_; lean_object* v_toGoalState_974_; lean_object* v_clean_975_; lean_object* v_mvarId_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1025_; 
v___x_973_ = lean_st_ref_take(v___y_972_);
v_toGoalState_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc_ref(v_toGoalState_974_);
v_clean_975_ = lean_ctor_get(v_toGoalState_974_, 16);
lean_inc_ref(v_clean_975_);
v_mvarId_976_ = lean_ctor_get(v___x_973_, 1);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1025_ == 0)
{
lean_object* v_unused_1026_; 
v_unused_1026_ = lean_ctor_get(v___x_973_, 0);
lean_dec(v_unused_1026_);
v___x_978_ = v___x_973_;
v_isShared_979_ = v_isSharedCheck_1025_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_mvarId_976_);
lean_dec(v___x_973_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1025_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_nextDeclIdx_980_; lean_object* v_enodeMap_981_; lean_object* v_exprs_982_; lean_object* v_parents_983_; lean_object* v_congrTable_984_; lean_object* v_appMap_985_; lean_object* v_indicesFound_986_; lean_object* v_toProcess_987_; lean_object* v_internalizing_988_; uint8_t v_inconsistent_989_; lean_object* v_nextIdx_990_; lean_object* v_newRawFacts_991_; lean_object* v_facts_992_; lean_object* v_extThms_993_; lean_object* v_ematch_994_; lean_object* v_inj_995_; lean_object* v_split_996_; lean_object* v_sstates_997_; lean_object* v_goalStack_998_; uint64_t v_introBase_999_; lean_object* v_numIntros_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1023_; 
v_nextDeclIdx_980_ = lean_ctor_get(v_toGoalState_974_, 0);
v_enodeMap_981_ = lean_ctor_get(v_toGoalState_974_, 1);
v_exprs_982_ = lean_ctor_get(v_toGoalState_974_, 2);
v_parents_983_ = lean_ctor_get(v_toGoalState_974_, 3);
v_congrTable_984_ = lean_ctor_get(v_toGoalState_974_, 4);
v_appMap_985_ = lean_ctor_get(v_toGoalState_974_, 5);
v_indicesFound_986_ = lean_ctor_get(v_toGoalState_974_, 6);
v_toProcess_987_ = lean_ctor_get(v_toGoalState_974_, 7);
v_internalizing_988_ = lean_ctor_get(v_toGoalState_974_, 8);
v_inconsistent_989_ = lean_ctor_get_uint8(v_toGoalState_974_, sizeof(void*)*20 + 8);
v_nextIdx_990_ = lean_ctor_get(v_toGoalState_974_, 9);
v_newRawFacts_991_ = lean_ctor_get(v_toGoalState_974_, 10);
v_facts_992_ = lean_ctor_get(v_toGoalState_974_, 11);
v_extThms_993_ = lean_ctor_get(v_toGoalState_974_, 12);
v_ematch_994_ = lean_ctor_get(v_toGoalState_974_, 13);
v_inj_995_ = lean_ctor_get(v_toGoalState_974_, 14);
v_split_996_ = lean_ctor_get(v_toGoalState_974_, 15);
v_sstates_997_ = lean_ctor_get(v_toGoalState_974_, 17);
v_goalStack_998_ = lean_ctor_get(v_toGoalState_974_, 18);
v_introBase_999_ = lean_ctor_get_uint64(v_toGoalState_974_, sizeof(void*)*20);
v_numIntros_1000_ = lean_ctor_get(v_toGoalState_974_, 19);
v_isSharedCheck_1023_ = !lean_is_exclusive(v_toGoalState_974_);
if (v_isSharedCheck_1023_ == 0)
{
lean_object* v_unused_1024_; 
v_unused_1024_ = lean_ctor_get(v_toGoalState_974_, 16);
lean_dec(v_unused_1024_);
v___x_1002_ = v_toGoalState_974_;
v_isShared_1003_ = v_isSharedCheck_1023_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_numIntros_1000_);
lean_inc(v_goalStack_998_);
lean_inc(v_sstates_997_);
lean_inc(v_split_996_);
lean_inc(v_inj_995_);
lean_inc(v_ematch_994_);
lean_inc(v_extThms_993_);
lean_inc(v_facts_992_);
lean_inc(v_newRawFacts_991_);
lean_inc(v_nextIdx_990_);
lean_inc(v_internalizing_988_);
lean_inc(v_toProcess_987_);
lean_inc(v_indicesFound_986_);
lean_inc(v_appMap_985_);
lean_inc(v_congrTable_984_);
lean_inc(v_parents_983_);
lean_inc(v_exprs_982_);
lean_inc(v_enodeMap_981_);
lean_inc(v_nextDeclIdx_980_);
lean_dec(v_toGoalState_974_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1023_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v_used_1004_; lean_object* v_next_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1022_; 
v_used_1004_ = lean_ctor_get(v_clean_975_, 0);
v_next_1005_ = lean_ctor_get(v_clean_975_, 1);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_clean_975_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1007_ = v_clean_975_;
v_isShared_1008_ = v_isSharedCheck_1022_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_next_1005_);
lean_inc(v_used_1004_);
lean_dec(v_clean_975_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1022_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1009_ = lean_box(0);
lean_inc(v_name_971_);
v___x_1010_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_used_1004_, v_name_971_, v___x_1009_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v___x_1010_);
v___x_1012_ = v___x_1007_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_next_1005_);
v___x_1012_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1014_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 16, v___x_1012_);
v___x_1014_ = v___x_1002_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_nextDeclIdx_980_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_enodeMap_981_);
lean_ctor_set(v_reuseFailAlloc_1020_, 2, v_exprs_982_);
lean_ctor_set(v_reuseFailAlloc_1020_, 3, v_parents_983_);
lean_ctor_set(v_reuseFailAlloc_1020_, 4, v_congrTable_984_);
lean_ctor_set(v_reuseFailAlloc_1020_, 5, v_appMap_985_);
lean_ctor_set(v_reuseFailAlloc_1020_, 6, v_indicesFound_986_);
lean_ctor_set(v_reuseFailAlloc_1020_, 7, v_toProcess_987_);
lean_ctor_set(v_reuseFailAlloc_1020_, 8, v_internalizing_988_);
lean_ctor_set(v_reuseFailAlloc_1020_, 9, v_nextIdx_990_);
lean_ctor_set(v_reuseFailAlloc_1020_, 10, v_newRawFacts_991_);
lean_ctor_set(v_reuseFailAlloc_1020_, 11, v_facts_992_);
lean_ctor_set(v_reuseFailAlloc_1020_, 12, v_extThms_993_);
lean_ctor_set(v_reuseFailAlloc_1020_, 13, v_ematch_994_);
lean_ctor_set(v_reuseFailAlloc_1020_, 14, v_inj_995_);
lean_ctor_set(v_reuseFailAlloc_1020_, 15, v_split_996_);
lean_ctor_set(v_reuseFailAlloc_1020_, 16, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1020_, 17, v_sstates_997_);
lean_ctor_set(v_reuseFailAlloc_1020_, 18, v_goalStack_998_);
lean_ctor_set(v_reuseFailAlloc_1020_, 19, v_numIntros_1000_);
lean_ctor_set_uint8(v_reuseFailAlloc_1020_, sizeof(void*)*20 + 8, v_inconsistent_989_);
lean_ctor_set_uint64(v_reuseFailAlloc_1020_, sizeof(void*)*20, v_introBase_999_);
v___x_1014_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1016_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_1014_);
v___x_1016_ = v___x_978_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_mvarId_976_);
v___x_1016_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_st_ref_put(v___y_972_, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v_name_971_);
return v___x_1018_;
}
}
}
}
}
}
}
v___jp_1027_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___y_1036_);
lean_ctor_set(v___x_1041_, 1, v___y_1040_);
lean_inc(v___y_1033_);
v___x_1042_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v___y_1033_, v___x_1041_, v___y_1039_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v_fst_1044_; lean_object* v_snd_1045_; lean_object* v___x_1046_; lean_object* v_toGoalState_1047_; lean_object* v_clean_1048_; lean_object* v_mvarId_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1096_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
lean_dec_ref_known(v___x_1042_, 1);
v_fst_1044_ = lean_ctor_get(v_a_1043_, 0);
lean_inc(v_fst_1044_);
v_snd_1045_ = lean_ctor_get(v_a_1043_, 1);
lean_inc(v_snd_1045_);
lean_dec(v_a_1043_);
v___x_1046_ = lean_st_ref_take(v___y_1039_);
v_toGoalState_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc_ref(v_toGoalState_1047_);
v_clean_1048_ = lean_ctor_get(v_toGoalState_1047_, 16);
lean_inc_ref(v_clean_1048_);
v_mvarId_1049_ = lean_ctor_get(v___x_1046_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; 
v_unused_1097_ = lean_ctor_get(v___x_1046_, 0);
lean_dec(v_unused_1097_);
v___x_1051_ = v___x_1046_;
v_isShared_1052_ = v_isSharedCheck_1096_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_mvarId_1049_);
lean_dec(v___x_1046_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1096_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v_nextDeclIdx_1053_; lean_object* v_enodeMap_1054_; lean_object* v_exprs_1055_; lean_object* v_parents_1056_; lean_object* v_congrTable_1057_; lean_object* v_appMap_1058_; lean_object* v_indicesFound_1059_; lean_object* v_toProcess_1060_; lean_object* v_internalizing_1061_; uint8_t v_inconsistent_1062_; lean_object* v_nextIdx_1063_; lean_object* v_newRawFacts_1064_; lean_object* v_facts_1065_; lean_object* v_extThms_1066_; lean_object* v_ematch_1067_; lean_object* v_inj_1068_; lean_object* v_split_1069_; lean_object* v_sstates_1070_; lean_object* v_goalStack_1071_; uint64_t v_introBase_1072_; lean_object* v_numIntros_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1094_; 
v_nextDeclIdx_1053_ = lean_ctor_get(v_toGoalState_1047_, 0);
v_enodeMap_1054_ = lean_ctor_get(v_toGoalState_1047_, 1);
v_exprs_1055_ = lean_ctor_get(v_toGoalState_1047_, 2);
v_parents_1056_ = lean_ctor_get(v_toGoalState_1047_, 3);
v_congrTable_1057_ = lean_ctor_get(v_toGoalState_1047_, 4);
v_appMap_1058_ = lean_ctor_get(v_toGoalState_1047_, 5);
v_indicesFound_1059_ = lean_ctor_get(v_toGoalState_1047_, 6);
v_toProcess_1060_ = lean_ctor_get(v_toGoalState_1047_, 7);
v_internalizing_1061_ = lean_ctor_get(v_toGoalState_1047_, 8);
v_inconsistent_1062_ = lean_ctor_get_uint8(v_toGoalState_1047_, sizeof(void*)*20 + 8);
v_nextIdx_1063_ = lean_ctor_get(v_toGoalState_1047_, 9);
v_newRawFacts_1064_ = lean_ctor_get(v_toGoalState_1047_, 10);
v_facts_1065_ = lean_ctor_get(v_toGoalState_1047_, 11);
v_extThms_1066_ = lean_ctor_get(v_toGoalState_1047_, 12);
v_ematch_1067_ = lean_ctor_get(v_toGoalState_1047_, 13);
v_inj_1068_ = lean_ctor_get(v_toGoalState_1047_, 14);
v_split_1069_ = lean_ctor_get(v_toGoalState_1047_, 15);
v_sstates_1070_ = lean_ctor_get(v_toGoalState_1047_, 17);
v_goalStack_1071_ = lean_ctor_get(v_toGoalState_1047_, 18);
v_introBase_1072_ = lean_ctor_get_uint64(v_toGoalState_1047_, sizeof(void*)*20);
v_numIntros_1073_ = lean_ctor_get(v_toGoalState_1047_, 19);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_toGoalState_1047_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; 
v_unused_1095_ = lean_ctor_get(v_toGoalState_1047_, 16);
lean_dec(v_unused_1095_);
v___x_1075_ = v_toGoalState_1047_;
v_isShared_1076_ = v_isSharedCheck_1094_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_numIntros_1073_);
lean_inc(v_goalStack_1071_);
lean_inc(v_sstates_1070_);
lean_inc(v_split_1069_);
lean_inc(v_inj_1068_);
lean_inc(v_ematch_1067_);
lean_inc(v_extThms_1066_);
lean_inc(v_facts_1065_);
lean_inc(v_newRawFacts_1064_);
lean_inc(v_nextIdx_1063_);
lean_inc(v_internalizing_1061_);
lean_inc(v_toProcess_1060_);
lean_inc(v_indicesFound_1059_);
lean_inc(v_appMap_1058_);
lean_inc(v_congrTable_1057_);
lean_inc(v_parents_1056_);
lean_inc(v_exprs_1055_);
lean_inc(v_enodeMap_1054_);
lean_inc(v_nextDeclIdx_1053_);
lean_dec(v_toGoalState_1047_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1094_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v_used_1077_; lean_object* v_next_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1093_; 
v_used_1077_ = lean_ctor_get(v_clean_1048_, 0);
v_next_1078_ = lean_ctor_get(v_clean_1048_, 1);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_clean_1048_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1080_ = v_clean_1048_;
v_isShared_1081_ = v_isSharedCheck_1093_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_next_1078_);
lean_inc(v_used_1077_);
lean_dec(v_clean_1048_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1093_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1082_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_next_1078_, v___y_1033_, v_snd_1045_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 1, v___x_1082_);
v___x_1084_ = v___x_1080_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_used_1077_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1086_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 16, v___x_1084_);
v___x_1086_ = v___x_1075_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_nextDeclIdx_1053_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_enodeMap_1054_);
lean_ctor_set(v_reuseFailAlloc_1091_, 2, v_exprs_1055_);
lean_ctor_set(v_reuseFailAlloc_1091_, 3, v_parents_1056_);
lean_ctor_set(v_reuseFailAlloc_1091_, 4, v_congrTable_1057_);
lean_ctor_set(v_reuseFailAlloc_1091_, 5, v_appMap_1058_);
lean_ctor_set(v_reuseFailAlloc_1091_, 6, v_indicesFound_1059_);
lean_ctor_set(v_reuseFailAlloc_1091_, 7, v_toProcess_1060_);
lean_ctor_set(v_reuseFailAlloc_1091_, 8, v_internalizing_1061_);
lean_ctor_set(v_reuseFailAlloc_1091_, 9, v_nextIdx_1063_);
lean_ctor_set(v_reuseFailAlloc_1091_, 10, v_newRawFacts_1064_);
lean_ctor_set(v_reuseFailAlloc_1091_, 11, v_facts_1065_);
lean_ctor_set(v_reuseFailAlloc_1091_, 12, v_extThms_1066_);
lean_ctor_set(v_reuseFailAlloc_1091_, 13, v_ematch_1067_);
lean_ctor_set(v_reuseFailAlloc_1091_, 14, v_inj_1068_);
lean_ctor_set(v_reuseFailAlloc_1091_, 15, v_split_1069_);
lean_ctor_set(v_reuseFailAlloc_1091_, 16, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1091_, 17, v_sstates_1070_);
lean_ctor_set(v_reuseFailAlloc_1091_, 18, v_goalStack_1071_);
lean_ctor_set(v_reuseFailAlloc_1091_, 19, v_numIntros_1073_);
lean_ctor_set_uint8(v_reuseFailAlloc_1091_, sizeof(void*)*20 + 8, v_inconsistent_1062_);
lean_ctor_set_uint64(v_reuseFailAlloc_1091_, sizeof(void*)*20, v_introBase_1072_);
v___x_1086_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1088_; 
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v___x_1086_);
v___x_1088_ = v___x_1051_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_mvarId_1049_);
v___x_1088_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_st_ref_put(v___y_1039_, v___x_1088_);
v_name_971_ = v_fst_1044_;
v___y_972_ = v___y_1039_;
goto v___jp_970_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec(v___y_1033_);
v_a_1098_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1042_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1042_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
v___jp_1106_:
{
lean_object* v___x_1118_; lean_object* v_toGoalState_1119_; lean_object* v_clean_1120_; lean_object* v_used_1121_; uint8_t v___x_1122_; 
v___x_1118_ = lean_st_ref_get(v___y_1108_);
v_toGoalState_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc_ref(v_toGoalState_1119_);
lean_dec(v___x_1118_);
v_clean_1120_ = lean_ctor_get(v_toGoalState_1119_, 16);
lean_inc_ref(v_clean_1120_);
lean_dec_ref(v_toGoalState_1119_);
v_used_1121_ = lean_ctor_get(v_clean_1120_, 0);
lean_inc_ref(v_used_1121_);
lean_dec_ref(v_clean_1120_);
v___x_1122_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_used_1121_, v_name_1107_);
lean_dec_ref(v_used_1121_);
if (v___x_1122_ == 0)
{
lean_dec_ref(v_type_958_);
v_name_971_ = v_name_1107_;
v___y_972_ = v___y_1108_;
goto v___jp_970_;
}
else
{
lean_object* v___x_1123_; 
lean_inc(v_name_1107_);
v___x_1123_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(v_name_1107_, v_type_958_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; lean_object* v___x_1125_; lean_object* v_toGoalState_1126_; lean_object* v_clean_1127_; lean_object* v_next_1128_; lean_object* v___x_1129_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1124_);
lean_dec_ref_known(v___x_1123_, 1);
v___x_1125_ = lean_st_ref_get(v___y_1108_);
v_toGoalState_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc_ref(v_toGoalState_1126_);
lean_dec(v___x_1125_);
v_clean_1127_ = lean_ctor_get(v_toGoalState_1126_, 16);
lean_inc_ref(v_clean_1127_);
lean_dec_ref(v_toGoalState_1126_);
v_next_1128_ = lean_ctor_get(v_clean_1127_, 1);
lean_inc_ref(v_next_1128_);
lean_dec_ref(v_clean_1127_);
v___x_1129_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_next_1128_, v_a_1124_);
lean_dec_ref(v_next_1128_);
if (lean_obj_tag(v___x_1129_) == 1)
{
lean_object* v_val_1130_; 
v_val_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_val_1130_);
lean_dec_ref_known(v___x_1129_, 1);
v___y_1028_ = v___y_1109_;
v___y_1029_ = v___y_1115_;
v___y_1030_ = v___y_1116_;
v___y_1031_ = v___y_1110_;
v___y_1032_ = v___y_1112_;
v___y_1033_ = v_a_1124_;
v___y_1034_ = v___y_1111_;
v___y_1035_ = v___y_1114_;
v___y_1036_ = v_name_1107_;
v___y_1037_ = v___y_1113_;
v___y_1038_ = v___y_1117_;
v___y_1039_ = v___y_1108_;
v___y_1040_ = v_val_1130_;
goto v___jp_1027_;
}
else
{
lean_object* v___x_1131_; 
lean_dec(v___x_1129_);
v___x_1131_ = lean_unsigned_to_nat(1u);
v___y_1028_ = v___y_1109_;
v___y_1029_ = v___y_1115_;
v___y_1030_ = v___y_1116_;
v___y_1031_ = v___y_1110_;
v___y_1032_ = v___y_1112_;
v___y_1033_ = v_a_1124_;
v___y_1034_ = v___y_1111_;
v___y_1035_ = v___y_1114_;
v___y_1036_ = v_name_1107_;
v___y_1037_ = v___y_1113_;
v___y_1038_ = v___y_1117_;
v___y_1039_ = v___y_1108_;
v___y_1040_ = v___x_1131_;
goto v___jp_1027_;
}
}
else
{
lean_dec(v_name_1107_);
return v___x_1123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___boxed(lean_object* v_name_1202_, lean_object* v_type_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v_name_1202_, v_type_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
lean_dec(v_a_1205_);
lean_dec(v_a_1204_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0(lean_object* v_00_u03b2_1216_, lean_object* v_x_1217_, lean_object* v_x_1218_, lean_object* v_x_1219_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_x_1217_, v_x_1218_, v_x_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(lean_object* v_00_u03b2_1221_, lean_object* v_x_1222_, lean_object* v_x_1223_){
_start:
{
uint8_t v___x_1224_; 
v___x_1224_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_x_1222_, v_x_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___boxed(lean_object* v_00_u03b2_1225_, lean_object* v_x_1226_, lean_object* v_x_1227_){
_start:
{
uint8_t v_res_1228_; lean_object* v_r_1229_; 
v_res_1228_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(v_00_u03b2_1225_, v_x_1226_, v_x_1227_);
lean_dec(v_x_1227_);
lean_dec_ref(v_x_1226_);
v_r_1229_ = lean_box(v_res_1228_);
return v_r_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(lean_object* v_a_1230_, lean_object* v_inst_1231_, lean_object* v_a_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v_a_1230_, v_a_1232_, v___y_1233_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___boxed(lean_object* v_a_1245_, lean_object* v_inst_1246_, lean_object* v_a_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(v_a_1245_, v_inst_1246_, v_a_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec(v___y_1248_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(lean_object* v_00_u03b2_1260_, lean_object* v_x_1261_, lean_object* v_x_1262_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_x_1261_, v_x_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___boxed(lean_object* v_00_u03b2_1264_, lean_object* v_x_1265_, lean_object* v_x_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(v_00_u03b2_1264_, v_x_1265_, v_x_1266_);
lean_dec(v_x_1266_);
lean_dec_ref(v_x_1265_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(lean_object* v_00_u03b2_1268_, lean_object* v_x_1269_, size_t v_x_1270_, size_t v_x_1271_, lean_object* v_x_1272_, lean_object* v_x_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_1269_, v_x_1270_, v_x_1271_, v_x_1272_, v_x_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1275_, lean_object* v_x_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_, lean_object* v_x_1279_, lean_object* v_x_1280_){
_start:
{
size_t v_x_34456__boxed_1281_; size_t v_x_34457__boxed_1282_; lean_object* v_res_1283_; 
v_x_34456__boxed_1281_ = lean_unbox_usize(v_x_1277_);
lean_dec(v_x_1277_);
v_x_34457__boxed_1282_ = lean_unbox_usize(v_x_1278_);
lean_dec(v_x_1278_);
v_res_1283_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(v_00_u03b2_1275_, v_x_1276_, v_x_34456__boxed_1281_, v_x_34457__boxed_1282_, v_x_1279_, v_x_1280_);
return v_res_1283_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(lean_object* v_00_u03b2_1284_, lean_object* v_x_1285_, size_t v_x_1286_, lean_object* v_x_1287_){
_start:
{
uint8_t v___x_1288_; 
v___x_1288_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_1285_, v_x_1286_, v_x_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1289_, lean_object* v_x_1290_, lean_object* v_x_1291_, lean_object* v_x_1292_){
_start:
{
size_t v_x_34473__boxed_1293_; uint8_t v_res_1294_; lean_object* v_r_1295_; 
v_x_34473__boxed_1293_ = lean_unbox_usize(v_x_1291_);
lean_dec(v_x_1291_);
v_res_1294_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(v_00_u03b2_1289_, v_x_1290_, v_x_34473__boxed_1293_, v_x_1292_);
lean_dec(v_x_1292_);
lean_dec_ref(v_x_1290_);
v_r_1295_ = lean_box(v_res_1294_);
return v_r_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(lean_object* v_00_u03b2_1296_, lean_object* v_x_1297_, size_t v_x_1298_, lean_object* v_x_1299_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_1297_, v_x_1298_, v_x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1301_, lean_object* v_x_1302_, lean_object* v_x_1303_, lean_object* v_x_1304_){
_start:
{
size_t v_x_34484__boxed_1305_; lean_object* v_res_1306_; 
v_x_34484__boxed_1305_ = lean_unbox_usize(v_x_1303_);
lean_dec(v_x_1303_);
v_res_1306_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(v_00_u03b2_1301_, v_x_1302_, v_x_34484__boxed_1305_, v_x_1304_);
lean_dec(v_x_1304_);
lean_dec_ref(v_x_1302_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1307_, lean_object* v_n_1308_, lean_object* v_k_1309_, lean_object* v_v_1310_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(v_n_1308_, v_k_1309_, v_v_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1312_, size_t v_depth_1313_, lean_object* v_keys_1314_, lean_object* v_vals_1315_, lean_object* v_heq_1316_, lean_object* v_i_1317_, lean_object* v_entries_1318_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_depth_1313_, v_keys_1314_, v_vals_1315_, v_i_1317_, v_entries_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1320_, lean_object* v_depth_1321_, lean_object* v_keys_1322_, lean_object* v_vals_1323_, lean_object* v_heq_1324_, lean_object* v_i_1325_, lean_object* v_entries_1326_){
_start:
{
size_t v_depth_boxed_1327_; lean_object* v_res_1328_; 
v_depth_boxed_1327_ = lean_unbox_usize(v_depth_1321_);
lean_dec(v_depth_1321_);
v_res_1328_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(v_00_u03b2_1320_, v_depth_boxed_1327_, v_keys_1322_, v_vals_1323_, v_heq_1324_, v_i_1325_, v_entries_1326_);
lean_dec_ref(v_vals_1323_);
lean_dec_ref(v_keys_1322_);
return v_res_1328_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1329_, lean_object* v_keys_1330_, lean_object* v_vals_1331_, lean_object* v_heq_1332_, lean_object* v_i_1333_, lean_object* v_k_1334_){
_start:
{
uint8_t v___x_1335_; 
v___x_1335_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_keys_1330_, v_i_1333_, v_k_1334_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1336_, lean_object* v_keys_1337_, lean_object* v_vals_1338_, lean_object* v_heq_1339_, lean_object* v_i_1340_, lean_object* v_k_1341_){
_start:
{
uint8_t v_res_1342_; lean_object* v_r_1343_; 
v_res_1342_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(v_00_u03b2_1336_, v_keys_1337_, v_vals_1338_, v_heq_1339_, v_i_1340_, v_k_1341_);
lean_dec(v_k_1341_);
lean_dec_ref(v_vals_1338_);
lean_dec_ref(v_keys_1337_);
v_r_1343_ = lean_box(v_res_1342_);
return v_r_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_1344_, lean_object* v_keys_1345_, lean_object* v_vals_1346_, lean_object* v_heq_1347_, lean_object* v_i_1348_, lean_object* v_k_1349_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_keys_1345_, v_vals_1346_, v_i_1348_, v_k_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1351_, lean_object* v_keys_1352_, lean_object* v_vals_1353_, lean_object* v_heq_1354_, lean_object* v_i_1355_, lean_object* v_k_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(v_00_u03b2_1351_, v_keys_1352_, v_vals_1353_, v_heq_1354_, v_i_1355_, v_k_1356_);
lean_dec(v_k_1356_);
lean_dec_ref(v_vals_1353_);
lean_dec_ref(v_keys_1352_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1358_, lean_object* v_x_1359_, lean_object* v_x_1360_, lean_object* v_x_1361_, lean_object* v_x_1362_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1359_, v_x_1360_, v_x_1361_, v_x_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(lean_object* v_msgData_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; lean_object* v_env_1371_; uint8_t v___x_1372_; lean_object* v_env_1373_; lean_object* v___x_1374_; lean_object* v_toCold_1375_; lean_object* v_mctx_1376_; lean_object* v_lctx_1377_; lean_object* v_options_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1370_ = lean_st_ref_get(v___y_1368_);
v_env_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc_ref(v_env_1371_);
lean_dec(v___x_1370_);
v___x_1372_ = 0;
v_env_1373_ = l_Lean_Environment_setRecordingDeps(v_env_1371_, v___x_1372_);
v___x_1374_ = lean_st_ref_get(v___y_1366_);
v_toCold_1375_ = lean_ctor_get(v___y_1367_, 0);
v_mctx_1376_ = lean_ctor_get(v___x_1374_, 0);
lean_inc_ref(v_mctx_1376_);
lean_dec(v___x_1374_);
v_lctx_1377_ = lean_ctor_get(v___y_1365_, 2);
v_options_1378_ = lean_ctor_get(v_toCold_1375_, 2);
lean_inc_ref(v_options_1378_);
lean_inc_ref(v_lctx_1377_);
v___x_1379_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1379_, 0, v_env_1373_);
lean_ctor_set(v___x_1379_, 1, v_mctx_1376_);
lean_ctor_set(v___x_1379_, 2, v_lctx_1377_);
lean_ctor_set(v___x_1379_, 3, v_options_1378_);
v___x_1380_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
lean_ctor_set(v___x_1380_, 1, v_msgData_1364_);
v___x_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0___boxed(lean_object* v_msgData_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(v_msgData_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(lean_object* v_msg_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v_ref_1395_; lean_object* v___x_1396_; lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1405_; 
v_ref_1395_ = lean_ctor_get(v___y_1392_, 2);
v___x_1396_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(v_msg_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1399_ = v___x_1396_;
v_isShared_1400_ = v_isSharedCheck_1405_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1405_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; lean_object* v___x_1403_; 
lean_inc(v_ref_1395_);
v___x_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1401_, 0, v_ref_1395_);
lean_ctor_set(v___x_1401_, 1, v_a_1397_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set_tag(v___x_1399_, 1);
lean_ctor_set(v___x_1399_, 0, v___x_1401_);
v___x_1403_ = v___x_1399_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1401_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg___boxed(lean_object* v_msg_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v_msg_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
return v_res_1412_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1(void){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__0));
v___x_1415_ = l_Lean_stringToMessageData(v___x_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v_fst_1428_; lean_object* v_snd_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___x_1492_; lean_object* v_mvarId_1493_; lean_object* v___x_1494_; 
v___x_1492_ = lean_st_ref_get(v_a_1416_);
v_mvarId_1493_ = lean_ctor_get(v___x_1492_, 1);
lean_inc(v_mvarId_1493_);
lean_dec(v___x_1492_);
v___x_1494_ = l_Lean_MVarId_getType(v_mvarId_1493_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1495_);
lean_dec_ref_known(v___x_1494_, 1);
switch(lean_obj_tag(v_a_1495_))
{
case 7:
{
lean_object* v_binderName_1496_; lean_object* v_binderType_1497_; 
v_binderName_1496_ = lean_ctor_get(v_a_1495_, 0);
lean_inc(v_binderName_1496_);
v_binderType_1497_ = lean_ctor_get(v_a_1495_, 1);
lean_inc_ref(v_binderType_1497_);
lean_dec_ref_known(v_a_1495_, 3);
v_fst_1428_ = v_binderName_1496_;
v_snd_1429_ = v_binderType_1497_;
v___y_1430_ = v_a_1416_;
v___y_1431_ = v_a_1417_;
v___y_1432_ = v_a_1418_;
v___y_1433_ = v_a_1419_;
v___y_1434_ = v_a_1420_;
v___y_1435_ = v_a_1421_;
v___y_1436_ = v_a_1422_;
v___y_1437_ = v_a_1423_;
v___y_1438_ = v_a_1424_;
v___y_1439_ = v_a_1425_;
goto v___jp_1427_;
}
case 8:
{
lean_object* v_declName_1498_; lean_object* v_type_1499_; 
v_declName_1498_ = lean_ctor_get(v_a_1495_, 0);
lean_inc(v_declName_1498_);
v_type_1499_ = lean_ctor_get(v_a_1495_, 1);
lean_inc_ref(v_type_1499_);
lean_dec_ref_known(v_a_1495_, 4);
v_fst_1428_ = v_declName_1498_;
v_snd_1429_ = v_type_1499_;
v___y_1430_ = v_a_1416_;
v___y_1431_ = v_a_1417_;
v___y_1432_ = v_a_1418_;
v___y_1433_ = v_a_1419_;
v___y_1434_ = v_a_1420_;
v___y_1435_ = v_a_1421_;
v___y_1436_ = v_a_1422_;
v___y_1437_ = v_a_1423_;
v___y_1438_ = v_a_1424_;
v___y_1439_ = v_a_1425_;
goto v___jp_1427_;
}
default: 
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
lean_dec(v_a_1495_);
v___x_1500_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1);
v___x_1501_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v___x_1500_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_);
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1501_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1501_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
v_a_1510_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1494_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1494_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
v___jp_1427_:
{
lean_object* v___x_1440_; 
v___x_1440_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v_fst_1428_, v_snd_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v___x_1442_; lean_object* v_mvarId_1443_; lean_object* v___x_1444_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___x_1440_, 1);
v___x_1442_ = lean_st_ref_get(v___y_1430_);
v_mvarId_1443_ = lean_ctor_get(v___x_1442_, 1);
lean_inc(v_mvarId_1443_);
lean_dec(v___x_1442_);
v___x_1444_ = l_Lean_MVarId_intro(v_mvarId_1443_, v_a_1441_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v_fst_1446_; lean_object* v_snd_1447_; lean_object* v___x_1448_; lean_object* v_toGoalState_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1474_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref_known(v___x_1444_, 1);
v_fst_1446_ = lean_ctor_get(v_a_1445_, 0);
lean_inc(v_fst_1446_);
v_snd_1447_ = lean_ctor_get(v_a_1445_, 1);
lean_inc(v_snd_1447_);
lean_dec(v_a_1445_);
v___x_1448_ = lean_st_ref_take(v___y_1430_);
v_toGoalState_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1474_ == 0)
{
lean_object* v_unused_1475_; 
v_unused_1475_ = lean_ctor_get(v___x_1448_, 1);
lean_dec(v_unused_1475_);
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1474_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_toGoalState_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1474_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 1, v_snd_1447_);
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_toGoalState_1449_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_snd_1447_);
v___x_1454_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_st_ref_put(v___y_1430_, v___x_1454_);
lean_inc(v_fst_1446_);
v___x_1456_ = l_Lean_Meta_Grind_registerFVarAnchor___redArg(v_fst_1446_, v___y_1430_, v___y_1432_, v___y_1433_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v___x_1456_, 0);
lean_dec(v_unused_1464_);
v___x_1458_ = v___x_1456_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_dec(v___x_1456_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 0, v_fst_1446_);
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_fst_1446_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec(v_fst_1446_);
v_a_1465_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1456_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1456_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
v_a_1476_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1444_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1444_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
v_a_1484_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1440_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1440_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___boxed(lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_);
lean_dec(v_a_1527_);
lean_dec_ref(v_a_1526_);
lean_dec(v_a_1525_);
lean_dec_ref(v_a_1524_);
lean_dec(v_a_1523_);
lean_dec_ref(v_a_1522_);
lean_dec(v_a_1521_);
lean_dec_ref(v_a_1520_);
lean_dec(v_a_1519_);
lean_dec(v_a_1518_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0(lean_object* v_00_u03b1_1530_, lean_object* v_msg_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v_msg_1531_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___boxed(lean_object* v_00_u03b1_1544_, lean_object* v_msg_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0(v_00_u03b1_1544_, v_msg_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec(v___y_1546_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(lean_object* v_x_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v___x_1570_; 
lean_inc(v___y_1564_);
lean_inc_ref(v___y_1563_);
lean_inc(v___y_1562_);
lean_inc_ref(v___y_1561_);
lean_inc(v___y_1560_);
lean_inc(v___y_1559_);
v___x_1570_ = lean_apply_11(v_x_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, lean_box(0));
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0___boxed(lean_object* v_x_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(v_x_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec(v___y_1572_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(lean_object* v_mvarId_1584_, lean_object* v_x_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___f_1597_; lean_object* v___x_1598_; 
lean_inc(v___y_1591_);
lean_inc_ref(v___y_1590_);
lean_inc(v___y_1589_);
lean_inc_ref(v___y_1588_);
lean_inc(v___y_1587_);
lean_inc(v___y_1586_);
v___f_1597_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_1597_, 0, v_x_1585_);
lean_closure_set(v___f_1597_, 1, v___y_1586_);
lean_closure_set(v___f_1597_, 2, v___y_1587_);
lean_closure_set(v___f_1597_, 3, v___y_1588_);
lean_closure_set(v___f_1597_, 4, v___y_1589_);
lean_closure_set(v___f_1597_, 5, v___y_1590_);
lean_closure_set(v___f_1597_, 6, v___y_1591_);
v___x_1598_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1584_, v___f_1597_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
if (lean_obj_tag(v___x_1598_) == 0)
{
return v___x_1598_;
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1598_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1598_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___boxed(lean_object* v_mvarId_1607_, lean_object* v_x_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_1607_, v_x_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
lean_dec(v___y_1609_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(lean_object* v_00_u03b1_1621_, lean_object* v_mvarId_1622_, lean_object* v_x_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_1622_, v_x_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___boxed(lean_object* v_00_u03b1_1636_, lean_object* v_mvarId_1637_, lean_object* v_x_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(v_00_u03b1_1636_, v_mvarId_1637_, v_x_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec(v___y_1639_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0(lean_object* v_x_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v___x_1662_; 
lean_inc(v___y_1656_);
lean_inc_ref(v___y_1655_);
lean_inc(v___y_1654_);
lean_inc_ref(v___y_1653_);
lean_inc(v___y_1652_);
v___x_1662_ = lean_apply_10(v_x_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, lean_box(0));
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0___boxed(lean_object* v_x_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0(v_x_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(lean_object* v_mvarId_1675_, lean_object* v_x_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v___f_1687_; lean_object* v___x_1688_; 
lean_inc(v___y_1681_);
lean_inc_ref(v___y_1680_);
lean_inc(v___y_1679_);
lean_inc_ref(v___y_1678_);
lean_inc(v___y_1677_);
v___f_1687_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1687_, 0, v_x_1676_);
lean_closure_set(v___f_1687_, 1, v___y_1677_);
lean_closure_set(v___f_1687_, 2, v___y_1678_);
lean_closure_set(v___f_1687_, 3, v___y_1679_);
lean_closure_set(v___f_1687_, 4, v___y_1680_);
lean_closure_set(v___f_1687_, 5, v___y_1681_);
v___x_1688_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1675_, v___f_1687_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1688_) == 0)
{
return v___x_1688_;
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1688_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1688_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___boxed(lean_object* v_mvarId_1697_, lean_object* v_x_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_1697_, v_x_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3(lean_object* v_00_u03b1_1710_, lean_object* v_mvarId_1711_, lean_object* v_x_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_1711_, v_x_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___boxed(lean_object* v_00_u03b1_1724_, lean_object* v_mvarId_1725_, lean_object* v_x_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3(v_00_u03b1_1724_, v_mvarId_1725_, v_x_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(lean_object* v_a_1738_, lean_object* v_generation_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v___x_1751_; 
lean_inc(v_a_1738_);
v___x_1751_ = l_Lean_FVarId_getDecl___redArg(v_a_1738_, v___y_1746_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1752_);
lean_dec_ref_known(v___x_1751_, 1);
v___x_1753_ = l_Lean_LocalDecl_type(v_a_1752_);
lean_dec(v_a_1752_);
lean_inc_ref(v___x_1753_);
v___x_1754_ = l_Lean_Meta_isProp(v___x_1753_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; uint8_t v___x_1756_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1754_, 1);
v___x_1756_ = lean_unbox(v_a_1755_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; 
lean_dec_ref(v___x_1753_);
lean_inc(v_a_1738_);
v___x_1757_ = l_Lean_FVarId_getDecl___redArg(v_a_1738_, v___y_1746_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; uint8_t v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref_known(v___x_1757_, 1);
v___x_1759_ = lean_unbox(v_a_1755_);
lean_dec(v_a_1755_);
v___x_1760_ = l_Lean_LocalDecl_value(v_a_1758_, v___x_1759_);
lean_dec(v_a_1758_);
v___x_1761_ = l_Lean_Meta_Grind_preprocessHypothesis(v___x_1760_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v___x_1761_, 1);
lean_inc(v_a_1738_);
v___x_1763_ = l_Lean_mkFVar(v_a_1738_);
v___x_1764_ = l_Lean_Meta_Sym_shareCommon(v___x_1763_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1766_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
lean_inc(v_a_1762_);
v___x_1766_ = l_Lean_Meta_Simp_Result_getProof(v_a_1762_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v_expr_1768_; lean_object* v___x_1769_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v_expr_1768_ = lean_ctor_get(v_a_1762_, 0);
lean_inc_ref(v_expr_1768_);
lean_dec(v_a_1762_);
v___x_1769_ = l_Lean_Meta_Grind_addNewEq(v_a_1765_, v_expr_1768_, v_a_1767_, v_generation_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1778_; 
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1778_ == 0)
{
lean_object* v_unused_1779_; 
v_unused_1779_ = lean_ctor_get(v___x_1769_, 0);
lean_dec(v_unused_1779_);
v___x_1771_ = v___x_1769_;
v_isShared_1772_ = v_isSharedCheck_1778_;
goto v_resetjp_1770_;
}
else
{
lean_dec(v___x_1769_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1778_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1776_; 
v___x_1773_ = lean_st_ref_get(v___y_1740_);
v___x_1774_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1774_, 0, v_a_1738_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1774_);
v___x_1776_ = v___x_1771_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1774_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec(v_a_1738_);
v_a_1780_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1769_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1769_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec(v_a_1765_);
lean_dec(v_a_1762_);
lean_dec(v_generation_1739_);
lean_dec(v_a_1738_);
v_a_1788_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1766_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1766_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_dec(v_a_1762_);
lean_dec(v_generation_1739_);
lean_dec(v_a_1738_);
v_a_1796_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1764_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1764_);
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
lean_dec(v_generation_1739_);
lean_dec(v_a_1738_);
v_a_1804_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___x_1761_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1761_);
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
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
lean_dec(v_a_1755_);
lean_dec(v_generation_1739_);
lean_dec(v_a_1738_);
v_a_1812_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1757_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1757_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
lean_dec(v_a_1755_);
lean_dec(v_generation_1739_);
v___x_1820_ = lean_st_ref_get(v___y_1740_);
v___x_1821_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
lean_inc_ref(v___x_1753_);
v___x_1822_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v___x_1821_, v___x_1753_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v_mvarId_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_a_1823_);
lean_dec_ref_known(v___x_1822_, 1);
v_mvarId_1824_ = lean_ctor_get(v___x_1820_, 1);
lean_inc(v_mvarId_1824_);
lean_dec(v___x_1820_);
v___x_1825_ = l_Lean_mkFVar(v_a_1738_);
v___x_1826_ = l_Lean_MVarId_assert(v_mvarId_1824_, v_a_1823_, v___x_1753_, v___x_1825_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1845_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1829_ = v___x_1826_;
v_isShared_1830_ = v_isSharedCheck_1845_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1826_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1845_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1831_; lean_object* v_toGoalState_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1843_; 
v___x_1831_ = lean_st_ref_get(v___y_1740_);
v_toGoalState_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1843_ == 0)
{
lean_object* v_unused_1844_; 
v_unused_1844_ = lean_ctor_get(v___x_1831_, 1);
lean_dec(v_unused_1844_);
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1843_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_toGoalState_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1843_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 1, v_a_1827_);
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_toGoalState_1832_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_a_1827_);
v___x_1837_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1838_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1838_);
v___x_1840_ = v___x_1829_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
v_a_1846_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1826_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1826_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_dec(v___x_1820_);
lean_dec_ref(v___x_1753_);
lean_dec(v_a_1738_);
v_a_1854_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1822_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1822_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec_ref(v___x_1753_);
lean_dec(v_generation_1739_);
lean_dec(v_a_1738_);
v_a_1862_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1754_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1754_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec(v_generation_1739_);
lean_dec(v_a_1738_);
v_a_1870_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1751_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1751_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed(lean_object* v_a_1878_, lean_object* v_generation_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(v_a_1878_, v_generation_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec(v___y_1880_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(lean_object* v_x_1892_, lean_object* v_x_1893_, lean_object* v_x_1894_, lean_object* v_x_1895_){
_start:
{
lean_object* v_ks_1896_; lean_object* v_vs_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1921_; 
v_ks_1896_ = lean_ctor_get(v_x_1892_, 0);
v_vs_1897_ = lean_ctor_get(v_x_1892_, 1);
v_isSharedCheck_1921_ = !lean_is_exclusive(v_x_1892_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1899_ = v_x_1892_;
v_isShared_1900_ = v_isSharedCheck_1921_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_vs_1897_);
lean_inc(v_ks_1896_);
lean_dec(v_x_1892_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1921_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; uint8_t v___x_1902_; 
v___x_1901_ = lean_array_get_size(v_ks_1896_);
v___x_1902_ = lean_nat_dec_lt(v_x_1893_, v___x_1901_);
if (v___x_1902_ == 0)
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1906_; 
lean_dec(v_x_1893_);
v___x_1903_ = lean_array_push(v_ks_1896_, v_x_1894_);
v___x_1904_ = lean_array_push(v_vs_1897_, v_x_1895_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 1, v___x_1904_);
lean_ctor_set(v___x_1899_, 0, v___x_1903_);
v___x_1906_ = v___x_1899_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1903_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
else
{
lean_object* v_k_x27_1908_; uint8_t v___x_1909_; 
v_k_x27_1908_ = lean_array_fget_borrowed(v_ks_1896_, v_x_1893_);
v___x_1909_ = l_Lean_instBEqMVarId_beq(v_x_1894_, v_k_x27_1908_);
if (v___x_1909_ == 0)
{
lean_object* v___x_1911_; 
if (v_isShared_1900_ == 0)
{
v___x_1911_ = v___x_1899_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_ks_1896_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_vs_1897_);
v___x_1911_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = lean_unsigned_to_nat(1u);
v___x_1913_ = lean_nat_add(v_x_1893_, v___x_1912_);
lean_dec(v_x_1893_);
v_x_1892_ = v___x_1911_;
v_x_1893_ = v___x_1913_;
goto _start;
}
}
else
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1919_; 
v___x_1916_ = lean_array_fset(v_ks_1896_, v_x_1893_, v_x_1894_);
v___x_1917_ = lean_array_fset(v_vs_1897_, v_x_1893_, v_x_1895_);
lean_dec(v_x_1893_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 1, v___x_1917_);
lean_ctor_set(v___x_1899_, 0, v___x_1916_);
v___x_1919_ = v___x_1899_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1916_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v___x_1917_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(lean_object* v_n_1922_, lean_object* v_k_1923_, lean_object* v_v_1924_){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = lean_unsigned_to_nat(0u);
v___x_1926_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_n_1922_, v___x_1925_, v_k_1923_, v_v_1924_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1927_, size_t v_x_1928_, size_t v_x_1929_, lean_object* v_x_1930_, lean_object* v_x_1931_){
_start:
{
if (lean_obj_tag(v_x_1927_) == 0)
{
lean_object* v_es_1932_; size_t v___x_1933_; size_t v___x_1934_; lean_object* v_j_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; 
v_es_1932_ = lean_ctor_get(v_x_1927_, 0);
v___x_1933_ = ((size_t)31ULL);
v___x_1934_ = lean_usize_land(v_x_1928_, v___x_1933_);
v_j_1935_ = lean_usize_to_nat(v___x_1934_);
v___x_1936_ = lean_array_get_size(v_es_1932_);
v___x_1937_ = lean_nat_dec_lt(v_j_1935_, v___x_1936_);
if (v___x_1937_ == 0)
{
lean_dec(v_j_1935_);
lean_dec(v_x_1931_);
lean_dec(v_x_1930_);
return v_x_1927_;
}
else
{
lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1976_; 
lean_inc_ref(v_es_1932_);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_1976_ == 0)
{
lean_object* v_unused_1977_; 
v_unused_1977_ = lean_ctor_get(v_x_1927_, 0);
lean_dec(v_unused_1977_);
v___x_1939_ = v_x_1927_;
v_isShared_1940_ = v_isSharedCheck_1976_;
goto v_resetjp_1938_;
}
else
{
lean_dec(v_x_1927_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1976_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v_v_1941_; lean_object* v___x_1942_; lean_object* v_xs_x27_1943_; lean_object* v___y_1945_; 
v_v_1941_ = lean_array_fget(v_es_1932_, v_j_1935_);
v___x_1942_ = lean_box(0);
v_xs_x27_1943_ = lean_array_fset(v_es_1932_, v_j_1935_, v___x_1942_);
switch(lean_obj_tag(v_v_1941_))
{
case 0:
{
lean_object* v_key_1950_; lean_object* v_val_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1961_; 
v_key_1950_ = lean_ctor_get(v_v_1941_, 0);
v_val_1951_ = lean_ctor_get(v_v_1941_, 1);
v_isSharedCheck_1961_ = !lean_is_exclusive(v_v_1941_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1953_ = v_v_1941_;
v_isShared_1954_ = v_isSharedCheck_1961_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_val_1951_);
lean_inc(v_key_1950_);
lean_dec(v_v_1941_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1961_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
uint8_t v___x_1955_; 
v___x_1955_ = l_Lean_instBEqMVarId_beq(v_x_1930_, v_key_1950_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
lean_del_object(v___x_1953_);
v___x_1956_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1950_, v_val_1951_, v_x_1930_, v_x_1931_);
v___x_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1956_);
v___y_1945_ = v___x_1957_;
goto v___jp_1944_;
}
else
{
lean_object* v___x_1959_; 
lean_dec(v_val_1951_);
lean_dec(v_key_1950_);
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 1, v_x_1931_);
lean_ctor_set(v___x_1953_, 0, v_x_1930_);
v___x_1959_ = v___x_1953_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_x_1930_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v_x_1931_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
v___y_1945_ = v___x_1959_;
goto v___jp_1944_;
}
}
}
}
case 1:
{
lean_object* v_node_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1974_; 
v_node_1962_ = lean_ctor_get(v_v_1941_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_v_1941_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1964_ = v_v_1941_;
v_isShared_1965_ = v_isSharedCheck_1974_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_node_1962_);
lean_dec(v_v_1941_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1974_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
size_t v___x_1966_; size_t v___x_1967_; size_t v___x_1968_; size_t v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1972_; 
v___x_1966_ = ((size_t)5ULL);
v___x_1967_ = lean_usize_shift_right(v_x_1928_, v___x_1966_);
v___x_1968_ = ((size_t)1ULL);
v___x_1969_ = lean_usize_add(v_x_1929_, v___x_1968_);
v___x_1970_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_node_1962_, v___x_1967_, v___x_1969_, v_x_1930_, v_x_1931_);
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 0, v___x_1970_);
v___x_1972_ = v___x_1964_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
v___y_1945_ = v___x_1972_;
goto v___jp_1944_;
}
}
}
default: 
{
lean_object* v___x_1975_; 
v___x_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1975_, 0, v_x_1930_);
lean_ctor_set(v___x_1975_, 1, v_x_1931_);
v___y_1945_ = v___x_1975_;
goto v___jp_1944_;
}
}
v___jp_1944_:
{
lean_object* v___x_1946_; lean_object* v___x_1948_; 
v___x_1946_ = lean_array_fset(v_xs_x27_1943_, v_j_1935_, v___y_1945_);
lean_dec(v_j_1935_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v___x_1946_);
v___x_1948_ = v___x_1939_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1946_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
else
{
lean_object* v_ks_1978_; lean_object* v_vs_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1997_; 
v_ks_1978_ = lean_ctor_get(v_x_1927_, 0);
v_vs_1979_ = lean_ctor_get(v_x_1927_, 1);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1981_ = v_x_1927_;
v_isShared_1982_ = v_isSharedCheck_1997_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_vs_1979_);
lean_inc(v_ks_1978_);
lean_dec(v_x_1927_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1997_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_ks_1978_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v_vs_1979_);
v___x_1984_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v_newNode_1985_; size_t v___x_1986_; uint8_t v___x_1987_; 
v_newNode_1985_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(v___x_1984_, v_x_1930_, v_x_1931_);
v___x_1986_ = ((size_t)7ULL);
v___x_1987_ = lean_usize_dec_le(v___x_1986_, v_x_1929_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; 
v___x_1988_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1985_);
v___x_1989_ = lean_unsigned_to_nat(4u);
v___x_1990_ = lean_nat_dec_lt(v___x_1988_, v___x_1989_);
lean_dec(v___x_1988_);
if (v___x_1990_ == 0)
{
lean_object* v_ks_1991_; lean_object* v_vs_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v_ks_1991_ = lean_ctor_get(v_newNode_1985_, 0);
lean_inc_ref(v_ks_1991_);
v_vs_1992_ = lean_ctor_get(v_newNode_1985_, 1);
lean_inc_ref(v_vs_1992_);
lean_dec_ref(v_newNode_1985_);
v___x_1993_ = lean_unsigned_to_nat(0u);
v___x_1994_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0);
v___x_1995_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_x_1929_, v_ks_1991_, v_vs_1992_, v___x_1993_, v___x_1994_);
lean_dec_ref(v_vs_1992_);
lean_dec_ref(v_ks_1991_);
return v___x_1995_;
}
else
{
return v_newNode_1985_;
}
}
else
{
return v_newNode_1985_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(size_t v_depth_1998_, lean_object* v_keys_1999_, lean_object* v_vals_2000_, lean_object* v_i_2001_, lean_object* v_entries_2002_){
_start:
{
lean_object* v___x_2003_; uint8_t v___x_2004_; 
v___x_2003_ = lean_array_get_size(v_keys_1999_);
v___x_2004_ = lean_nat_dec_lt(v_i_2001_, v___x_2003_);
if (v___x_2004_ == 0)
{
lean_dec(v_i_2001_);
return v_entries_2002_;
}
else
{
lean_object* v_k_2005_; lean_object* v_v_2006_; uint64_t v___x_2007_; size_t v_h_2008_; size_t v___x_2009_; lean_object* v___x_2010_; size_t v___x_2011_; size_t v___x_2012_; size_t v___x_2013_; size_t v_h_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v_k_2005_ = lean_array_fget_borrowed(v_keys_1999_, v_i_2001_);
v_v_2006_ = lean_array_fget_borrowed(v_vals_2000_, v_i_2001_);
v___x_2007_ = l_Lean_instHashableMVarId_hash(v_k_2005_);
v_h_2008_ = lean_uint64_to_usize(v___x_2007_);
v___x_2009_ = ((size_t)5ULL);
v___x_2010_ = lean_unsigned_to_nat(1u);
v___x_2011_ = ((size_t)1ULL);
v___x_2012_ = lean_usize_sub(v_depth_1998_, v___x_2011_);
v___x_2013_ = lean_usize_mul(v___x_2009_, v___x_2012_);
v_h_2014_ = lean_usize_shift_right(v_h_2008_, v___x_2013_);
v___x_2015_ = lean_nat_add(v_i_2001_, v___x_2010_);
lean_dec(v_i_2001_);
lean_inc(v_v_2006_);
lean_inc(v_k_2005_);
v___x_2016_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_entries_2002_, v_h_2014_, v_depth_1998_, v_k_2005_, v_v_2006_);
v_i_2001_ = v___x_2015_;
v_entries_2002_ = v___x_2016_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_depth_2018_, lean_object* v_keys_2019_, lean_object* v_vals_2020_, lean_object* v_i_2021_, lean_object* v_entries_2022_){
_start:
{
size_t v_depth_boxed_2023_; lean_object* v_res_2024_; 
v_depth_boxed_2023_ = lean_unbox_usize(v_depth_2018_);
lean_dec(v_depth_2018_);
v_res_2024_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_boxed_2023_, v_keys_2019_, v_vals_2020_, v_i_2021_, v_entries_2022_);
lean_dec_ref(v_vals_2020_);
lean_dec_ref(v_keys_2019_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_2025_, lean_object* v_x_2026_, lean_object* v_x_2027_, lean_object* v_x_2028_, lean_object* v_x_2029_){
_start:
{
size_t v_x_160063__boxed_2030_; size_t v_x_160064__boxed_2031_; lean_object* v_res_2032_; 
v_x_160063__boxed_2030_ = lean_unbox_usize(v_x_2026_);
lean_dec(v_x_2026_);
v_x_160064__boxed_2031_ = lean_unbox_usize(v_x_2027_);
lean_dec(v_x_2027_);
v_res_2032_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_2025_, v_x_160063__boxed_2030_, v_x_160064__boxed_2031_, v_x_2028_, v_x_2029_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(lean_object* v_x_2033_, lean_object* v_x_2034_, lean_object* v_x_2035_){
_start:
{
uint64_t v___x_2036_; size_t v___x_2037_; size_t v___x_2038_; lean_object* v___x_2039_; 
v___x_2036_ = l_Lean_instHashableMVarId_hash(v_x_2034_);
v___x_2037_ = lean_uint64_to_usize(v___x_2036_);
v___x_2038_ = ((size_t)1ULL);
v___x_2039_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_2033_, v___x_2037_, v___x_2038_, v_x_2034_, v_x_2035_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(lean_object* v_mvarId_2040_, lean_object* v_val_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v___x_2044_; lean_object* v_mctx_2045_; lean_object* v_cache_2046_; lean_object* v_zetaDeltaFVarIds_2047_; lean_object* v_postponed_2048_; lean_object* v_diag_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2077_; 
v___x_2044_ = lean_st_ref_take(v___y_2042_);
v_mctx_2045_ = lean_ctor_get(v___x_2044_, 0);
v_cache_2046_ = lean_ctor_get(v___x_2044_, 1);
v_zetaDeltaFVarIds_2047_ = lean_ctor_get(v___x_2044_, 2);
v_postponed_2048_ = lean_ctor_get(v___x_2044_, 3);
v_diag_2049_ = lean_ctor_get(v___x_2044_, 4);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2051_ = v___x_2044_;
v_isShared_2052_ = v_isSharedCheck_2077_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_diag_2049_);
lean_inc(v_postponed_2048_);
lean_inc(v_zetaDeltaFVarIds_2047_);
lean_inc(v_cache_2046_);
lean_inc(v_mctx_2045_);
lean_dec(v___x_2044_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2077_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v_depth_2053_; lean_object* v_levelAssignDepth_2054_; lean_object* v_lmvarCounter_2055_; lean_object* v_mvarCounter_2056_; lean_object* v_lDecls_2057_; lean_object* v_decls_2058_; lean_object* v_userNames_2059_; lean_object* v_lAssignment_2060_; lean_object* v_eAssignment_2061_; lean_object* v_dAssignment_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2076_; 
v_depth_2053_ = lean_ctor_get(v_mctx_2045_, 0);
v_levelAssignDepth_2054_ = lean_ctor_get(v_mctx_2045_, 1);
v_lmvarCounter_2055_ = lean_ctor_get(v_mctx_2045_, 2);
v_mvarCounter_2056_ = lean_ctor_get(v_mctx_2045_, 3);
v_lDecls_2057_ = lean_ctor_get(v_mctx_2045_, 4);
v_decls_2058_ = lean_ctor_get(v_mctx_2045_, 5);
v_userNames_2059_ = lean_ctor_get(v_mctx_2045_, 6);
v_lAssignment_2060_ = lean_ctor_get(v_mctx_2045_, 7);
v_eAssignment_2061_ = lean_ctor_get(v_mctx_2045_, 8);
v_dAssignment_2062_ = lean_ctor_get(v_mctx_2045_, 9);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_mctx_2045_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2064_ = v_mctx_2045_;
v_isShared_2065_ = v_isSharedCheck_2076_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_dAssignment_2062_);
lean_inc(v_eAssignment_2061_);
lean_inc(v_lAssignment_2060_);
lean_inc(v_userNames_2059_);
lean_inc(v_decls_2058_);
lean_inc(v_lDecls_2057_);
lean_inc(v_mvarCounter_2056_);
lean_inc(v_lmvarCounter_2055_);
lean_inc(v_levelAssignDepth_2054_);
lean_inc(v_depth_2053_);
lean_dec(v_mctx_2045_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2076_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2066_ = lean_box(0);
v___x_2067_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_eAssignment_2061_, v_mvarId_2040_, v_val_2041_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 8, v___x_2067_);
v___x_2069_ = v___x_2064_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_depth_2053_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_levelAssignDepth_2054_);
lean_ctor_set(v_reuseFailAlloc_2075_, 2, v_lmvarCounter_2055_);
lean_ctor_set(v_reuseFailAlloc_2075_, 3, v_mvarCounter_2056_);
lean_ctor_set(v_reuseFailAlloc_2075_, 4, v_lDecls_2057_);
lean_ctor_set(v_reuseFailAlloc_2075_, 5, v_decls_2058_);
lean_ctor_set(v_reuseFailAlloc_2075_, 6, v_userNames_2059_);
lean_ctor_set(v_reuseFailAlloc_2075_, 7, v_lAssignment_2060_);
lean_ctor_set(v_reuseFailAlloc_2075_, 8, v___x_2067_);
lean_ctor_set(v_reuseFailAlloc_2075_, 9, v_dAssignment_2062_);
v___x_2069_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2071_; 
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v___x_2069_);
v___x_2071_ = v___x_2051_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2069_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_cache_2046_);
lean_ctor_set(v_reuseFailAlloc_2074_, 2, v_zetaDeltaFVarIds_2047_);
lean_ctor_set(v_reuseFailAlloc_2074_, 3, v_postponed_2048_);
lean_ctor_set(v_reuseFailAlloc_2074_, 4, v_diag_2049_);
v___x_2071_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = lean_st_ref_put(v___y_2042_, v___x_2071_);
v___x_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2066_);
return v___x_2073_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg___boxed(lean_object* v_mvarId_2078_, lean_object* v_val_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2078_, v_val_2079_, v___y_2080_);
lean_dec(v___y_2080_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(lean_object* v___y_2083_){
_start:
{
lean_object* v___x_2085_; lean_object* v_ngen_2086_; lean_object* v_namePrefix_2087_; lean_object* v_idx_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2118_; 
v___x_2085_ = lean_st_ref_get(v___y_2083_);
v_ngen_2086_ = lean_ctor_get(v___x_2085_, 2);
lean_inc_ref(v_ngen_2086_);
lean_dec(v___x_2085_);
v_namePrefix_2087_ = lean_ctor_get(v_ngen_2086_, 0);
v_idx_2088_ = lean_ctor_get(v_ngen_2086_, 1);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_ngen_2086_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2090_ = v_ngen_2086_;
v_isShared_2091_ = v_isSharedCheck_2118_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_idx_2088_);
lean_inc(v_namePrefix_2087_);
lean_dec(v_ngen_2086_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2118_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v_r_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2096_; 
lean_inc(v_idx_2088_);
lean_inc(v_namePrefix_2087_);
v_r_2092_ = l_Lean_Name_num___override(v_namePrefix_2087_, v_idx_2088_);
v___x_2093_ = lean_unsigned_to_nat(1u);
v___x_2094_ = lean_nat_add(v_idx_2088_, v___x_2093_);
lean_dec(v_idx_2088_);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 1, v___x_2094_);
v___x_2096_ = v___x_2090_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_namePrefix_2087_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v___x_2094_);
v___x_2096_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
lean_object* v___x_2097_; lean_object* v_env_2098_; lean_object* v_nextMacroScope_2099_; lean_object* v_auxDeclNGen_2100_; lean_object* v_traceState_2101_; lean_object* v_cache_2102_; lean_object* v_recordedDeps_2103_; lean_object* v_messages_2104_; lean_object* v_infoState_2105_; lean_object* v_snapshotTasks_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2115_; 
v___x_2097_ = lean_st_ref_take(v___y_2083_);
v_env_2098_ = lean_ctor_get(v___x_2097_, 0);
v_nextMacroScope_2099_ = lean_ctor_get(v___x_2097_, 1);
v_auxDeclNGen_2100_ = lean_ctor_get(v___x_2097_, 3);
v_traceState_2101_ = lean_ctor_get(v___x_2097_, 4);
v_cache_2102_ = lean_ctor_get(v___x_2097_, 5);
v_recordedDeps_2103_ = lean_ctor_get(v___x_2097_, 6);
v_messages_2104_ = lean_ctor_get(v___x_2097_, 7);
v_infoState_2105_ = lean_ctor_get(v___x_2097_, 8);
v_snapshotTasks_2106_ = lean_ctor_get(v___x_2097_, 9);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2115_ == 0)
{
lean_object* v_unused_2116_; 
v_unused_2116_ = lean_ctor_get(v___x_2097_, 2);
lean_dec(v_unused_2116_);
v___x_2108_ = v___x_2097_;
v_isShared_2109_ = v_isSharedCheck_2115_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_snapshotTasks_2106_);
lean_inc(v_infoState_2105_);
lean_inc(v_messages_2104_);
lean_inc(v_recordedDeps_2103_);
lean_inc(v_cache_2102_);
lean_inc(v_traceState_2101_);
lean_inc(v_auxDeclNGen_2100_);
lean_inc(v_nextMacroScope_2099_);
lean_inc(v_env_2098_);
lean_dec(v___x_2097_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2115_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 2, v___x_2096_);
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_env_2098_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v_nextMacroScope_2099_);
lean_ctor_set(v_reuseFailAlloc_2114_, 2, v___x_2096_);
lean_ctor_set(v_reuseFailAlloc_2114_, 3, v_auxDeclNGen_2100_);
lean_ctor_set(v_reuseFailAlloc_2114_, 4, v_traceState_2101_);
lean_ctor_set(v_reuseFailAlloc_2114_, 5, v_cache_2102_);
lean_ctor_set(v_reuseFailAlloc_2114_, 6, v_recordedDeps_2103_);
lean_ctor_set(v_reuseFailAlloc_2114_, 7, v_messages_2104_);
lean_ctor_set(v_reuseFailAlloc_2114_, 8, v_infoState_2105_);
lean_ctor_set(v_reuseFailAlloc_2114_, 9, v_snapshotTasks_2106_);
v___x_2111_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = lean_st_ref_put(v___y_2083_, v___x_2111_);
v___x_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2113_, 0, v_r_2092_);
return v___x_2113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg___boxed(lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_2119_);
lean_dec(v___y_2119_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v___x_2133_; lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
v___x_2133_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_2131_);
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2___boxed(lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec(v___y_2142_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(lean_object* v___x_2159_, lean_object* v_a_2160_, uint8_t v___x_2161_, uint8_t v___x_2162_, uint8_t v___x_2163_, lean_object* v_a_2164_, lean_object* v___x_2165_, lean_object* v_expr_2166_, lean_object* v___x_2167_, lean_object* v_val_2168_, lean_object* v_mvarId_2169_, lean_object* v___x_2170_, lean_object* v_a_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Lean_Meta_mkLambdaFVars(v___x_2159_, v_a_2160_, v___x_2161_, v___x_2162_, v___x_2161_, v___x_2162_, v___x_2163_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2184_);
lean_dec_ref_known(v___x_2183_, 1);
v___x_2185_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1));
v___x_2186_ = lean_box(0);
v___x_2187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2187_, 0, v_a_2164_);
lean_ctor_set(v___x_2187_, 1, v___x_2186_);
v___x_2188_ = l_Lean_mkConst(v___x_2185_, v___x_2187_);
v___x_2189_ = lean_unsigned_to_nat(5u);
v___x_2190_ = lean_mk_empty_array_with_capacity(v___x_2189_);
v___x_2191_ = lean_array_push(v___x_2190_, v___x_2165_);
v___x_2192_ = lean_array_push(v___x_2191_, v_expr_2166_);
v___x_2193_ = lean_array_push(v___x_2192_, v___x_2167_);
v___x_2194_ = lean_array_push(v___x_2193_, v_val_2168_);
v___x_2195_ = lean_array_push(v___x_2194_, v_a_2184_);
v___x_2196_ = l_Lean_mkAppN(v___x_2188_, v___x_2195_);
lean_dec_ref(v___x_2195_);
v___x_2197_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2169_, v___x_2196_, v___y_2179_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2215_; 
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2215_ == 0)
{
lean_object* v_unused_2216_; 
v_unused_2216_ = lean_ctor_get(v___x_2197_, 0);
lean_dec(v_unused_2216_);
v___x_2199_ = v___x_2197_;
v_isShared_2200_ = v_isSharedCheck_2215_;
goto v_resetjp_2198_;
}
else
{
lean_dec(v___x_2197_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2215_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2201_; lean_object* v_toGoalState_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2213_; 
v___x_2201_ = lean_st_ref_get(v___y_2172_);
v_toGoalState_2202_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2213_ == 0)
{
lean_object* v_unused_2214_; 
v_unused_2214_ = lean_ctor_get(v___x_2201_, 1);
lean_dec(v_unused_2214_);
v___x_2204_ = v___x_2201_;
v_isShared_2205_ = v_isSharedCheck_2213_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_toGoalState_2202_);
lean_dec(v___x_2201_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2213_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 1, v___x_2170_);
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_toGoalState_2202_);
lean_ctor_set(v_reuseFailAlloc_2212_, 1, v___x_2170_);
v___x_2207_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2208_, 0, v_a_2171_);
lean_ctor_set(v___x_2208_, 1, v___x_2207_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v___x_2208_);
v___x_2210_ = v___x_2199_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec(v_a_2171_);
lean_dec(v___x_2170_);
v_a_2217_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2197_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2197_);
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
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec(v_a_2171_);
lean_dec(v___x_2170_);
lean_dec(v_mvarId_2169_);
lean_dec_ref(v_val_2168_);
lean_dec_ref(v___x_2167_);
lean_dec_ref(v_expr_2166_);
lean_dec_ref(v___x_2165_);
lean_dec(v_a_2164_);
v_a_2225_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2183_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2183_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed(lean_object** _args){
lean_object* v___x_2233_ = _args[0];
lean_object* v_a_2234_ = _args[1];
lean_object* v___x_2235_ = _args[2];
lean_object* v___x_2236_ = _args[3];
lean_object* v___x_2237_ = _args[4];
lean_object* v_a_2238_ = _args[5];
lean_object* v___x_2239_ = _args[6];
lean_object* v_expr_2240_ = _args[7];
lean_object* v___x_2241_ = _args[8];
lean_object* v_val_2242_ = _args[9];
lean_object* v_mvarId_2243_ = _args[10];
lean_object* v___x_2244_ = _args[11];
lean_object* v_a_2245_ = _args[12];
lean_object* v___y_2246_ = _args[13];
lean_object* v___y_2247_ = _args[14];
lean_object* v___y_2248_ = _args[15];
lean_object* v___y_2249_ = _args[16];
lean_object* v___y_2250_ = _args[17];
lean_object* v___y_2251_ = _args[18];
lean_object* v___y_2252_ = _args[19];
lean_object* v___y_2253_ = _args[20];
lean_object* v___y_2254_ = _args[21];
lean_object* v___y_2255_ = _args[22];
lean_object* v___y_2256_ = _args[23];
_start:
{
uint8_t v___x_160385__boxed_2257_; uint8_t v___x_160386__boxed_2258_; uint8_t v___x_160387__boxed_2259_; lean_object* v_res_2260_; 
v___x_160385__boxed_2257_ = lean_unbox(v___x_2235_);
v___x_160386__boxed_2258_ = lean_unbox(v___x_2236_);
v___x_160387__boxed_2259_ = lean_unbox(v___x_2237_);
v_res_2260_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(v___x_2233_, v_a_2234_, v___x_160385__boxed_2257_, v___x_160386__boxed_2258_, v___x_160387__boxed_2259_, v_a_2238_, v___x_2239_, v_expr_2240_, v___x_2241_, v_val_2242_, v_mvarId_2243_, v___x_2244_, v_a_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v___x_2233_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(lean_object* v___x_2266_, lean_object* v_a_2267_, uint8_t v___x_2268_, uint8_t v___x_2269_, uint8_t v___x_2270_, lean_object* v_a_2271_, lean_object* v___x_2272_, lean_object* v___x_2273_, lean_object* v_expr_2274_, lean_object* v___x_2275_, lean_object* v_val_2276_, lean_object* v_mvarId_2277_, lean_object* v___x_2278_, lean_object* v_a_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = l_Lean_Meta_mkLambdaFVars(v___x_2266_, v_a_2267_, v___x_2268_, v___x_2269_, v___x_2268_, v___x_2269_, v___x_2270_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v_a_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_a_2292_);
lean_dec_ref_known(v___x_2291_, 1);
v___x_2293_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1));
v___x_2294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2294_, 0, v_a_2271_);
lean_ctor_set(v___x_2294_, 1, v___x_2272_);
v___x_2295_ = l_Lean_mkConst(v___x_2293_, v___x_2294_);
v___x_2296_ = lean_unsigned_to_nat(5u);
v___x_2297_ = lean_mk_empty_array_with_capacity(v___x_2296_);
v___x_2298_ = lean_array_push(v___x_2297_, v___x_2273_);
v___x_2299_ = lean_array_push(v___x_2298_, v_expr_2274_);
v___x_2300_ = lean_array_push(v___x_2299_, v___x_2275_);
v___x_2301_ = lean_array_push(v___x_2300_, v_val_2276_);
v___x_2302_ = lean_array_push(v___x_2301_, v_a_2292_);
v___x_2303_ = l_Lean_mkAppN(v___x_2295_, v___x_2302_);
lean_dec_ref(v___x_2302_);
v___x_2304_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2277_, v___x_2303_, v___y_2287_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2322_; 
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2322_ == 0)
{
lean_object* v_unused_2323_; 
v_unused_2323_ = lean_ctor_get(v___x_2304_, 0);
lean_dec(v_unused_2323_);
v___x_2306_ = v___x_2304_;
v_isShared_2307_ = v_isSharedCheck_2322_;
goto v_resetjp_2305_;
}
else
{
lean_dec(v___x_2304_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2322_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2308_; lean_object* v_toGoalState_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2320_; 
v___x_2308_ = lean_st_ref_get(v___y_2280_);
v_toGoalState_2309_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2320_ == 0)
{
lean_object* v_unused_2321_; 
v_unused_2321_ = lean_ctor_get(v___x_2308_, 1);
lean_dec(v_unused_2321_);
v___x_2311_ = v___x_2308_;
v_isShared_2312_ = v_isSharedCheck_2320_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_toGoalState_2309_);
lean_dec(v___x_2308_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2320_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 1, v___x_2278_);
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_toGoalState_2309_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v___x_2278_);
v___x_2314_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
lean_object* v___x_2315_; lean_object* v___x_2317_; 
v___x_2315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2315_, 0, v_a_2279_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 0, v___x_2315_);
v___x_2317_ = v___x_2306_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2315_);
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
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec(v_a_2279_);
lean_dec(v___x_2278_);
v_a_2324_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2304_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2304_);
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
lean_dec(v_a_2279_);
lean_dec(v___x_2278_);
lean_dec(v_mvarId_2277_);
lean_dec_ref(v_val_2276_);
lean_dec_ref(v___x_2275_);
lean_dec_ref(v_expr_2274_);
lean_dec_ref(v___x_2273_);
lean_dec(v___x_2272_);
lean_dec(v_a_2271_);
v_a_2332_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2291_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2291_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed(lean_object** _args){
lean_object* v___x_2340_ = _args[0];
lean_object* v_a_2341_ = _args[1];
lean_object* v___x_2342_ = _args[2];
lean_object* v___x_2343_ = _args[3];
lean_object* v___x_2344_ = _args[4];
lean_object* v_a_2345_ = _args[5];
lean_object* v___x_2346_ = _args[6];
lean_object* v___x_2347_ = _args[7];
lean_object* v_expr_2348_ = _args[8];
lean_object* v___x_2349_ = _args[9];
lean_object* v_val_2350_ = _args[10];
lean_object* v_mvarId_2351_ = _args[11];
lean_object* v___x_2352_ = _args[12];
lean_object* v_a_2353_ = _args[13];
lean_object* v___y_2354_ = _args[14];
lean_object* v___y_2355_ = _args[15];
lean_object* v___y_2356_ = _args[16];
lean_object* v___y_2357_ = _args[17];
lean_object* v___y_2358_ = _args[18];
lean_object* v___y_2359_ = _args[19];
lean_object* v___y_2360_ = _args[20];
lean_object* v___y_2361_ = _args[21];
lean_object* v___y_2362_ = _args[22];
lean_object* v___y_2363_ = _args[23];
lean_object* v___y_2364_ = _args[24];
_start:
{
uint8_t v___x_160567__boxed_2365_; uint8_t v___x_160568__boxed_2366_; uint8_t v___x_160569__boxed_2367_; lean_object* v_res_2368_; 
v___x_160567__boxed_2365_ = lean_unbox(v___x_2342_);
v___x_160568__boxed_2366_ = lean_unbox(v___x_2343_);
v___x_160569__boxed_2367_ = lean_unbox(v___x_2344_);
v_res_2368_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(v___x_2340_, v_a_2341_, v___x_160567__boxed_2365_, v___x_160568__boxed_2366_, v___x_160569__boxed_2367_, v_a_2345_, v___x_2346_, v___x_2347_, v_expr_2348_, v___x_2349_, v_val_2350_, v_mvarId_2351_, v___x_2352_, v_a_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___x_2340_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(lean_object* v___x_2369_, lean_object* v_a_2370_, uint8_t v___x_2371_, uint8_t v___x_2372_, uint8_t v___x_2373_, lean_object* v_mvarId_2374_, lean_object* v___x_2375_, lean_object* v_a_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Lean_Meta_mkLambdaFVars(v___x_2369_, v_a_2370_, v___x_2371_, v___x_2372_, v___x_2371_, v___x_2372_, v___x_2373_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v___x_2390_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2389_);
lean_dec_ref_known(v___x_2388_, 1);
v___x_2390_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2374_, v_a_2389_, v___y_2384_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2408_; 
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2408_ == 0)
{
lean_object* v_unused_2409_; 
v_unused_2409_ = lean_ctor_get(v___x_2390_, 0);
lean_dec(v_unused_2409_);
v___x_2392_ = v___x_2390_;
v_isShared_2393_ = v_isSharedCheck_2408_;
goto v_resetjp_2391_;
}
else
{
lean_dec(v___x_2390_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2408_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2394_; lean_object* v_toGoalState_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2406_; 
v___x_2394_ = lean_st_ref_get(v___y_2377_);
v_toGoalState_2395_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2406_ == 0)
{
lean_object* v_unused_2407_; 
v_unused_2407_ = lean_ctor_get(v___x_2394_, 1);
lean_dec(v_unused_2407_);
v___x_2397_ = v___x_2394_;
v_isShared_2398_ = v_isSharedCheck_2406_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_toGoalState_2395_);
lean_dec(v___x_2394_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2406_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 1, v___x_2375_);
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_toGoalState_2395_);
lean_ctor_set(v_reuseFailAlloc_2405_, 1, v___x_2375_);
v___x_2400_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
lean_object* v___x_2401_; lean_object* v___x_2403_; 
v___x_2401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2401_, 0, v_a_2376_);
lean_ctor_set(v___x_2401_, 1, v___x_2400_);
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 0, v___x_2401_);
v___x_2403_ = v___x_2392_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2401_);
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
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
lean_dec(v_a_2376_);
lean_dec(v___x_2375_);
v_a_2410_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2390_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2390_);
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
lean_dec(v_a_2376_);
lean_dec(v___x_2375_);
lean_dec(v_mvarId_2374_);
v_a_2418_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2420_ = v___x_2388_;
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2388_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed(lean_object** _args){
lean_object* v___x_2426_ = _args[0];
lean_object* v_a_2427_ = _args[1];
lean_object* v___x_2428_ = _args[2];
lean_object* v___x_2429_ = _args[3];
lean_object* v___x_2430_ = _args[4];
lean_object* v_mvarId_2431_ = _args[5];
lean_object* v___x_2432_ = _args[6];
lean_object* v_a_2433_ = _args[7];
lean_object* v___y_2434_ = _args[8];
lean_object* v___y_2435_ = _args[9];
lean_object* v___y_2436_ = _args[10];
lean_object* v___y_2437_ = _args[11];
lean_object* v___y_2438_ = _args[12];
lean_object* v___y_2439_ = _args[13];
lean_object* v___y_2440_ = _args[14];
lean_object* v___y_2441_ = _args[15];
lean_object* v___y_2442_ = _args[16];
lean_object* v___y_2443_ = _args[17];
lean_object* v___y_2444_ = _args[18];
_start:
{
uint8_t v___x_160738__boxed_2445_; uint8_t v___x_160739__boxed_2446_; uint8_t v___x_160740__boxed_2447_; lean_object* v_res_2448_; 
v___x_160738__boxed_2445_ = lean_unbox(v___x_2428_);
v___x_160739__boxed_2446_ = lean_unbox(v___x_2429_);
v___x_160740__boxed_2447_ = lean_unbox(v___x_2430_);
v_res_2448_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(v___x_2426_, v_a_2427_, v___x_160738__boxed_2445_, v___x_160739__boxed_2446_, v___x_160740__boxed_2447_, v_mvarId_2431_, v___x_2432_, v_a_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___x_2426_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(lean_object* v_mvarId_2451_, lean_object* v___x_2452_, lean_object* v_generation_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
lean_object* v___x_2465_; 
lean_inc(v_mvarId_2451_);
v___x_2465_ = l_Lean_MVarId_getTag(v_mvarId_2451_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; lean_object* v___x_2467_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_a_2466_);
lean_dec_ref_known(v___x_2465_, 1);
v___x_2467_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2452_, v_a_2466_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; lean_object* v___x_2469_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc_n(v_a_2468_, 2);
lean_dec_ref_known(v___x_2467_, 1);
v___x_2469_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2451_, v_a_2468_, v___y_2461_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v___x_2470_; lean_object* v_toGoalState_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2480_; 
lean_dec_ref_known(v___x_2469_, 1);
v___x_2470_ = lean_st_ref_get(v___y_2454_);
v_toGoalState_2471_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2480_ == 0)
{
lean_object* v_unused_2481_; 
v_unused_2481_ = lean_ctor_get(v___x_2470_, 1);
lean_dec(v_unused_2481_);
v___x_2473_ = v___x_2470_;
v_isShared_2474_ = v_isSharedCheck_2480_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_toGoalState_2471_);
lean_dec(v___x_2470_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2480_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2475_; lean_object* v___x_2477_; 
v___x_2475_ = l_Lean_Expr_mvarId_x21(v_a_2468_);
lean_dec(v_a_2468_);
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 1, v___x_2475_);
v___x_2477_ = v___x_2473_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_toGoalState_2471_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v___x_2475_);
v___x_2477_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
lean_object* v___x_2478_; 
v___x_2478_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v___x_2477_, v_generation_2453_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
return v___x_2478_;
}
}
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
lean_dec(v_a_2468_);
lean_dec(v_generation_2453_);
v_a_2482_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2469_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2469_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
else
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
lean_dec(v_generation_2453_);
lean_dec(v_mvarId_2451_);
v_a_2490_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2492_ = v___x_2467_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2467_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2490_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
else
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
lean_dec(v_generation_2453_);
lean_dec_ref(v___x_2452_);
lean_dec(v_mvarId_2451_);
v_a_2498_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v___x_2465_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2465_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed(lean_object* v_mvarId_2506_, lean_object* v___x_2507_, lean_object* v_generation_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(v_mvarId_2506_, v___x_2507_, v_generation_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec(v___y_2509_);
return v_res_2520_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3(void){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = lean_box(0);
v___x_2526_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__2));
v___x_2527_ = l_Lean_mkConst(v___x_2526_, v___x_2525_);
return v___x_2527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(lean_object* v_goal_2528_, lean_object* v_generation_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v___x_2540_; lean_object* v_a_2542_; lean_object* v___y_2547_; lean_object* v___x_2557_; lean_object* v_mvarId_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2835_; 
lean_inc_ref(v_goal_2528_);
v___x_2540_ = lean_st_mk_ref(v_goal_2528_);
v___x_2557_ = lean_st_ref_get(v___x_2540_);
v_mvarId_2558_ = lean_ctor_get(v___x_2557_, 1);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2835_ == 0)
{
lean_object* v_unused_2836_; 
v_unused_2836_ = lean_ctor_get(v___x_2557_, 0);
lean_dec(v_unused_2836_);
v___x_2560_ = v___x_2557_;
v_isShared_2561_ = v_isSharedCheck_2835_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_mvarId_2558_);
lean_dec(v___x_2557_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2835_;
goto v_resetjp_2559_;
}
v___jp_2541_:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2543_ = lean_st_ref_get(v___x_2540_);
lean_dec(v___x_2540_);
v___x_2544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2544_, 0, v_a_2542_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
v___x_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2544_);
return v___x_2545_;
}
v___jp_2546_:
{
if (lean_obj_tag(v___y_2547_) == 0)
{
lean_object* v_a_2548_; 
v_a_2548_ = lean_ctor_get(v___y_2547_, 0);
lean_inc(v_a_2548_);
lean_dec_ref_known(v___y_2547_, 1);
v_a_2542_ = v_a_2548_;
goto v___jp_2541_;
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_dec(v___x_2540_);
v_a_2549_ = lean_ctor_get(v___y_2547_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___y_2547_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___y_2547_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___y_2547_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
v_resetjp_2559_:
{
lean_object* v___x_2562_; 
v___x_2562_ = l_Lean_MVarId_getType(v_mvarId_2558_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; uint8_t v___x_2564_; uint8_t v___x_2565_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2562_, 1);
v___x_2564_ = l_Lean_Expr_isForall(v_a_2563_);
v___x_2565_ = 1;
if (v___x_2564_ == 0)
{
uint8_t v___x_2566_; 
lean_del_object(v___x_2560_);
v___x_2566_ = l_Lean_Expr_isLet(v_a_2563_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2567_; 
lean_dec(v_a_2563_);
lean_dec_ref(v___y_2535_);
lean_dec(v_generation_2529_);
v___x_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2567_, 0, v_goal_2528_);
v_a_2542_ = v___x_2567_;
goto v___jp_2541_;
}
else
{
lean_object* v___x_2568_; 
lean_dec_ref(v_goal_2528_);
v___x_2568_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_2531_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; uint8_t v_zetaDelta_2570_; 
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_a_2569_);
lean_dec_ref_known(v___x_2568_, 1);
v_zetaDelta_2570_ = lean_ctor_get_uint8(v_a_2569_, sizeof(void*)*18 + 19);
lean_dec(v_a_2569_);
if (v_zetaDelta_2570_ == 0)
{
lean_object* v___x_2571_; 
lean_dec(v_a_2563_);
v___x_2571_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_2540_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v___f_2573_; lean_object* v___x_2574_; lean_object* v_mvarId_2575_; lean_object* v___x_2576_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_a_2572_);
lean_dec_ref_known(v___x_2571_, 1);
v___f_2573_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed), 13, 2);
lean_closure_set(v___f_2573_, 0, v_a_2572_);
lean_closure_set(v___f_2573_, 1, v_generation_2529_);
v___x_2574_ = lean_st_ref_get(v___x_2540_);
v_mvarId_2575_ = lean_ctor_get(v___x_2574_, 1);
lean_inc(v_mvarId_2575_);
lean_dec(v___x_2574_);
v___x_2576_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_2575_, v___f_2573_, v___x_2540_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec_ref(v___y_2535_);
v___y_2547_ = v___x_2576_;
goto v___jp_2546_;
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
lean_dec(v___x_2540_);
lean_dec_ref(v___y_2535_);
lean_dec(v_generation_2529_);
v_a_2577_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2571_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2571_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
else
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v_mvarId_2588_; lean_object* v___f_2589_; lean_object* v___x_2590_; 
v___x_2585_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__0));
v___x_2586_ = l_Lean_Meta_expandLet(v_a_2563_, v___x_2585_, v___x_2565_);
lean_dec(v_a_2563_);
v___x_2587_ = lean_st_ref_get(v___x_2540_);
v_mvarId_2588_ = lean_ctor_get(v___x_2587_, 1);
lean_inc_n(v_mvarId_2588_, 2);
lean_dec(v___x_2587_);
v___f_2589_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed), 14, 3);
lean_closure_set(v___f_2589_, 0, v_mvarId_2588_);
lean_closure_set(v___f_2589_, 1, v___x_2586_);
lean_closure_set(v___f_2589_, 2, v_generation_2529_);
v___x_2590_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_2588_, v___f_2589_, v___x_2540_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec_ref(v___y_2535_);
v___y_2547_ = v___x_2590_;
goto v___jp_2546_;
}
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_dec(v_a_2563_);
lean_dec(v___x_2540_);
lean_dec_ref(v___y_2535_);
lean_dec(v_generation_2529_);
v_a_2591_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2568_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2568_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
}
else
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
lean_dec(v_generation_2529_);
lean_dec_ref(v_goal_2528_);
v___x_2599_ = l_Lean_Expr_bindingDomain_x21(v_a_2563_);
lean_inc_ref(v___x_2599_);
v___x_2600_ = l_Lean_Meta_isProp(v___x_2599_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; uint8_t v___x_2602_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
lean_dec_ref_known(v___x_2600_, 1);
v___x_2602_ = lean_unbox(v_a_2601_);
lean_dec(v_a_2601_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2603_; 
lean_dec_ref(v___x_2599_);
lean_dec(v_a_2563_);
v___x_2603_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_2540_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec_ref(v___y_2535_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v___x_2605_; lean_object* v___x_2607_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2604_);
lean_dec_ref_known(v___x_2603_, 1);
v___x_2605_ = lean_st_ref_get(v___x_2540_);
if (v_isShared_2561_ == 0)
{
lean_ctor_set_tag(v___x_2560_, 3);
lean_ctor_set(v___x_2560_, 1, v___x_2605_);
lean_ctor_set(v___x_2560_, 0, v_a_2604_);
v___x_2607_ = v___x_2560_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2604_);
lean_ctor_set(v_reuseFailAlloc_2608_, 1, v___x_2605_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
v_a_2542_ = v___x_2607_;
goto v___jp_2541_;
}
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_del_object(v___x_2560_);
lean_dec(v___x_2540_);
v_a_2609_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2603_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2603_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
else
{
uint8_t v___x_2617_; lean_object* v___x_2618_; lean_object* v_mvarId_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2817_; 
lean_del_object(v___x_2560_);
v___x_2617_ = 0;
v___x_2618_ = lean_st_ref_get(v___x_2540_);
v_mvarId_2619_ = lean_ctor_get(v___x_2618_, 1);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2817_ == 0)
{
lean_object* v_unused_2818_; 
v_unused_2818_ = lean_ctor_get(v___x_2618_, 0);
lean_dec(v_unused_2818_);
v___x_2621_ = v___x_2618_;
v_isShared_2622_ = v_isSharedCheck_2817_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_mvarId_2619_);
lean_dec(v___x_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2817_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2623_; 
lean_inc(v_mvarId_2619_);
v___x_2623_ = l_Lean_MVarId_getTag(v_mvarId_2619_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_a_2624_);
lean_dec_ref_known(v___x_2623_, 1);
v___x_2625_ = l_Lean_Expr_bindingBody_x21(v_a_2563_);
v___x_2626_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___x_2540_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v___x_2628_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc_n(v_a_2627_, 2);
lean_dec_ref_known(v___x_2626_, 1);
v___x_2628_ = l_Lean_Meta_Grind_registerFVarAnchor___redArg(v_a_2627_, v___x_2540_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
lean_dec_ref_known(v___x_2628_, 1);
lean_inc(v_a_2627_);
v___x_2629_ = l_Lean_mkFVar(v_a_2627_);
lean_inc_ref(v___x_2599_);
v___x_2630_ = l_Lean_Meta_Grind_preprocessHypothesis(v___x_2599_, v___x_2540_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; lean_object* v_lctx_2632_; lean_object* v_localInstances_2633_; lean_object* v_expr_2634_; lean_object* v_proof_x3f_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2631_);
lean_dec_ref_known(v___x_2630_, 1);
v_lctx_2632_ = lean_ctor_get(v___y_2535_, 2);
v_localInstances_2633_ = lean_ctor_get(v___y_2535_, 3);
v_expr_2634_ = lean_ctor_get(v_a_2631_, 0);
lean_inc_ref_n(v_expr_2634_, 2);
v_proof_x3f_2635_ = lean_ctor_get(v_a_2631_, 1);
lean_inc(v_proof_x3f_2635_);
lean_dec(v_a_2631_);
v___x_2636_ = l_Lean_Expr_bindingName_x21(v_a_2563_);
lean_inc(v___x_2636_);
v___x_2637_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v___x_2636_, v_expr_2634_, v___x_2540_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; uint8_t v___x_2639_; uint8_t v___x_2640_; lean_object* v___x_2641_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v_localInsts_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___x_2762_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2638_);
lean_dec_ref_known(v___x_2637_, 1);
v___x_2639_ = l_Lean_Expr_bindingInfo_x21(v_a_2563_);
v___x_2640_ = 0;
lean_inc_ref_n(v_expr_2634_, 2);
lean_inc(v_a_2627_);
lean_inc_ref(v_lctx_2632_);
v___x_2641_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_2632_, v_a_2627_, v_a_2638_, v_expr_2634_, v___x_2639_, v___x_2640_);
v___x_2762_ = l_Lean_Meta_isClass_x3f(v_expr_2634_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2763_);
lean_dec_ref_known(v___x_2762_, 1);
if (lean_obj_tag(v_a_2763_) == 1)
{
lean_object* v_val_2764_; lean_object* v___x_2766_; 
v_val_2764_ = lean_ctor_get(v_a_2763_, 0);
lean_inc(v_val_2764_);
lean_dec_ref_known(v_a_2763_, 1);
lean_inc_ref(v___x_2629_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 1, v___x_2629_);
lean_ctor_set(v___x_2621_, 0, v_val_2764_);
v___x_2766_ = v___x_2621_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_val_2764_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v___x_2629_);
v___x_2766_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
lean_object* v___x_2767_; 
lean_inc_ref(v_localInstances_2633_);
v___x_2767_ = lean_array_push(v_localInstances_2633_, v___x_2766_);
lean_inc(v___x_2540_);
v_localInsts_2678_ = v___x_2767_;
v___y_2679_ = v___x_2540_;
v___y_2680_ = v___y_2530_;
v___y_2681_ = v___y_2531_;
v___y_2682_ = v___y_2532_;
v___y_2683_ = v___y_2533_;
v___y_2684_ = v___y_2534_;
v___y_2685_ = v___y_2535_;
v___y_2686_ = v___y_2536_;
v___y_2687_ = v___y_2537_;
v___y_2688_ = v___y_2538_;
goto v___jp_2677_;
}
}
else
{
lean_inc_ref(v_localInstances_2633_);
lean_dec(v_a_2763_);
lean_del_object(v___x_2621_);
lean_inc(v___x_2540_);
v_localInsts_2678_ = v_localInstances_2633_;
v___y_2679_ = v___x_2540_;
v___y_2680_ = v___y_2530_;
v___y_2681_ = v___y_2531_;
v___y_2682_ = v___y_2532_;
v___y_2683_ = v___y_2533_;
v___y_2684_ = v___y_2534_;
v___y_2685_ = v___y_2535_;
v___y_2686_ = v___y_2536_;
v___y_2687_ = v___y_2537_;
v___y_2688_ = v___y_2538_;
goto v___jp_2677_;
}
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_dec_ref(v___x_2641_);
lean_dec(v___x_2636_);
lean_dec(v_proof_x3f_2635_);
lean_dec_ref(v_expr_2634_);
lean_dec_ref(v___x_2629_);
lean_dec(v_a_2627_);
lean_dec_ref(v___x_2625_);
lean_dec(v_a_2624_);
lean_del_object(v___x_2621_);
lean_dec(v_mvarId_2619_);
lean_dec_ref(v___x_2599_);
lean_dec(v_a_2563_);
lean_dec(v___x_2540_);
lean_dec_ref(v___y_2535_);
v_a_2769_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2762_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2762_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
v___jp_2642_:
{
uint8_t v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2655_ = 2;
v___x_2656_ = lean_unsigned_to_nat(0u);
v___x_2657_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_2641_, v___y_2649_, v___y_2654_, v___x_2655_, v_a_2624_, v___x_2656_, v___y_2647_, v___y_2653_, v___y_2644_, v___y_2651_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; uint8_t v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___f_2667_; lean_object* v___x_2668_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
lean_dec_ref_known(v___x_2657_, 1);
v___x_2659_ = l_Lean_Expr_mvarId_x21(v_a_2658_);
v___x_2660_ = lean_unsigned_to_nat(1u);
v___x_2661_ = lean_mk_empty_array_with_capacity(v___x_2660_);
v___x_2662_ = lean_array_push(v___x_2661_, v___x_2629_);
v___x_2663_ = 1;
v___x_2664_ = lean_box(v___x_2617_);
v___x_2665_ = lean_box(v___x_2565_);
v___x_2666_ = lean_box(v___x_2663_);
lean_inc(v___x_2659_);
v___f_2667_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed), 19, 8);
lean_closure_set(v___f_2667_, 0, v___x_2662_);
lean_closure_set(v___f_2667_, 1, v_a_2658_);
lean_closure_set(v___f_2667_, 2, v___x_2664_);
lean_closure_set(v___f_2667_, 3, v___x_2665_);
lean_closure_set(v___f_2667_, 4, v___x_2666_);
lean_closure_set(v___f_2667_, 5, v_mvarId_2619_);
lean_closure_set(v___f_2667_, 6, v___x_2659_);
lean_closure_set(v___f_2667_, 7, v_a_2627_);
v___x_2668_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2659_, v___f_2667_, v___y_2648_, v___y_2643_, v___y_2646_, v___y_2650_, v___y_2645_, v___y_2652_, v___y_2647_, v___y_2653_, v___y_2644_, v___y_2651_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2648_);
v___y_2547_ = v___x_2668_;
goto v___jp_2546_;
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec_ref(v___x_2629_);
lean_dec(v_a_2627_);
lean_dec(v_mvarId_2619_);
lean_dec(v___x_2540_);
v_a_2669_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2671_ = v___x_2657_;
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2657_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2669_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
v___jp_2677_:
{
if (lean_obj_tag(v_proof_x3f_2635_) == 0)
{
uint8_t v___x_2689_; 
lean_dec(v___x_2636_);
lean_dec_ref(v_expr_2634_);
lean_dec_ref(v___x_2599_);
v___x_2689_ = l_Lean_Expr_isArrow(v_a_2563_);
lean_dec(v_a_2563_);
if (v___x_2689_ == 0)
{
lean_object* v___x_2690_; 
v___x_2690_ = lean_expr_instantiate1(v___x_2625_, v___x_2629_);
lean_dec_ref(v___x_2625_);
v___y_2643_ = v___y_2680_;
v___y_2644_ = v___y_2687_;
v___y_2645_ = v___y_2683_;
v___y_2646_ = v___y_2681_;
v___y_2647_ = v___y_2685_;
v___y_2648_ = v___y_2679_;
v___y_2649_ = v_localInsts_2678_;
v___y_2650_ = v___y_2682_;
v___y_2651_ = v___y_2688_;
v___y_2652_ = v___y_2684_;
v___y_2653_ = v___y_2686_;
v___y_2654_ = v___x_2690_;
goto v___jp_2642_;
}
else
{
v___y_2643_ = v___y_2680_;
v___y_2644_ = v___y_2687_;
v___y_2645_ = v___y_2683_;
v___y_2646_ = v___y_2681_;
v___y_2647_ = v___y_2685_;
v___y_2648_ = v___y_2679_;
v___y_2649_ = v_localInsts_2678_;
v___y_2650_ = v___y_2682_;
v___y_2651_ = v___y_2688_;
v___y_2652_ = v___y_2684_;
v___y_2653_ = v___y_2686_;
v___y_2654_ = v___x_2625_;
goto v___jp_2642_;
}
}
else
{
lean_object* v_val_2691_; uint8_t v___x_2692_; 
v_val_2691_ = lean_ctor_get(v_proof_x3f_2635_, 0);
lean_inc(v_val_2691_);
lean_dec_ref_known(v_proof_x3f_2635_, 1);
v___x_2692_ = l_Lean_Expr_isArrow(v_a_2563_);
lean_dec(v_a_2563_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
lean_inc_ref(v___x_2625_);
lean_inc_ref_n(v___x_2599_, 2);
v___x_2693_ = l_Lean_mkLambda(v___x_2636_, v___x_2639_, v___x_2599_, v___x_2625_);
v___x_2694_ = lean_box(0);
v___x_2695_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3);
lean_inc_ref(v___x_2629_);
lean_inc(v_val_2691_);
lean_inc_ref(v_expr_2634_);
v___x_2696_ = l_Lean_mkApp4(v___x_2695_, v___x_2599_, v_expr_2634_, v_val_2691_, v___x_2629_);
v___x_2697_ = lean_expr_instantiate1(v___x_2625_, v___x_2696_);
lean_dec_ref(v___x_2696_);
lean_dec_ref(v___x_2625_);
lean_inc_ref(v___x_2697_);
v___x_2698_ = l_Lean_Meta_getLevel(v___x_2697_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; uint8_t v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
lean_dec_ref_known(v___x_2698_, 1);
v___x_2700_ = 2;
v___x_2701_ = lean_unsigned_to_nat(0u);
v___x_2702_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_2641_, v_localInsts_2678_, v___x_2697_, v___x_2700_, v_a_2624_, v___x_2701_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; uint8_t v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___f_2712_; lean_object* v___x_2713_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_a_2703_);
lean_dec_ref_known(v___x_2702_, 1);
v___x_2704_ = l_Lean_Expr_mvarId_x21(v_a_2703_);
v___x_2705_ = lean_unsigned_to_nat(1u);
v___x_2706_ = lean_mk_empty_array_with_capacity(v___x_2705_);
v___x_2707_ = lean_array_push(v___x_2706_, v___x_2629_);
v___x_2708_ = 1;
v___x_2709_ = lean_box(v___x_2692_);
v___x_2710_ = lean_box(v___x_2565_);
v___x_2711_ = lean_box(v___x_2708_);
lean_inc(v___x_2704_);
v___f_2712_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed), 25, 14);
lean_closure_set(v___f_2712_, 0, v___x_2707_);
lean_closure_set(v___f_2712_, 1, v_a_2703_);
lean_closure_set(v___f_2712_, 2, v___x_2709_);
lean_closure_set(v___f_2712_, 3, v___x_2710_);
lean_closure_set(v___f_2712_, 4, v___x_2711_);
lean_closure_set(v___f_2712_, 5, v_a_2699_);
lean_closure_set(v___f_2712_, 6, v___x_2694_);
lean_closure_set(v___f_2712_, 7, v___x_2599_);
lean_closure_set(v___f_2712_, 8, v_expr_2634_);
lean_closure_set(v___f_2712_, 9, v___x_2693_);
lean_closure_set(v___f_2712_, 10, v_val_2691_);
lean_closure_set(v___f_2712_, 11, v_mvarId_2619_);
lean_closure_set(v___f_2712_, 12, v___x_2704_);
lean_closure_set(v___f_2712_, 13, v_a_2627_);
v___x_2713_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2704_, v___f_2712_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2679_);
v___y_2547_ = v___x_2713_;
goto v___jp_2546_;
}
else
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2721_; 
lean_dec(v_a_2699_);
lean_dec_ref(v___x_2693_);
lean_dec(v_val_2691_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2679_);
lean_dec_ref(v_expr_2634_);
lean_dec_ref(v___x_2629_);
lean_dec(v_a_2627_);
lean_dec(v_mvarId_2619_);
lean_dec_ref(v___x_2599_);
lean_dec(v___x_2540_);
v_a_2714_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2716_ = v___x_2702_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2702_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2719_; 
if (v_isShared_2717_ == 0)
{
v___x_2719_ = v___x_2716_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2714_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_dec_ref(v___x_2697_);
lean_dec_ref(v___x_2693_);
lean_dec(v_val_2691_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2679_);
lean_dec_ref(v_localInsts_2678_);
lean_dec_ref(v___x_2641_);
lean_dec_ref(v_expr_2634_);
lean_dec_ref(v___x_2629_);
lean_dec(v_a_2627_);
lean_dec(v_a_2624_);
lean_dec(v_mvarId_2619_);
lean_dec_ref(v___x_2599_);
lean_dec(v___x_2540_);
v_a_2722_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2698_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2698_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
else
{
lean_object* v___x_2730_; 
lean_dec(v___x_2636_);
lean_inc_ref(v___x_2625_);
v___x_2730_ = l_Lean_Meta_getLevel(v___x_2625_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; uint8_t v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref_known(v___x_2730_, 1);
v___x_2732_ = 2;
v___x_2733_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___x_2625_);
v___x_2734_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_2641_, v_localInsts_2678_, v___x_2625_, v___x_2732_, v_a_2624_, v___x_2733_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; uint8_t v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___f_2744_; lean_object* v___x_2745_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
lean_dec_ref_known(v___x_2734_, 1);
v___x_2736_ = l_Lean_Expr_mvarId_x21(v_a_2735_);
v___x_2737_ = lean_unsigned_to_nat(1u);
v___x_2738_ = lean_mk_empty_array_with_capacity(v___x_2737_);
v___x_2739_ = lean_array_push(v___x_2738_, v___x_2629_);
v___x_2740_ = 1;
v___x_2741_ = lean_box(v___x_2617_);
v___x_2742_ = lean_box(v___x_2565_);
v___x_2743_ = lean_box(v___x_2740_);
lean_inc(v___x_2736_);
v___f_2744_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed), 24, 13);
lean_closure_set(v___f_2744_, 0, v___x_2739_);
lean_closure_set(v___f_2744_, 1, v_a_2735_);
lean_closure_set(v___f_2744_, 2, v___x_2741_);
lean_closure_set(v___f_2744_, 3, v___x_2742_);
lean_closure_set(v___f_2744_, 4, v___x_2743_);
lean_closure_set(v___f_2744_, 5, v_a_2731_);
lean_closure_set(v___f_2744_, 6, v___x_2599_);
lean_closure_set(v___f_2744_, 7, v_expr_2634_);
lean_closure_set(v___f_2744_, 8, v___x_2625_);
lean_closure_set(v___f_2744_, 9, v_val_2691_);
lean_closure_set(v___f_2744_, 10, v_mvarId_2619_);
lean_closure_set(v___f_2744_, 11, v___x_2736_);
lean_closure_set(v___f_2744_, 12, v_a_2627_);
v___x_2745_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_2736_, v___f_2744_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2679_);
v___y_2547_ = v___x_2745_;
goto v___jp_2546_;
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_dec(v_a_2731_);
lean_dec(v_val_2691_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2679_);
lean_dec_ref(v_expr_2634_);
lean_dec_ref(v___x_2629_);
lean_dec(v_a_2627_);
lean_dec_ref(v___x_2625_);
lean_dec(v_mvarId_2619_);
lean_dec_ref(v___x_2599_);
lean_dec(v___x_2540_);
v_a_2746_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2734_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2734_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
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
else
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
lean_dec(v_val_2691_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2679_);
lean_dec_ref(v_localInsts_2678_);
lean_dec_ref(v___x_2641_);
lean_dec_ref(v_expr_2634_);
lean_dec_ref(v___x_2629_);
lean_dec(v_a_2627_);
lean_dec_ref(v___x_2625_);
lean_dec(v_a_2624_);
lean_dec(v_mvarId_2619_);
lean_dec_ref(v___x_2599_);
lean_dec(v___x_2540_);
v_a_2754_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2756_ = v___x_2730_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2730_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_dec(v___x_2636_);
lean_dec(v_proof_x3f_2635_);
lean_dec_ref(v_expr_2634_);
lean_dec_ref(v___x_2629_);
lean_dec(v_a_2627_);
lean_dec_ref(v___x_2625_);
lean_dec(v_a_2624_);
lean_del_object(v___x_2621_);
lean_dec(v_mvarId_2619_);
lean_dec_ref(v___x_2599_);
lean_dec(v_a_2563_);
lean_dec(v___x_2540_);
lean_dec_ref(v___y_2535_);
v_a_2777_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2637_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2637_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_dec_ref(v___x_2629_);
lean_dec(v_a_2627_);
lean_dec_ref(v___x_2625_);
lean_dec(v_a_2624_);
lean_del_object(v___x_2621_);
lean_dec(v_mvarId_2619_);
lean_dec_ref(v___x_2599_);
lean_dec(v_a_2563_);
lean_dec(v___x_2540_);
lean_dec_ref(v___y_2535_);
v_a_2785_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2630_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2630_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
else
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
lean_dec(v_a_2627_);
lean_dec_ref(v___x_2625_);
lean_dec(v_a_2624_);
lean_del_object(v___x_2621_);
lean_dec(v_mvarId_2619_);
lean_dec_ref(v___x_2599_);
lean_dec(v_a_2563_);
lean_dec(v___x_2540_);
lean_dec_ref(v___y_2535_);
v_a_2793_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2628_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2628_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec_ref(v___x_2625_);
lean_dec(v_a_2624_);
lean_del_object(v___x_2621_);
lean_dec(v_mvarId_2619_);
lean_dec_ref(v___x_2599_);
lean_dec(v_a_2563_);
lean_dec(v___x_2540_);
lean_dec_ref(v___y_2535_);
v_a_2801_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2626_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2626_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
lean_del_object(v___x_2621_);
lean_dec(v_mvarId_2619_);
lean_dec_ref(v___x_2599_);
lean_dec(v_a_2563_);
lean_dec(v___x_2540_);
lean_dec_ref(v___y_2535_);
v_a_2809_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2623_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2623_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec_ref(v___x_2599_);
lean_dec(v_a_2563_);
lean_del_object(v___x_2560_);
lean_dec(v___x_2540_);
lean_dec_ref(v___y_2535_);
v_a_2819_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2600_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2600_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
lean_del_object(v___x_2560_);
lean_dec(v___x_2540_);
lean_dec_ref(v___y_2535_);
lean_dec(v_generation_2529_);
lean_dec_ref(v_goal_2528_);
v_a_2827_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2562_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2562_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2827_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed(lean_object* v_goal_2837_, lean_object* v_generation_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(v_goal_2837_, v_generation_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(lean_object* v_goal_2850_, lean_object* v_generation_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v_mvarId_2862_; lean_object* v___f_2863_; lean_object* v___x_2864_; 
v_mvarId_2862_ = lean_ctor_get(v_goal_2850_, 1);
lean_inc(v_mvarId_2862_);
v___f_2863_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed), 12, 2);
lean_closure_set(v___f_2863_, 0, v_goal_2850_);
lean_closure_set(v___f_2863_, 1, v_generation_2851_);
v___x_2864_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_2862_, v___f_2863_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2873_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2867_ = v___x_2864_;
v_isShared_2868_ = v_isSharedCheck_2873_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2864_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2873_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v_fst_2869_; lean_object* v___x_2871_; 
v_fst_2869_ = lean_ctor_get(v_a_2865_, 0);
lean_inc(v_fst_2869_);
lean_dec(v_a_2865_);
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 0, v_fst_2869_);
v___x_2871_ = v___x_2867_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_fst_2869_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
v_a_2874_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2864_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2864_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___boxed(lean_object* v_goal_2882_, lean_object* v_generation_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_2882_, v_generation_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_);
lean_dec(v_a_2892_);
lean_dec_ref(v_a_2891_);
lean_dec(v_a_2890_);
lean_dec_ref(v_a_2889_);
lean_dec(v_a_2888_);
lean_dec_ref(v_a_2887_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
lean_dec(v_a_2884_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(lean_object* v_mvarId_2895_, lean_object* v_val_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_2895_, v_val_2896_, v___y_2904_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___boxed(lean_object* v_mvarId_2909_, lean_object* v_val_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v_res_2922_; 
v_res_2922_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(v_mvarId_2909_, v_val_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec(v___y_2911_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_2932_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___boxed(lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec(v___y_2935_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1(lean_object* v_00_u03b2_2947_, lean_object* v_x_2948_, lean_object* v_x_2949_, lean_object* v_x_2950_){
_start:
{
lean_object* v___x_2951_; 
v___x_2951_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_x_2948_, v_x_2949_, v_x_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2952_, lean_object* v_x_2953_, size_t v_x_2954_, size_t v_x_2955_, lean_object* v_x_2956_, lean_object* v_x_2957_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_2953_, v_x_2954_, v_x_2955_, v_x_2956_, v_x_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2959_, lean_object* v_x_2960_, lean_object* v_x_2961_, lean_object* v_x_2962_, lean_object* v_x_2963_, lean_object* v_x_2964_){
_start:
{
size_t v_x_161733__boxed_2965_; size_t v_x_161734__boxed_2966_; lean_object* v_res_2967_; 
v_x_161733__boxed_2965_ = lean_unbox_usize(v_x_2961_);
lean_dec(v_x_2961_);
v_x_161734__boxed_2966_ = lean_unbox_usize(v_x_2962_);
lean_dec(v_x_2962_);
v_res_2967_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(v_00_u03b2_2959_, v_x_2960_, v_x_161733__boxed_2965_, v_x_161734__boxed_2966_, v_x_2963_, v_x_2964_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_2968_, lean_object* v_n_2969_, lean_object* v_k_2970_, lean_object* v_v_2971_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(v_n_2969_, v_k_2970_, v_v_2971_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2973_, size_t v_depth_2974_, lean_object* v_keys_2975_, lean_object* v_vals_2976_, lean_object* v_heq_2977_, lean_object* v_i_2978_, lean_object* v_entries_2979_){
_start:
{
lean_object* v___x_2980_; 
v___x_2980_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_2974_, v_keys_2975_, v_vals_2976_, v_i_2978_, v_entries_2979_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2981_, lean_object* v_depth_2982_, lean_object* v_keys_2983_, lean_object* v_vals_2984_, lean_object* v_heq_2985_, lean_object* v_i_2986_, lean_object* v_entries_2987_){
_start:
{
size_t v_depth_boxed_2988_; lean_object* v_res_2989_; 
v_depth_boxed_2988_ = lean_unbox_usize(v_depth_2982_);
lean_dec(v_depth_2982_);
v_res_2989_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(v_00_u03b2_2981_, v_depth_boxed_2988_, v_keys_2983_, v_vals_2984_, v_heq_2985_, v_i_2986_, v_entries_2987_);
lean_dec_ref(v_vals_2984_);
lean_dec_ref(v_keys_2983_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_2990_, lean_object* v_x_2991_, lean_object* v_x_2992_, lean_object* v_x_2993_, lean_object* v_x_2994_){
_start:
{
lean_object* v___x_2995_; 
v___x_2995_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_x_2991_, v_x_2992_, v_x_2993_, v_x_2994_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(lean_object* v_type_2996_, lean_object* v_a_2997_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = l_Lean_Expr_getAppFn(v_type_2996_);
if (lean_obj_tag(v___x_2999_) == 4)
{
lean_object* v_declName_3000_; lean_object* v___x_3001_; 
v_declName_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_declName_3000_);
lean_dec_ref_known(v___x_2999_, 2);
v___x_3001_ = l_Lean_Meta_Grind_isEagerSplit___redArg(v_declName_3000_, v_a_2997_);
lean_dec(v_declName_3000_);
return v___x_3001_;
}
else
{
uint8_t v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
lean_dec_ref(v___x_2999_);
v___x_3002_ = 0;
v___x_3003_ = lean_box(v___x_3002_);
v___x_3004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3003_);
return v___x_3004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg___boxed(lean_object* v_type_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_){
_start:
{
lean_object* v_res_3008_; 
v_res_3008_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_3005_, v_a_3006_);
lean_dec_ref(v_a_3006_);
lean_dec_ref(v_type_3005_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(lean_object* v_type_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_){
_start:
{
lean_object* v___x_3020_; 
v___x_3020_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_type_3009_, v_a_3011_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___boxed(lean_object* v_type_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(v_type_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
lean_dec(v_a_3030_);
lean_dec_ref(v_a_3029_);
lean_dec(v_a_3028_);
lean_dec_ref(v_a_3027_);
lean_dec(v_a_3026_);
lean_dec_ref(v_a_3025_);
lean_dec(v_a_3024_);
lean_dec_ref(v_a_3023_);
lean_dec(v_a_3022_);
lean_dec_ref(v_type_3021_);
return v_res_3032_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3033_; 
v___x_3033_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_3033_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
return v___x_3035_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3036_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_3037_ = lean_unsigned_to_nat(0u);
v___x_3038_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3037_);
lean_ctor_set(v___x_3038_, 1, v___x_3037_);
lean_ctor_set(v___x_3038_, 2, v___x_3037_);
lean_ctor_set(v___x_3038_, 3, v___x_3037_);
lean_ctor_set(v___x_3038_, 4, v___x_3036_);
lean_ctor_set(v___x_3038_, 5, v___x_3036_);
lean_ctor_set(v___x_3038_, 6, v___x_3036_);
lean_ctor_set(v___x_3038_, 7, v___x_3036_);
lean_ctor_set(v___x_3038_, 8, v___x_3036_);
lean_ctor_set(v___x_3038_, 9, v___x_3036_);
return v___x_3038_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3039_ = lean_unsigned_to_nat(32u);
v___x_3040_ = lean_mk_empty_array_with_capacity(v___x_3039_);
v___x_3041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3040_);
return v___x_3041_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3042_ = ((size_t)5ULL);
v___x_3043_ = lean_unsigned_to_nat(0u);
v___x_3044_ = lean_unsigned_to_nat(32u);
v___x_3045_ = lean_mk_empty_array_with_capacity(v___x_3044_);
v___x_3046_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_3047_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3047_, 0, v___x_3046_);
lean_ctor_set(v___x_3047_, 1, v___x_3045_);
lean_ctor_set(v___x_3047_, 2, v___x_3043_);
lean_ctor_set(v___x_3047_, 3, v___x_3043_);
lean_ctor_set_usize(v___x_3047_, 4, v___x_3042_);
return v___x_3047_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3048_ = lean_box(1);
v___x_3049_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_3050_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_3051_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3050_);
lean_ctor_set(v___x_3051_, 1, v___x_3049_);
lean_ctor_set(v___x_3051_, 2, v___x_3048_);
return v___x_3051_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_3054_ = l_Lean_stringToMessageData(v___x_3053_);
return v___x_3054_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_3057_ = l_Lean_stringToMessageData(v___x_3056_);
return v___x_3057_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3059_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_3060_ = l_Lean_stringToMessageData(v___x_3059_);
return v___x_3060_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3062_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_3063_ = l_Lean_stringToMessageData(v___x_3062_);
return v___x_3063_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3065_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_3066_ = l_Lean_stringToMessageData(v___x_3065_);
return v___x_3066_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3068_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_3069_ = l_Lean_stringToMessageData(v___x_3068_);
return v___x_3069_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3071_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_3072_ = l_Lean_stringToMessageData(v___x_3071_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_3073_, lean_object* v_declHint_3074_, lean_object* v___y_3075_){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v_env_3079_; uint8_t v___x_3080_; 
v___x_3077_ = lean_box(0);
v___x_3078_ = lean_st_ref_get(v___y_3075_);
v_env_3079_ = lean_ctor_get(v___x_3078_, 0);
lean_inc_ref(v_env_3079_);
lean_dec(v___x_3078_);
v___x_3080_ = l_Lean_Name_isAnonymous(v_declHint_3074_);
if (v___x_3080_ == 0)
{
uint8_t v_isExporting_3081_; 
v_isExporting_3081_ = lean_ctor_get_uint8(v_env_3079_, sizeof(void*)*13);
if (v_isExporting_3081_ == 0)
{
lean_object* v___x_3082_; 
lean_dec_ref(v_env_3079_);
lean_dec(v_declHint_3074_);
v___x_3082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3082_, 0, v_msg_3073_);
return v___x_3082_;
}
else
{
lean_object* v___x_3083_; uint8_t v___x_3084_; 
lean_inc_ref(v_env_3079_);
v___x_3083_ = l_Lean_Environment_setExporting(v_env_3079_, v___x_3080_);
lean_inc(v_declHint_3074_);
lean_inc_ref(v___x_3083_);
v___x_3084_ = l_Lean_Environment_contains(v___x_3083_, v_declHint_3074_, v_isExporting_3081_);
if (v___x_3084_ == 0)
{
lean_object* v___x_3085_; 
lean_dec_ref(v___x_3083_);
lean_dec_ref(v_env_3079_);
lean_dec(v_declHint_3074_);
v___x_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3085_, 0, v_msg_3073_);
return v___x_3085_;
}
else
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v_c_3091_; lean_object* v___x_3092_; 
v___x_3086_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_3087_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_3088_ = l_Lean_Options_empty;
lean_inc_ref(v___x_3083_);
v___x_3089_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3083_);
lean_ctor_set(v___x_3089_, 1, v___x_3086_);
lean_ctor_set(v___x_3089_, 2, v___x_3087_);
lean_ctor_set(v___x_3089_, 3, v___x_3088_);
lean_inc(v_declHint_3074_);
v___x_3090_ = l_Lean_MessageData_ofConstName(v_declHint_3074_, v___x_3080_);
v_c_3091_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3091_, 0, v___x_3089_);
lean_ctor_set(v_c_3091_, 1, v___x_3090_);
v___x_3092_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_3083_, v_declHint_3074_);
lean_dec_ref(v___x_3083_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
lean_dec_ref(v_env_3079_);
lean_dec(v_declHint_3074_);
v___x_3093_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_3094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
lean_ctor_set(v___x_3094_, 1, v_c_3091_);
v___x_3095_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_3096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3094_);
lean_ctor_set(v___x_3096_, 1, v___x_3095_);
v___x_3097_ = l_Lean_MessageData_note(v___x_3096_);
v___x_3098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3098_, 0, v_msg_3073_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3098_);
return v___x_3099_;
}
else
{
lean_object* v_val_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3134_; 
v_val_3100_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3102_ = v___x_3092_;
v_isShared_3103_ = v_isSharedCheck_3134_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_val_3100_);
lean_dec(v___x_3092_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3134_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3104_; lean_object* v_moduleNames_3105_; lean_object* v_mod_3106_; uint8_t v___x_3107_; 
v___x_3104_ = l_Lean_Environment_header(v_env_3079_);
lean_dec_ref(v_env_3079_);
v_moduleNames_3105_ = lean_ctor_get(v___x_3104_, 4);
lean_inc_ref(v_moduleNames_3105_);
lean_dec_ref(v___x_3104_);
v_mod_3106_ = lean_array_get(v___x_3077_, v_moduleNames_3105_, v_val_3100_);
lean_dec(v_val_3100_);
lean_dec_ref(v_moduleNames_3105_);
v___x_3107_ = l_Lean_isPrivateName(v_declHint_3074_);
lean_dec(v_declHint_3074_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3119_; 
v___x_3108_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_3109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
lean_ctor_set(v___x_3109_, 1, v_c_3091_);
v___x_3110_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_3111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3109_);
lean_ctor_set(v___x_3111_, 1, v___x_3110_);
v___x_3112_ = l_Lean_MessageData_ofName(v_mod_3106_);
v___x_3113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3111_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v___x_3114_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_3115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3113_);
lean_ctor_set(v___x_3115_, 1, v___x_3114_);
v___x_3116_ = l_Lean_MessageData_note(v___x_3115_);
v___x_3117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3117_, 0, v_msg_3073_);
lean_ctor_set(v___x_3117_, 1, v___x_3116_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set_tag(v___x_3102_, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3117_);
v___x_3119_ = v___x_3102_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v___x_3117_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
else
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3132_; 
v___x_3121_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_3122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3121_);
lean_ctor_set(v___x_3122_, 1, v_c_3091_);
v___x_3123_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_3124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3122_);
lean_ctor_set(v___x_3124_, 1, v___x_3123_);
v___x_3125_ = l_Lean_MessageData_ofName(v_mod_3106_);
v___x_3126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3124_);
lean_ctor_set(v___x_3126_, 1, v___x_3125_);
v___x_3127_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_3128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3126_);
lean_ctor_set(v___x_3128_, 1, v___x_3127_);
v___x_3129_ = l_Lean_MessageData_note(v___x_3128_);
v___x_3130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3130_, 0, v_msg_3073_);
lean_ctor_set(v___x_3130_, 1, v___x_3129_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set_tag(v___x_3102_, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3130_);
v___x_3132_ = v___x_3102_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_3130_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3135_; 
lean_dec_ref(v_env_3079_);
lean_dec(v_declHint_3074_);
v___x_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3135_, 0, v_msg_3073_);
return v___x_3135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_3136_, lean_object* v_declHint_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_3136_, v_declHint_3137_, v___y_3138_);
lean_dec(v___y_3138_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_3141_, lean_object* v_declHint_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
lean_object* v___x_3146_; lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3156_; 
v___x_3146_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_3141_, v_declHint_3142_, v___y_3144_);
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3149_ = v___x_3146_;
v_isShared_3150_ = v_isSharedCheck_3156_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3146_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3156_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3154_; 
v___x_3151_ = l_Lean_unknownIdentifierMessageTag;
v___x_3152_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3151_);
lean_ctor_set(v___x_3152_, 1, v_a_3147_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 0, v___x_3152_);
v___x_3154_ = v___x_3149_;
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
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_3157_, lean_object* v_declHint_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_3157_, v_declHint_3158_, v___y_3159_, v___y_3160_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msgData_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v___x_3167_; lean_object* v_toCold_3168_; lean_object* v_env_3169_; lean_object* v_options_3170_; uint8_t v___x_3171_; lean_object* v_env_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3167_ = lean_st_ref_get(v___y_3165_);
v_toCold_3168_ = lean_ctor_get(v___y_3164_, 0);
v_env_3169_ = lean_ctor_get(v___x_3167_, 0);
lean_inc_ref(v_env_3169_);
lean_dec(v___x_3167_);
v_options_3170_ = lean_ctor_get(v_toCold_3168_, 2);
v___x_3171_ = 0;
v_env_3172_ = l_Lean_Environment_setRecordingDeps(v_env_3169_, v___x_3171_);
v___x_3173_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_3174_ = lean_unsigned_to_nat(32u);
v___x_3175_ = lean_mk_empty_array_with_capacity(v___x_3174_);
lean_dec_ref(v___x_3175_);
v___x_3176_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
lean_inc_ref(v_options_3170_);
v___x_3177_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3177_, 0, v_env_3172_);
lean_ctor_set(v___x_3177_, 1, v___x_3173_);
lean_ctor_set(v___x_3177_, 2, v___x_3176_);
lean_ctor_set(v___x_3177_, 3, v_options_3170_);
v___x_3178_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
lean_ctor_set(v___x_3178_, 1, v_msgData_3163_);
v___x_3179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3178_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msgData_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_3180_, v___y_3181_, v___y_3182_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_msg_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v_ref_3189_; lean_object* v___x_3190_; lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3199_; 
v_ref_3189_ = lean_ctor_get(v___y_3186_, 2);
v___x_3190_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_3185_, v___y_3186_, v___y_3187_);
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3193_ = v___x_3190_;
v_isShared_3194_ = v_isSharedCheck_3199_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3190_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3199_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3195_; lean_object* v___x_3197_; 
lean_inc(v_ref_3189_);
v___x_3195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3195_, 0, v_ref_3189_);
lean_ctor_set(v___x_3195_, 1, v_a_3191_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set_tag(v___x_3193_, 1);
lean_ctor_set(v___x_3193_, 0, v___x_3195_);
v___x_3197_ = v___x_3193_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3195_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_msg_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_3200_, v___y_3201_, v___y_3202_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_3205_, lean_object* v_msg_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v_toCold_3210_; lean_object* v_currRecDepth_3211_; lean_object* v_ref_3212_; uint16_t v_optionFlags_3213_; uint8_t v_suppressElabErrors_3214_; uint8_t v_checkDeprecated_3215_; uint8_t v_isRecordingDeps_3216_; lean_object* v_ref_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
v_toCold_3210_ = lean_ctor_get(v___y_3207_, 0);
v_currRecDepth_3211_ = lean_ctor_get(v___y_3207_, 1);
v_ref_3212_ = lean_ctor_get(v___y_3207_, 2);
v_optionFlags_3213_ = lean_ctor_get_uint16(v___y_3207_, sizeof(void*)*3);
v_suppressElabErrors_3214_ = lean_ctor_get_uint8(v___y_3207_, sizeof(void*)*3 + 2);
v_checkDeprecated_3215_ = lean_ctor_get_uint8(v___y_3207_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3216_ = lean_ctor_get_uint8(v___y_3207_, sizeof(void*)*3 + 4);
v_ref_3217_ = l_Lean_replaceRef(v_ref_3205_, v_ref_3212_);
lean_inc(v_currRecDepth_3211_);
lean_inc_ref(v_toCold_3210_);
v___x_3218_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3218_, 0, v_toCold_3210_);
lean_ctor_set(v___x_3218_, 1, v_currRecDepth_3211_);
lean_ctor_set(v___x_3218_, 2, v_ref_3217_);
lean_ctor_set_uint16(v___x_3218_, sizeof(void*)*3, v_optionFlags_3213_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 2, v_suppressElabErrors_3214_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 3, v_checkDeprecated_3215_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 4, v_isRecordingDeps_3216_);
v___x_3219_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_3206_, v___x_3218_, v___y_3208_);
lean_dec_ref_known(v___x_3218_, 3);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_3220_, lean_object* v_msg_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3220_, v_msg_3221_, v___y_3222_, v___y_3223_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
lean_dec(v_ref_3220_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_3226_, lean_object* v_msg_3227_, lean_object* v_declHint_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
lean_object* v___x_3232_; lean_object* v_a_3233_; lean_object* v___x_3234_; 
v___x_3232_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_3227_, v_declHint_3228_, v___y_3229_, v___y_3230_);
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_a_3233_);
lean_dec_ref(v___x_3232_);
v___x_3234_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3226_, v_a_3233_, v___y_3229_, v___y_3230_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_3235_, lean_object* v_msg_3236_, lean_object* v_declHint_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3235_, v_msg_3236_, v_declHint_3237_, v___y_3238_, v___y_3239_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v_ref_3235_);
return v_res_3241_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3243_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_3244_ = l_Lean_stringToMessageData(v___x_3243_);
return v___x_3244_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3246_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_3247_ = l_Lean_stringToMessageData(v___x_3246_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3248_, lean_object* v_constName_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
lean_object* v___x_3253_; uint8_t v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3253_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_3254_ = 0;
lean_inc(v_constName_3249_);
v___x_3255_ = l_Lean_MessageData_ofConstName(v_constName_3249_, v___x_3254_);
v___x_3256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3253_);
lean_ctor_set(v___x_3256_, 1, v___x_3255_);
v___x_3257_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_3258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3256_);
lean_ctor_set(v___x_3258_, 1, v___x_3257_);
v___x_3259_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3248_, v___x_3258_, v_constName_3249_, v___y_3250_, v___y_3251_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3260_, lean_object* v_constName_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_){
_start:
{
lean_object* v_res_3265_; 
v_res_3265_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_3260_, v_constName_3261_, v___y_3262_, v___y_3263_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec(v_ref_3260_);
return v_res_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(lean_object* v_constName_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
lean_object* v_ref_3270_; lean_object* v___x_3271_; 
v_ref_3270_ = lean_ctor_get(v___y_3267_, 2);
v___x_3271_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_3270_, v_constName_3266_, v___y_3267_, v___y_3268_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_3272_, v___y_3273_, v___y_3274_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(lean_object* v_constName_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
lean_object* v___x_3281_; lean_object* v_env_3282_; uint8_t v___x_3283_; lean_object* v___x_3284_; 
v___x_3281_ = lean_st_ref_get(v___y_3279_);
v_env_3282_ = lean_ctor_get(v___x_3281_, 0);
lean_inc_ref(v_env_3282_);
lean_dec(v___x_3281_);
v___x_3283_ = 0;
lean_inc(v_constName_3277_);
v___x_3284_ = l_Lean_Environment_find_x3f(v_env_3282_, v_constName_3277_, v___x_3283_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v___x_3285_; 
v___x_3285_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_3277_, v___y_3278_, v___y_3279_);
return v___x_3285_;
}
else
{
lean_object* v_val_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
lean_dec(v_constName_3277_);
v_val_3286_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___x_3284_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_val_3286_);
lean_dec(v___x_3284_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
lean_ctor_set_tag(v___x_3288_, 0);
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_val_3286_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0___boxed(lean_object* v_constName_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_constName_3294_, v___y_3295_, v___y_3296_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(lean_object* v_type_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l_Lean_Expr_getAppFn(v_type_3299_);
if (lean_obj_tag(v___x_3303_) == 4)
{
lean_object* v_declName_3304_; lean_object* v___x_3305_; 
v_declName_3304_ = lean_ctor_get(v___x_3303_, 0);
lean_inc(v_declName_3304_);
lean_dec_ref_known(v___x_3303_, 2);
v___x_3305_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_declName_3304_, v_a_3300_, v_a_3301_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3323_; 
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3308_ = v___x_3305_;
v_isShared_3309_ = v_isSharedCheck_3323_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3305_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3323_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
if (lean_obj_tag(v_a_3306_) == 5)
{
lean_object* v_val_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; uint8_t v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3316_; 
v_val_3310_ = lean_ctor_get(v_a_3306_, 0);
lean_inc_ref(v_val_3310_);
lean_dec_ref_known(v_a_3306_, 1);
v___x_3311_ = l_Lean_InductiveVal_numCtors(v_val_3310_);
lean_dec_ref(v_val_3310_);
v___x_3312_ = lean_unsigned_to_nat(1u);
v___x_3313_ = lean_nat_dec_le(v___x_3311_, v___x_3312_);
lean_dec(v___x_3311_);
v___x_3314_ = lean_box(v___x_3313_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 0, v___x_3314_);
v___x_3316_ = v___x_3308_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3314_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
else
{
uint8_t v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3321_; 
lean_dec(v_a_3306_);
v___x_3318_ = 0;
v___x_3319_ = lean_box(v___x_3318_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 0, v___x_3319_);
v___x_3321_ = v___x_3308_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3319_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
}
else
{
lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3331_; 
v_a_3324_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3326_ = v___x_3305_;
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3305_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3329_; 
if (v_isShared_3327_ == 0)
{
v___x_3329_ = v___x_3326_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3324_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
}
else
{
uint8_t v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
lean_dec_ref(v___x_3303_);
v___x_3332_ = 0;
v___x_3333_ = lean_box(v___x_3332_);
v___x_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
return v___x_3334_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive___boxed(lean_object* v_type_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_type_3335_, v_a_3336_, v_a_3337_);
lean_dec(v_a_3337_);
lean_dec_ref(v_a_3336_);
lean_dec_ref(v_type_3335_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(lean_object* v_00_u03b1_3340_, lean_object* v_constName_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_){
_start:
{
lean_object* v___x_3345_; 
v___x_3345_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_3341_, v___y_3342_, v___y_3343_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3346_, lean_object* v_constName_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
lean_object* v_res_3351_; 
v_res_3351_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(v_00_u03b1_3346_, v_constName_3347_, v___y_3348_, v___y_3349_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3352_, lean_object* v_ref_3353_, lean_object* v_constName_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
lean_object* v___x_3358_; 
v___x_3358_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_3353_, v_constName_3354_, v___y_3355_, v___y_3356_);
return v___x_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3359_, lean_object* v_ref_3360_, lean_object* v_constName_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(v_00_u03b1_3359_, v_ref_3360_, v_constName_3361_, v___y_3362_, v___y_3363_);
lean_dec(v___y_3363_);
lean_dec_ref(v___y_3362_);
lean_dec(v_ref_3360_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3366_, lean_object* v_ref_3367_, lean_object* v_msg_3368_, lean_object* v_declHint_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_){
_start:
{
lean_object* v___x_3373_; 
v___x_3373_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3367_, v_msg_3368_, v_declHint_3369_, v___y_3370_, v___y_3371_);
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3374_, lean_object* v_ref_3375_, lean_object* v_msg_3376_, lean_object* v_declHint_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3374_, v_ref_3375_, v_msg_3376_, v_declHint_3377_, v___y_3378_, v___y_3379_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v_ref_3375_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_3382_, lean_object* v_declHint_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
lean_object* v___x_3387_; 
v___x_3387_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_3382_, v_declHint_3383_, v___y_3385_);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_3388_, lean_object* v_declHint_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_3388_, v_declHint_3389_, v___y_3390_, v___y_3391_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_3394_, lean_object* v_ref_3395_, lean_object* v_msg_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v___x_3400_; 
v___x_3400_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3395_, v_msg_3396_, v___y_3397_, v___y_3398_);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_3401_, lean_object* v_ref_3402_, lean_object* v_msg_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_3401_, v_ref_3402_, v_msg_3403_, v___y_3404_, v___y_3405_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v_ref_3402_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_3408_, lean_object* v_msg_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_3409_, v___y_3410_, v___y_3411_);
return v___x_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_3414_, lean_object* v_msg_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_3414_, v_msg_3415_, v___y_3416_, v___y_3417_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(lean_object* v_goal_3420_, lean_object* v_fvarId_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_){
_start:
{
lean_object* v_toGoalState_3427_; lean_object* v_mvarId_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3464_; 
v_toGoalState_3427_ = lean_ctor_get(v_goal_3420_, 0);
v_mvarId_3428_ = lean_ctor_get(v_goal_3420_, 1);
v_isSharedCheck_3464_ = !lean_is_exclusive(v_goal_3420_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3430_ = v_goal_3420_;
v_isShared_3431_ = v_isSharedCheck_3464_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_mvarId_3428_);
lean_inc(v_toGoalState_3427_);
lean_dec(v_goal_3420_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3464_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3432_; 
v___x_3432_ = l_Lean_Meta_Grind_injection_x3f(v_mvarId_3428_, v_fvarId_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3455_; 
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3435_ = v___x_3432_;
v_isShared_3436_ = v_isSharedCheck_3455_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3432_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3455_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
if (lean_obj_tag(v_a_3433_) == 1)
{
lean_object* v_val_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3450_; 
v_val_3437_ = lean_ctor_get(v_a_3433_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v_a_3433_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3439_ = v_a_3433_;
v_isShared_3440_ = v_isSharedCheck_3450_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_val_3437_);
lean_dec(v_a_3433_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3450_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 1, v_val_3437_);
v___x_3442_ = v___x_3430_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_toGoalState_3427_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v_val_3437_);
v___x_3442_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
lean_object* v___x_3444_; 
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 0, v___x_3442_);
v___x_3444_ = v___x_3439_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3442_);
v___x_3444_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
lean_object* v___x_3446_; 
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 0, v___x_3444_);
v___x_3446_ = v___x_3435_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3444_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
}
}
else
{
lean_object* v___x_3451_; lean_object* v___x_3453_; 
lean_dec(v_a_3433_);
lean_del_object(v___x_3430_);
lean_dec_ref(v_toGoalState_3427_);
v___x_3451_ = lean_box(0);
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 0, v___x_3451_);
v___x_3453_ = v___x_3435_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3451_);
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
else
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
lean_del_object(v___x_3430_);
lean_dec_ref(v_toGoalState_3427_);
v_a_3456_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3458_ = v___x_3432_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3432_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f___boxed(lean_object* v_goal_3465_, lean_object* v_fvarId_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_){
_start:
{
lean_object* v_res_3472_; 
v_res_3472_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_3465_, v_fvarId_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_);
lean_dec(v_a_3470_);
lean_dec_ref(v_a_3469_);
lean_dec(v_a_3468_);
lean_dec_ref(v_a_3467_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(lean_object* v_mvarId_3473_, lean_object* v_x_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
lean_object* v___x_3480_; 
v___x_3480_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3473_, v_x_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3488_; 
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3483_ = v___x_3480_;
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3480_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3486_; 
if (v_isShared_3484_ == 0)
{
v___x_3486_ = v___x_3483_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3481_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
else
{
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3496_; 
v_a_3489_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3491_ = v___x_3480_;
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3480_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3494_; 
if (v_isShared_3492_ == 0)
{
v___x_3494_ = v___x_3491_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3489_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg___boxed(lean_object* v_mvarId_3497_, lean_object* v_x_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
lean_object* v_res_3504_; 
v_res_3504_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3497_, v_x_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(lean_object* v_00_u03b1_3505_, lean_object* v_mvarId_3506_, lean_object* v_x_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
lean_object* v___x_3513_; 
v___x_3513_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3506_, v_x_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___boxed(lean_object* v_00_u03b1_3514_, lean_object* v_mvarId_3515_, lean_object* v_x_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(v_00_u03b1_3514_, v_mvarId_3515_, v_x_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(lean_object* v_mvarId_3523_, lean_object* v_toGoalState_3524_, lean_object* v_goal_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
lean_object* v___x_3531_; 
lean_inc(v_mvarId_3523_);
v___x_3531_ = l_Lean_MVarId_getType(v_mvarId_3523_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3532_; lean_object* v___x_3533_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3532_);
lean_dec_ref_known(v___x_3531_, 1);
v___x_3533_ = l_Lean_Meta_isProp(v_a_3532_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3560_; 
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3536_ = v___x_3533_;
v_isShared_3537_ = v_isSharedCheck_3560_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3533_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3560_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
uint8_t v___x_3538_; 
v___x_3538_ = lean_unbox(v_a_3534_);
lean_dec(v_a_3534_);
if (v___x_3538_ == 0)
{
lean_object* v___x_3539_; 
lean_del_object(v___x_3536_);
lean_dec_ref(v_goal_3525_);
v___x_3539_ = l_Lean_MVarId_exfalso(v_mvarId_3523_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3548_; 
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3542_ = v___x_3539_;
v_isShared_3543_ = v_isSharedCheck_3548_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3539_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3548_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3544_; lean_object* v___x_3546_; 
v___x_3544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3544_, 0, v_toGoalState_3524_);
lean_ctor_set(v___x_3544_, 1, v_a_3540_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 0, v___x_3544_);
v___x_3546_ = v___x_3542_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v___x_3544_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
else
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3556_; 
lean_dec_ref(v_toGoalState_3524_);
v_a_3549_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3551_ = v___x_3539_;
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3539_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3554_; 
if (v_isShared_3552_ == 0)
{
v___x_3554_ = v___x_3551_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_a_3549_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
}
}
else
{
lean_object* v___x_3558_; 
lean_dec_ref(v_toGoalState_3524_);
lean_dec(v_mvarId_3523_);
if (v_isShared_3537_ == 0)
{
lean_ctor_set(v___x_3536_, 0, v_goal_3525_);
v___x_3558_ = v___x_3536_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_goal_3525_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
lean_dec_ref(v_goal_3525_);
lean_dec_ref(v_toGoalState_3524_);
lean_dec(v_mvarId_3523_);
v_a_3561_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3533_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3533_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec_ref(v_goal_3525_);
lean_dec_ref(v_toGoalState_3524_);
lean_dec(v_mvarId_3523_);
v_a_3569_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3531_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3531_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed(lean_object* v_mvarId_3577_, lean_object* v_toGoalState_3578_, lean_object* v_goal_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(v_mvarId_3577_, v_toGoalState_3578_, v_goal_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(lean_object* v_goal_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_){
_start:
{
lean_object* v_toGoalState_3592_; lean_object* v_mvarId_3593_; lean_object* v___f_3594_; lean_object* v___x_3595_; 
v_toGoalState_3592_ = lean_ctor_get(v_goal_3586_, 0);
lean_inc_ref(v_toGoalState_3592_);
v_mvarId_3593_ = lean_ctor_get(v_goal_3586_, 1);
lean_inc_n(v_mvarId_3593_, 2);
v___f_3594_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3594_, 0, v_mvarId_3593_);
lean_closure_set(v___f_3594_, 1, v_toGoalState_3592_);
lean_closure_set(v___f_3594_, 2, v_goal_3586_);
v___x_3595_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_3593_, v___f_3594_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___boxed(lean_object* v_goal_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___lam__0(lean_object* v_toGoalState_3603_, lean_object* v_mvarId_3604_, lean_object* v_goal_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
lean_object* v_mvarId_3617_; lean_object* v___x_3620_; 
lean_inc(v_mvarId_3604_);
v___x_3620_ = l_Lean_MVarId_getType(v_mvarId_3604_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v_a_3621_; lean_object* v___x_3622_; 
v_a_3621_ = lean_ctor_get(v___x_3620_, 0);
lean_inc_n(v_a_3621_, 2);
lean_dec_ref_known(v___x_3620_, 1);
v___x_3622_ = l_Lean_Meta_Grind_simpCore(v_a_3621_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
if (lean_obj_tag(v___x_3622_) == 0)
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3654_; 
v_a_3623_ = lean_ctor_get(v___x_3622_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3625_ = v___x_3622_;
v_isShared_3626_ = v_isSharedCheck_3654_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3622_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3654_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v_expr_3627_; lean_object* v_proof_x3f_3628_; uint8_t v___x_3629_; 
v_expr_3627_ = lean_ctor_get(v_a_3623_, 0);
lean_inc_ref(v_expr_3627_);
v_proof_x3f_3628_ = lean_ctor_get(v_a_3623_, 1);
lean_inc(v_proof_x3f_3628_);
lean_dec(v_a_3623_);
v___x_3629_ = lean_expr_eqv(v_expr_3627_, v_a_3621_);
lean_dec(v_a_3621_);
if (v___x_3629_ == 0)
{
lean_del_object(v___x_3625_);
lean_dec_ref(v_goal_3605_);
if (lean_obj_tag(v_proof_x3f_3628_) == 0)
{
lean_object* v___x_3630_; 
v___x_3630_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_3604_, v_expr_3627_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_object* v_a_3631_; 
v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
lean_inc(v_a_3631_);
lean_dec_ref_known(v___x_3630_, 1);
v_mvarId_3617_ = v_a_3631_;
goto v___jp_3616_;
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_dec_ref(v_toGoalState_3603_);
v_a_3632_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3630_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3630_);
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
lean_object* v_val_3640_; lean_object* v___x_3641_; 
v_val_3640_ = lean_ctor_get(v_proof_x3f_3628_, 0);
lean_inc(v_val_3640_);
lean_dec_ref_known(v_proof_x3f_3628_, 1);
v___x_3641_ = l_Lean_MVarId_replaceTargetEq(v_mvarId_3604_, v_expr_3627_, v_val_3640_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
lean_inc(v_a_3642_);
lean_dec_ref_known(v___x_3641_, 1);
v_mvarId_3617_ = v_a_3642_;
goto v___jp_3616_;
}
else
{
lean_object* v_a_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3650_; 
lean_dec_ref(v_toGoalState_3603_);
v_a_3643_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3645_ = v___x_3641_;
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_a_3643_);
lean_dec(v___x_3641_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3648_; 
if (v_isShared_3646_ == 0)
{
v___x_3648_ = v___x_3645_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_a_3643_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
}
}
else
{
lean_object* v___x_3652_; 
lean_dec(v_proof_x3f_3628_);
lean_dec_ref(v_expr_3627_);
lean_dec(v_mvarId_3604_);
lean_dec_ref(v_toGoalState_3603_);
if (v_isShared_3626_ == 0)
{
lean_ctor_set(v___x_3625_, 0, v_goal_3605_);
v___x_3652_ = v___x_3625_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_goal_3605_);
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
lean_dec(v_a_3621_);
lean_dec_ref(v_goal_3605_);
lean_dec(v_mvarId_3604_);
lean_dec_ref(v_toGoalState_3603_);
v_a_3655_ = lean_ctor_get(v___x_3622_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3657_ = v___x_3622_;
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3622_);
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
else
{
lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3670_; 
lean_dec_ref(v_goal_3605_);
lean_dec(v_mvarId_3604_);
lean_dec_ref(v_toGoalState_3603_);
v_a_3663_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3665_ = v___x_3620_;
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___x_3620_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3668_; 
if (v_isShared_3666_ == 0)
{
v___x_3668_ = v___x_3665_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3663_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
v___jp_3616_:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3618_, 0, v_toGoalState_3603_);
lean_ctor_set(v___x_3618_, 1, v_mvarId_3617_);
v___x_3619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3618_);
return v___x_3619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___lam__0___boxed(lean_object* v_toGoalState_3671_, lean_object* v_mvarId_3672_, lean_object* v_goal_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_){
_start:
{
lean_object* v_res_3684_; 
v_res_3684_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___lam__0(v_toGoalState_3671_, v_mvarId_3672_, v_goal_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_);
lean_dec(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
lean_dec(v___y_3678_);
lean_dec_ref(v___y_3677_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec(v___y_3674_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget(lean_object* v_goal_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_){
_start:
{
lean_object* v_toGoalState_3696_; lean_object* v_mvarId_3697_; lean_object* v___f_3698_; lean_object* v___x_3699_; 
v_toGoalState_3696_ = lean_ctor_get(v_goal_3685_, 0);
lean_inc_ref(v_toGoalState_3696_);
v_mvarId_3697_ = lean_ctor_get(v_goal_3685_, 1);
lean_inc_n(v_mvarId_3697_, 2);
v___f_3698_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___lam__0___boxed), 13, 3);
lean_closure_set(v___f_3698_, 0, v_toGoalState_3696_);
lean_closure_set(v___f_3698_, 1, v_mvarId_3697_);
lean_closure_set(v___f_3698_, 2, v_goal_3685_);
v___x_3699_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3697_, v___f_3698_, v_a_3686_, v_a_3687_, v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget___boxed(lean_object* v_goal_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget(v_goal_3700_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_);
lean_dec(v_a_3709_);
lean_dec_ref(v_a_3708_);
lean_dec(v_a_3707_);
lean_dec_ref(v_a_3706_);
lean_dec(v_a_3705_);
lean_dec_ref(v_a_3704_);
lean_dec(v_a_3703_);
lean_dec_ref(v_a_3702_);
lean_dec(v_a_3701_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f(lean_object* v_goal_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_){
_start:
{
lean_object* v_mvarId_3718_; lean_object* v___x_3719_; 
v_mvarId_3718_ = lean_ctor_get(v_goal_3712_, 1);
lean_inc(v_mvarId_3718_);
lean_dec_ref(v_goal_3712_);
v___x_3719_ = l_Lean_MVarId_getDecl(v_mvarId_3718_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_);
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3729_; 
v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3722_ = v___x_3719_;
v_isShared_3723_ = v_isSharedCheck_3729_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3719_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3729_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v_lctx_3724_; lean_object* v___x_3725_; lean_object* v___x_3727_; 
v_lctx_3724_ = lean_ctor_get(v_a_3720_, 1);
lean_inc_ref(v_lctx_3724_);
lean_dec(v_a_3720_);
v___x_3725_ = l_Lean_LocalContext_lastDecl(v_lctx_3724_);
lean_dec_ref(v_lctx_3724_);
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 0, v___x_3725_);
v___x_3727_ = v___x_3722_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3725_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
v_a_3730_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3719_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3719_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_lastDecl_x3f___boxed(lean_object* v_goal_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_){
_start:
{
lean_object* v_res_3744_; 
v_res_3744_ = l_Lean_Meta_Grind_Goal_lastDecl_x3f(v_goal_3738_, v_a_3739_, v_a_3740_, v_a_3741_, v_a_3742_);
lean_dec(v_a_3742_);
lean_dec_ref(v_a_3741_);
lean_dec(v_a_3740_);
lean_dec_ref(v_a_3739_);
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(lean_object* v_goal_3745_, lean_object* v_fvarId_3746_, lean_object* v_generation_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3758_ = lean_st_mk_ref(v_goal_3745_);
lean_inc(v_fvarId_3746_);
v___x_3759_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_3746_, v_generation_3747_, v___x_3758_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v___x_3760_; 
lean_dec_ref_known(v___x_3759_, 1);
v___x_3760_ = l_Lean_FVarId_getType___redArg(v_fvarId_3746_, v___y_3753_, v___y_3755_, v___y_3756_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_a_3761_; lean_object* v___x_3762_; 
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
lean_inc(v_a_3761_);
lean_dec_ref_known(v___x_3760_, 1);
v___x_3762_ = l_Lean_Meta_Grind_markCaseSplitAsResolved(v_a_3761_, v___x_3758_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3771_; 
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3771_ == 0)
{
lean_object* v_unused_3772_; 
v_unused_3772_ = lean_ctor_get(v___x_3762_, 0);
lean_dec(v_unused_3772_);
v___x_3764_ = v___x_3762_;
v_isShared_3765_ = v_isSharedCheck_3771_;
goto v_resetjp_3763_;
}
else
{
lean_dec(v___x_3762_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3771_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3769_; 
v___x_3766_ = lean_st_ref_get(v___x_3758_);
v___x_3767_ = lean_st_ref_get(v___x_3758_);
lean_dec(v___x_3758_);
lean_dec(v___x_3767_);
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 0, v___x_3766_);
v___x_3769_ = v___x_3764_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v___x_3766_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
else
{
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3780_; 
lean_dec(v___x_3758_);
v_a_3773_ = lean_ctor_get(v___x_3762_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3775_ = v___x_3762_;
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3762_);
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
else
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
lean_dec(v___x_3758_);
v_a_3781_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3760_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3760_);
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
else
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3796_; 
lean_dec(v___x_3758_);
lean_dec(v_fvarId_3746_);
v_a_3789_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3791_ = v___x_3759_;
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3759_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3794_; 
if (v_isShared_3792_ == 0)
{
v___x_3794_ = v___x_3791_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_a_3789_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed(lean_object* v_goal_3797_, lean_object* v_fvarId_3798_, lean_object* v_generation_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_){
_start:
{
lean_object* v_res_3810_; 
v_res_3810_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(v_goal_3797_, v_fvarId_3798_, v_generation_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
lean_dec(v___y_3808_);
lean_dec_ref(v___y_3807_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec(v___y_3800_);
return v_res_3810_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(lean_object* v_kp_3811_, lean_object* v_as_x27_3812_, lean_object* v_b_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
if (lean_obj_tag(v_as_x27_3812_) == 0)
{
lean_object* v___x_3824_; 
lean_dec_ref(v_kp_3811_);
v___x_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3824_, 0, v_b_3813_);
return v___x_3824_;
}
else
{
lean_object* v_head_3825_; lean_object* v_tail_3826_; lean_object* v_fst_3827_; lean_object* v_snd_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3854_; 
v_head_3825_ = lean_ctor_get(v_as_x27_3812_, 0);
v_tail_3826_ = lean_ctor_get(v_as_x27_3812_, 1);
v_fst_3827_ = lean_ctor_get(v_b_3813_, 0);
v_snd_3828_ = lean_ctor_get(v_b_3813_, 1);
v_isSharedCheck_3854_ = !lean_is_exclusive(v_b_3813_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3830_ = v_b_3813_;
v_isShared_3831_ = v_isSharedCheck_3854_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_snd_3828_);
lean_inc(v_fst_3827_);
lean_dec(v_b_3813_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3854_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3832_; 
lean_inc_ref(v_kp_3811_);
lean_inc(v___y_3822_);
lean_inc_ref(v___y_3821_);
lean_inc(v___y_3820_);
lean_inc_ref(v___y_3819_);
lean_inc(v___y_3818_);
lean_inc_ref(v___y_3817_);
lean_inc(v___y_3816_);
lean_inc_ref(v___y_3815_);
lean_inc(v___y_3814_);
lean_inc(v_head_3825_);
v___x_3832_ = lean_apply_11(v_kp_3811_, v_head_3825_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, lean_box(0));
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v_a_3833_; 
v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
lean_inc(v_a_3833_);
lean_dec_ref_known(v___x_3832_, 1);
if (lean_obj_tag(v_a_3833_) == 0)
{
lean_object* v_seq_3834_; lean_object* v___x_3835_; lean_object* v___x_3837_; 
v_seq_3834_ = lean_ctor_get(v_a_3833_, 0);
lean_inc(v_seq_3834_);
lean_dec_ref_known(v_a_3833_, 1);
v___x_3835_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_fst_3827_, v_seq_3834_);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 0, v___x_3835_);
v___x_3837_ = v___x_3830_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v___x_3835_);
lean_ctor_set(v_reuseFailAlloc_3839_, 1, v_snd_3828_);
v___x_3837_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
v_as_x27_3812_ = v_tail_3826_;
v_b_3813_ = v___x_3837_;
goto _start;
}
}
else
{
lean_object* v_gs_3840_; lean_object* v___x_3841_; lean_object* v___x_3843_; 
v_gs_3840_ = lean_ctor_get(v_a_3833_, 0);
lean_inc(v_gs_3840_);
lean_dec_ref_known(v_a_3833_, 1);
v___x_3841_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_snd_3828_, v_gs_3840_);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 1, v___x_3841_);
v___x_3843_ = v___x_3830_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_fst_3827_);
lean_ctor_set(v_reuseFailAlloc_3845_, 1, v___x_3841_);
v___x_3843_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
v_as_x27_3812_ = v_tail_3826_;
v_b_3813_ = v___x_3843_;
goto _start;
}
}
}
else
{
lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3853_; 
lean_del_object(v___x_3830_);
lean_dec(v_snd_3828_);
lean_dec(v_fst_3827_);
lean_dec_ref(v_kp_3811_);
v_a_3846_ = lean_ctor_get(v___x_3832_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3848_ = v___x_3832_;
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v___x_3832_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3851_; 
if (v_isShared_3849_ == 0)
{
v___x_3851_ = v___x_3848_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_a_3846_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg___boxed(lean_object* v_kp_3855_, lean_object* v_as_x27_3856_, lean_object* v_b_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3855_, v_as_x27_3856_, v_b_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec(v_as_x27_3856_);
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(lean_object* v___x_3869_, uint8_t v___x_3870_, uint64_t v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_){
_start:
{
if (lean_obj_tag(v_a_3872_) == 0)
{
lean_object* v___x_3874_; 
lean_dec_ref(v___x_3869_);
v___x_3874_ = lean_array_to_list(v_a_3873_);
return v___x_3874_;
}
else
{
lean_object* v_ematch_3875_; lean_object* v_head_3876_; lean_object* v_tail_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3930_; 
v_ematch_3875_ = lean_ctor_get(v___x_3869_, 13);
lean_inc_ref(v_ematch_3875_);
v_head_3876_ = lean_ctor_get(v_a_3872_, 0);
v_tail_3877_ = lean_ctor_get(v_a_3872_, 1);
v_isSharedCheck_3930_ = !lean_is_exclusive(v_a_3872_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3879_ = v_a_3872_;
v_isShared_3880_ = v_isSharedCheck_3930_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_tail_3877_);
lean_inc(v_head_3876_);
lean_dec(v_a_3872_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3930_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v_nextDeclIdx_3881_; lean_object* v_enodeMap_3882_; lean_object* v_exprs_3883_; lean_object* v_parents_3884_; lean_object* v_congrTable_3885_; lean_object* v_appMap_3886_; lean_object* v_indicesFound_3887_; lean_object* v_toProcess_3888_; lean_object* v_internalizing_3889_; lean_object* v_nextIdx_3890_; lean_object* v_newRawFacts_3891_; lean_object* v_facts_3892_; lean_object* v_extThms_3893_; lean_object* v_inj_3894_; lean_object* v_split_3895_; lean_object* v_clean_3896_; lean_object* v_sstates_3897_; lean_object* v_goalStack_3898_; uint64_t v_introBase_3899_; lean_object* v_numIntros_3900_; lean_object* v_thmMap_3901_; lean_object* v_gmt_3902_; lean_object* v_thms_3903_; lean_object* v_newThms_3904_; lean_object* v_numInstances_3905_; lean_object* v_numDelayedInstances_3906_; lean_object* v_preInstances_3907_; lean_object* v_nextThmIdx_3908_; lean_object* v_matchEqNames_3909_; lean_object* v_delayedThmInsts_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3928_; 
v_nextDeclIdx_3881_ = lean_ctor_get(v___x_3869_, 0);
v_enodeMap_3882_ = lean_ctor_get(v___x_3869_, 1);
v_exprs_3883_ = lean_ctor_get(v___x_3869_, 2);
v_parents_3884_ = lean_ctor_get(v___x_3869_, 3);
v_congrTable_3885_ = lean_ctor_get(v___x_3869_, 4);
v_appMap_3886_ = lean_ctor_get(v___x_3869_, 5);
v_indicesFound_3887_ = lean_ctor_get(v___x_3869_, 6);
v_toProcess_3888_ = lean_ctor_get(v___x_3869_, 7);
v_internalizing_3889_ = lean_ctor_get(v___x_3869_, 8);
v_nextIdx_3890_ = lean_ctor_get(v___x_3869_, 9);
v_newRawFacts_3891_ = lean_ctor_get(v___x_3869_, 10);
v_facts_3892_ = lean_ctor_get(v___x_3869_, 11);
v_extThms_3893_ = lean_ctor_get(v___x_3869_, 12);
v_inj_3894_ = lean_ctor_get(v___x_3869_, 14);
v_split_3895_ = lean_ctor_get(v___x_3869_, 15);
v_clean_3896_ = lean_ctor_get(v___x_3869_, 16);
v_sstates_3897_ = lean_ctor_get(v___x_3869_, 17);
v_goalStack_3898_ = lean_ctor_get(v___x_3869_, 18);
v_introBase_3899_ = lean_ctor_get_uint64(v___x_3869_, sizeof(void*)*20);
v_numIntros_3900_ = lean_ctor_get(v___x_3869_, 19);
v_thmMap_3901_ = lean_ctor_get(v_ematch_3875_, 0);
v_gmt_3902_ = lean_ctor_get(v_ematch_3875_, 1);
v_thms_3903_ = lean_ctor_get(v_ematch_3875_, 2);
v_newThms_3904_ = lean_ctor_get(v_ematch_3875_, 3);
v_numInstances_3905_ = lean_ctor_get(v_ematch_3875_, 4);
v_numDelayedInstances_3906_ = lean_ctor_get(v_ematch_3875_, 5);
v_preInstances_3907_ = lean_ctor_get(v_ematch_3875_, 7);
v_nextThmIdx_3908_ = lean_ctor_get(v_ematch_3875_, 8);
v_matchEqNames_3909_ = lean_ctor_get(v_ematch_3875_, 9);
v_delayedThmInsts_3910_ = lean_ctor_get(v_ematch_3875_, 10);
v_isSharedCheck_3928_ = !lean_is_exclusive(v_ematch_3875_);
if (v_isSharedCheck_3928_ == 0)
{
lean_object* v_unused_3929_; 
v_unused_3929_ = lean_ctor_get(v_ematch_3875_, 6);
lean_dec(v_unused_3929_);
v___x_3912_ = v_ematch_3875_;
v_isShared_3913_ = v_isSharedCheck_3928_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_delayedThmInsts_3910_);
lean_inc(v_matchEqNames_3909_);
lean_inc(v_nextThmIdx_3908_);
lean_inc(v_preInstances_3907_);
lean_inc(v_numDelayedInstances_3906_);
lean_inc(v_numInstances_3905_);
lean_inc(v_newThms_3904_);
lean_inc(v_thms_3903_);
lean_inc(v_gmt_3902_);
lean_inc(v_thmMap_3901_);
lean_dec(v_ematch_3875_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3928_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3917_; 
v___x_3914_ = lean_array_get_size(v_a_3873_);
v___x_3915_ = lean_unsigned_to_nat(0u);
if (v_isShared_3913_ == 0)
{
lean_ctor_set(v___x_3912_, 6, v___x_3915_);
v___x_3917_ = v___x_3912_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_thmMap_3901_);
lean_ctor_set(v_reuseFailAlloc_3927_, 1, v_gmt_3902_);
lean_ctor_set(v_reuseFailAlloc_3927_, 2, v_thms_3903_);
lean_ctor_set(v_reuseFailAlloc_3927_, 3, v_newThms_3904_);
lean_ctor_set(v_reuseFailAlloc_3927_, 4, v_numInstances_3905_);
lean_ctor_set(v_reuseFailAlloc_3927_, 5, v_numDelayedInstances_3906_);
lean_ctor_set(v_reuseFailAlloc_3927_, 6, v___x_3915_);
lean_ctor_set(v_reuseFailAlloc_3927_, 7, v_preInstances_3907_);
lean_ctor_set(v_reuseFailAlloc_3927_, 8, v_nextThmIdx_3908_);
lean_ctor_set(v_reuseFailAlloc_3927_, 9, v_matchEqNames_3909_);
lean_ctor_set(v_reuseFailAlloc_3927_, 10, v_delayedThmInsts_3910_);
v___x_3917_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
lean_object* v___x_3918_; lean_object* v___x_3920_; 
lean_inc(v_numIntros_3900_);
lean_inc_ref(v_goalStack_3898_);
lean_inc_ref(v_sstates_3897_);
lean_inc_ref(v_clean_3896_);
lean_inc_ref(v_split_3895_);
lean_inc_ref(v_inj_3894_);
lean_inc_ref(v_extThms_3893_);
lean_inc_ref(v_facts_3892_);
lean_inc_ref(v_newRawFacts_3891_);
lean_inc(v_nextIdx_3890_);
lean_inc_ref(v_internalizing_3889_);
lean_inc_ref(v_toProcess_3888_);
lean_inc_ref(v_indicesFound_3887_);
lean_inc_ref(v_appMap_3886_);
lean_inc_ref(v_congrTable_3885_);
lean_inc_ref(v_parents_3884_);
lean_inc_ref(v_exprs_3883_);
lean_inc_ref(v_enodeMap_3882_);
lean_inc(v_nextDeclIdx_3881_);
v___x_3918_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v___x_3918_, 0, v_nextDeclIdx_3881_);
lean_ctor_set(v___x_3918_, 1, v_enodeMap_3882_);
lean_ctor_set(v___x_3918_, 2, v_exprs_3883_);
lean_ctor_set(v___x_3918_, 3, v_parents_3884_);
lean_ctor_set(v___x_3918_, 4, v_congrTable_3885_);
lean_ctor_set(v___x_3918_, 5, v_appMap_3886_);
lean_ctor_set(v___x_3918_, 6, v_indicesFound_3887_);
lean_ctor_set(v___x_3918_, 7, v_toProcess_3888_);
lean_ctor_set(v___x_3918_, 8, v_internalizing_3889_);
lean_ctor_set(v___x_3918_, 9, v_nextIdx_3890_);
lean_ctor_set(v___x_3918_, 10, v_newRawFacts_3891_);
lean_ctor_set(v___x_3918_, 11, v_facts_3892_);
lean_ctor_set(v___x_3918_, 12, v_extThms_3893_);
lean_ctor_set(v___x_3918_, 13, v___x_3917_);
lean_ctor_set(v___x_3918_, 14, v_inj_3894_);
lean_ctor_set(v___x_3918_, 15, v_split_3895_);
lean_ctor_set(v___x_3918_, 16, v_clean_3896_);
lean_ctor_set(v___x_3918_, 17, v_sstates_3897_);
lean_ctor_set(v___x_3918_, 18, v_goalStack_3898_);
lean_ctor_set(v___x_3918_, 19, v_numIntros_3900_);
lean_ctor_set_uint8(v___x_3918_, sizeof(void*)*20 + 8, v___x_3870_);
lean_ctor_set_uint64(v___x_3918_, sizeof(void*)*20, v_introBase_3899_);
if (v_isShared_3880_ == 0)
{
lean_ctor_set_tag(v___x_3879_, 0);
lean_ctor_set(v___x_3879_, 1, v_head_3876_);
lean_ctor_set(v___x_3879_, 0, v___x_3918_);
v___x_3920_ = v___x_3879_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3918_);
lean_ctor_set(v_reuseFailAlloc_3926_, 1, v_head_3876_);
v___x_3920_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
uint64_t v___x_3921_; uint64_t v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3921_ = lean_uint64_of_nat(v___x_3914_);
v___x_3922_ = lean_uint64_mix_hash(v_a_3871_, v___x_3921_);
v___x_3923_ = l_Lean_Meta_Grind_Goal_setIntroBase(v___x_3920_, v___x_3922_);
v___x_3924_ = lean_array_push(v_a_3873_, v___x_3923_);
v_a_3872_ = v_tail_3877_;
v_a_3873_ = v___x_3924_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0___boxed(lean_object* v___x_3931_, lean_object* v___x_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_){
_start:
{
uint8_t v___x_45632__boxed_3936_; uint64_t v_a_45633__boxed_3937_; lean_object* v_res_3938_; 
v___x_45632__boxed_3936_ = lean_unbox(v___x_3932_);
v_a_45633__boxed_3937_ = lean_unbox_uint64(v_a_3933_);
lean_dec_ref(v_a_3933_);
v_res_3938_ = l_List_mapIdx_go___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v___x_3931_, v___x_45632__boxed_3936_, v_a_45633__boxed_3937_, v_a_3934_, v_a_3935_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1(lean_object* v_fvarId_3943_, lean_object* v_kp_3944_, lean_object* v_goal_3945_, lean_object* v_toGoalState_3946_, lean_object* v_mvarId_3947_, lean_object* v___f_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v_goal_3960_; lean_object* v_toGoalState_3961_; lean_object* v_mvarId_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___x_4047_; 
lean_inc(v_fvarId_3943_);
v___x_4047_ = l_Lean_FVarId_getType___redArg(v_fvarId_3943_, v___y_3954_, v___y_3956_, v___y_3957_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v_a_4048_; lean_object* v___x_4049_; 
v_a_4048_ = lean_ctor_get(v___x_4047_, 0);
lean_inc(v_a_4048_);
lean_dec_ref_known(v___x_4047_, 1);
lean_inc(v___y_3957_);
lean_inc_ref(v___y_3956_);
lean_inc(v___y_3955_);
lean_inc_ref(v___y_3954_);
v___x_4049_ = lean_whnf(v_a_4048_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4152_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4052_ = v___x_4049_;
v_isShared_4053_ = v_isSharedCheck_4152_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v___x_4049_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4152_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___x_4103_; 
v___x_4103_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_a_4050_, v___y_3950_);
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4143_; 
v_a_4104_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4106_ = v___x_4103_;
v_isShared_4107_ = v_isSharedCheck_4143_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4103_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4143_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
uint8_t v___x_4108_; 
v___x_4108_ = lean_unbox(v_a_4104_);
lean_dec(v_a_4104_);
if (v___x_4108_ == 0)
{
lean_object* v___x_4109_; lean_object* v___x_4111_; 
lean_del_object(v___x_4052_);
lean_dec(v_a_4050_);
lean_dec_ref(v___f_3948_);
lean_dec(v_mvarId_3947_);
lean_dec_ref(v_toGoalState_3946_);
lean_dec_ref(v_goal_3945_);
lean_dec_ref(v_kp_3944_);
lean_dec(v_fvarId_3943_);
v___x_4109_ = lean_box(0);
if (v_isShared_4107_ == 0)
{
lean_ctor_set(v___x_4106_, 0, v___x_4109_);
v___x_4111_ = v___x_4106_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v___x_4109_);
v___x_4111_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
return v___x_4111_;
}
}
else
{
lean_object* v___x_4113_; 
lean_del_object(v___x_4106_);
v___x_4113_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_3950_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_object* v_a_4114_; uint8_t v___x_4115_; 
v_a_4114_ = lean_ctor_get(v___x_4113_, 0);
lean_inc(v_a_4114_);
lean_dec_ref_known(v___x_4113_, 1);
v___x_4115_ = lean_unbox(v_a_4114_);
lean_dec(v_a_4114_);
if (v___x_4115_ == 0)
{
v___y_4055_ = v___y_3949_;
v___y_4056_ = v___y_3950_;
v___y_4057_ = v___y_3951_;
v___y_4058_ = v___y_3952_;
v___y_4059_ = v___y_3953_;
v___y_4060_ = v___y_3954_;
v___y_4061_ = v___y_3955_;
v___y_4062_ = v___y_3956_;
v___y_4063_ = v___y_3957_;
goto v___jp_4054_;
}
else
{
lean_object* v___x_4116_; 
v___x_4116_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_a_4050_, v___y_3956_, v___y_3957_);
if (lean_obj_tag(v___x_4116_) == 0)
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4126_; 
v_a_4117_ = lean_ctor_get(v___x_4116_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4116_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4119_ = v___x_4116_;
v_isShared_4120_ = v_isSharedCheck_4126_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4116_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4126_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
uint8_t v___x_4121_; 
v___x_4121_ = lean_unbox(v_a_4117_);
lean_dec(v_a_4117_);
if (v___x_4121_ == 0)
{
lean_object* v___x_4122_; lean_object* v___x_4124_; 
lean_del_object(v___x_4052_);
lean_dec(v_a_4050_);
lean_dec_ref(v___f_3948_);
lean_dec(v_mvarId_3947_);
lean_dec_ref(v_toGoalState_3946_);
lean_dec_ref(v_goal_3945_);
lean_dec_ref(v_kp_3944_);
lean_dec(v_fvarId_3943_);
v___x_4122_ = lean_box(0);
if (v_isShared_4120_ == 0)
{
lean_ctor_set(v___x_4119_, 0, v___x_4122_);
v___x_4124_ = v___x_4119_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v___x_4122_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
else
{
lean_del_object(v___x_4119_);
v___y_4055_ = v___y_3949_;
v___y_4056_ = v___y_3950_;
v___y_4057_ = v___y_3951_;
v___y_4058_ = v___y_3952_;
v___y_4059_ = v___y_3953_;
v___y_4060_ = v___y_3954_;
v___y_4061_ = v___y_3955_;
v___y_4062_ = v___y_3956_;
v___y_4063_ = v___y_3957_;
goto v___jp_4054_;
}
}
}
else
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4134_; 
lean_del_object(v___x_4052_);
lean_dec(v_a_4050_);
lean_dec_ref(v___f_3948_);
lean_dec(v_mvarId_3947_);
lean_dec_ref(v_toGoalState_3946_);
lean_dec_ref(v_goal_3945_);
lean_dec_ref(v_kp_3944_);
lean_dec(v_fvarId_3943_);
v_a_4127_ = lean_ctor_get(v___x_4116_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4116_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4129_ = v___x_4116_;
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_4116_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4132_; 
if (v_isShared_4130_ == 0)
{
v___x_4132_ = v___x_4129_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4127_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
}
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
lean_del_object(v___x_4052_);
lean_dec(v_a_4050_);
lean_dec_ref(v___f_3948_);
lean_dec(v_mvarId_3947_);
lean_dec_ref(v_toGoalState_3946_);
lean_dec_ref(v_goal_3945_);
lean_dec_ref(v_kp_3944_);
lean_dec(v_fvarId_3943_);
v_a_4135_ = lean_ctor_get(v___x_4113_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4137_ = v___x_4113_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4113_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_a_4135_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
}
}
else
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4151_; 
lean_del_object(v___x_4052_);
lean_dec(v_a_4050_);
lean_dec_ref(v___f_3948_);
lean_dec(v_mvarId_3947_);
lean_dec_ref(v_toGoalState_3946_);
lean_dec_ref(v_goal_3945_);
lean_dec_ref(v_kp_3944_);
lean_dec(v_fvarId_3943_);
v_a_4144_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4151_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4146_ = v___x_4103_;
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___x_4103_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4149_; 
if (v_isShared_4147_ == 0)
{
v___x_4149_ = v___x_4146_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v_a_4144_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
return v___x_4149_;
}
}
}
v___jp_4054_:
{
lean_object* v___x_4064_; 
v___x_4064_ = l_Lean_Expr_getAppFn(v_a_4050_);
if (lean_obj_tag(v___x_4064_) == 4)
{
lean_object* v_declName_4065_; lean_object* v___x_4066_; 
lean_del_object(v___x_4052_);
v_declName_4065_ = lean_ctor_get(v___x_4064_, 0);
lean_inc_n(v_declName_4065_, 2);
lean_dec_ref_known(v___x_4064_, 2);
v___x_4066_ = l_Lean_Meta_Grind_saveCases___redArg(v_declName_4065_, v___y_4057_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v___x_4067_; 
lean_dec_ref_known(v___x_4066_, 1);
v___x_4067_ = l_Lean_Meta_isProp(v_a_4050_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
if (lean_obj_tag(v___x_4067_) == 0)
{
lean_object* v_a_4068_; uint8_t v___x_4069_; 
v_a_4068_ = lean_ctor_get(v___x_4067_, 0);
lean_inc(v_a_4068_);
lean_dec_ref_known(v___x_4067_, 1);
v___x_4069_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_4065_);
lean_dec(v_declName_4065_);
if (v___x_4069_ == 0)
{
uint8_t v___x_4070_; 
v___x_4070_ = lean_unbox(v_a_4068_);
lean_dec(v_a_4068_);
if (v___x_4070_ == 0)
{
lean_dec_ref(v___f_3948_);
v_goal_3960_ = v_goal_3945_;
v_toGoalState_3961_ = v_toGoalState_3946_;
v_mvarId_3962_ = v_mvarId_3947_;
v___y_3963_ = v___y_4055_;
v___y_3964_ = v___y_4056_;
v___y_3965_ = v___y_4057_;
v___y_3966_ = v___y_4058_;
v___y_3967_ = v___y_4059_;
v___y_3968_ = v___y_4060_;
v___y_3969_ = v___y_4061_;
v___y_3970_ = v___y_4062_;
v___y_3971_ = v___y_4063_;
goto v___jp_3959_;
}
else
{
lean_object* v___x_4071_; 
lean_dec_ref(v_toGoalState_3946_);
lean_dec_ref(v_goal_3945_);
v___x_4071_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_3947_, v___f_3948_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v_a_4072_; lean_object* v_toGoalState_4073_; lean_object* v_mvarId_4074_; 
v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
lean_inc(v_a_4072_);
lean_dec_ref_known(v___x_4071_, 1);
v_toGoalState_4073_ = lean_ctor_get(v_a_4072_, 0);
lean_inc_ref(v_toGoalState_4073_);
v_mvarId_4074_ = lean_ctor_get(v_a_4072_, 1);
lean_inc(v_mvarId_4074_);
v_goal_3960_ = v_a_4072_;
v_toGoalState_3961_ = v_toGoalState_4073_;
v_mvarId_3962_ = v_mvarId_4074_;
v___y_3963_ = v___y_4055_;
v___y_3964_ = v___y_4056_;
v___y_3965_ = v___y_4057_;
v___y_3966_ = v___y_4058_;
v___y_3967_ = v___y_4059_;
v___y_3968_ = v___y_4060_;
v___y_3969_ = v___y_4061_;
v___y_3970_ = v___y_4062_;
v___y_3971_ = v___y_4063_;
goto v___jp_3959_;
}
else
{
lean_object* v_a_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4082_; 
lean_dec_ref(v_kp_3944_);
lean_dec(v_fvarId_3943_);
v_a_4075_ = lean_ctor_get(v___x_4071_, 0);
v_isSharedCheck_4082_ = !lean_is_exclusive(v___x_4071_);
if (v_isSharedCheck_4082_ == 0)
{
v___x_4077_ = v___x_4071_;
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_a_4075_);
lean_dec(v___x_4071_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v___x_4080_; 
if (v_isShared_4078_ == 0)
{
v___x_4080_ = v___x_4077_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_a_4075_);
v___x_4080_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
return v___x_4080_;
}
}
}
}
}
else
{
lean_dec(v_a_4068_);
lean_dec_ref(v___f_3948_);
v_goal_3960_ = v_goal_3945_;
v_toGoalState_3961_ = v_toGoalState_3946_;
v_mvarId_3962_ = v_mvarId_3947_;
v___y_3963_ = v___y_4055_;
v___y_3964_ = v___y_4056_;
v___y_3965_ = v___y_4057_;
v___y_3966_ = v___y_4058_;
v___y_3967_ = v___y_4059_;
v___y_3968_ = v___y_4060_;
v___y_3969_ = v___y_4061_;
v___y_3970_ = v___y_4062_;
v___y_3971_ = v___y_4063_;
goto v___jp_3959_;
}
}
else
{
lean_object* v_a_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4090_; 
lean_dec(v_declName_4065_);
lean_dec_ref(v___f_3948_);
lean_dec(v_mvarId_3947_);
lean_dec_ref(v_toGoalState_3946_);
lean_dec_ref(v_goal_3945_);
lean_dec_ref(v_kp_3944_);
lean_dec(v_fvarId_3943_);
v_a_4083_ = lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_4085_ = v___x_4067_;
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_a_4083_);
lean_dec(v___x_4067_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4088_; 
if (v_isShared_4086_ == 0)
{
v___x_4088_ = v___x_4085_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4083_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
}
}
else
{
lean_object* v_a_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4098_; 
lean_dec(v_declName_4065_);
lean_dec(v_a_4050_);
lean_dec_ref(v___f_3948_);
lean_dec(v_mvarId_3947_);
lean_dec_ref(v_toGoalState_3946_);
lean_dec_ref(v_goal_3945_);
lean_dec_ref(v_kp_3944_);
lean_dec(v_fvarId_3943_);
v_a_4091_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4093_ = v___x_4066_;
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_a_4091_);
lean_dec(v___x_4066_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v___x_4096_; 
if (v_isShared_4094_ == 0)
{
v___x_4096_ = v___x_4093_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4091_);
v___x_4096_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
return v___x_4096_;
}
}
}
}
else
{
lean_object* v___x_4099_; lean_object* v___x_4101_; 
lean_dec_ref(v___x_4064_);
lean_dec(v_a_4050_);
lean_dec_ref(v___f_3948_);
lean_dec(v_mvarId_3947_);
lean_dec_ref(v_toGoalState_3946_);
lean_dec_ref(v_goal_3945_);
lean_dec_ref(v_kp_3944_);
lean_dec(v_fvarId_3943_);
v___x_4099_ = lean_box(0);
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 0, v___x_4099_);
v___x_4101_ = v___x_4052_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v___x_4099_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
}
}
}
else
{
lean_object* v_a_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4160_; 
lean_dec_ref(v___f_3948_);
lean_dec(v_mvarId_3947_);
lean_dec_ref(v_toGoalState_3946_);
lean_dec_ref(v_goal_3945_);
lean_dec_ref(v_kp_3944_);
lean_dec(v_fvarId_3943_);
v_a_4153_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4155_ = v___x_4049_;
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_a_4153_);
lean_dec(v___x_4049_);
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
else
{
lean_object* v_a_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4168_; 
lean_dec_ref(v___f_3948_);
lean_dec(v_mvarId_3947_);
lean_dec_ref(v_toGoalState_3946_);
lean_dec_ref(v_goal_3945_);
lean_dec_ref(v_kp_3944_);
lean_dec(v_fvarId_3943_);
v_a_4161_ = lean_ctor_get(v___x_4047_, 0);
v_isSharedCheck_4168_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4168_ == 0)
{
v___x_4163_ = v___x_4047_;
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_a_4161_);
lean_dec(v___x_4047_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4166_; 
if (v_isShared_4164_ == 0)
{
v___x_4166_ = v___x_4163_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4161_);
v___x_4166_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
return v___x_4166_;
}
}
}
v___jp_3959_:
{
uint8_t v_inconsistent_3972_; 
v_inconsistent_3972_ = lean_ctor_get_uint8(v_toGoalState_3961_, sizeof(void*)*20 + 8);
if (v_inconsistent_3972_ == 0)
{
lean_object* v___x_3973_; lean_object* v___x_3974_; 
lean_dec_ref(v_goal_3960_);
v___x_3973_ = l_Lean_mkFVar(v_fvarId_3943_);
lean_inc_ref(v___x_3973_);
v___x_3974_ = l_Lean_Meta_Grind_cases(v_mvarId_3962_, v___x_3973_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_);
if (lean_obj_tag(v___x_3974_) == 0)
{
lean_object* v_a_3975_; lean_object* v___x_3976_; 
v_a_3975_ = lean_ctor_get(v___x_3974_, 0);
lean_inc(v_a_3975_);
lean_dec_ref_known(v___x_3974_, 1);
v___x_3976_ = l_Lean_Meta_Grind_getAnchor(v___x_3973_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; uint64_t v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_a_3977_);
lean_dec_ref_known(v___x_3976_, 1);
v___x_3978_ = lean_unsigned_to_nat(0u);
v___x_3979_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1___closed__0));
v___x_3980_ = lean_unbox_uint64(v_a_3977_);
lean_dec(v_a_3977_);
v___x_3981_ = l_List_mapIdx_go___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v_toGoalState_3961_, v_inconsistent_3972_, v___x_3980_, v_a_3975_, v___x_3979_);
v___x_3982_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1___closed__1));
v___x_3983_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_3944_, v___x_3981_, v___x_3982_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_);
lean_dec(v___x_3981_);
if (lean_obj_tag(v___x_3983_) == 0)
{
lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_4004_; 
v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3986_ = v___x_3983_;
v_isShared_3987_ = v_isSharedCheck_4004_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___x_3983_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_4004_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v_fst_3988_; lean_object* v_snd_3989_; lean_object* v___x_3990_; uint8_t v___x_3991_; 
v_fst_3988_ = lean_ctor_get(v_a_3984_, 0);
lean_inc(v_fst_3988_);
v_snd_3989_ = lean_ctor_get(v_a_3984_, 1);
lean_inc(v_snd_3989_);
lean_dec(v_a_3984_);
v___x_3990_ = lean_array_get_size(v_snd_3989_);
v___x_3991_ = lean_nat_dec_eq(v___x_3990_, v___x_3978_);
if (v___x_3991_ == 0)
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3996_; 
lean_dec(v_fst_3988_);
v___x_3992_ = lean_array_to_list(v_snd_3989_);
v___x_3993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3992_);
v___x_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3993_);
if (v_isShared_3987_ == 0)
{
lean_ctor_set(v___x_3986_, 0, v___x_3994_);
v___x_3996_ = v___x_3986_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v___x_3994_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
return v___x_3996_;
}
}
else
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4002_; 
lean_dec(v_snd_3989_);
v___x_3998_ = lean_array_to_list(v_fst_3988_);
v___x_3999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3998_);
v___x_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3999_);
if (v_isShared_3987_ == 0)
{
lean_ctor_set(v___x_3986_, 0, v___x_4000_);
v___x_4002_ = v___x_3986_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v___x_4000_);
v___x_4002_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
return v___x_4002_;
}
}
}
}
else
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4012_; 
v_a_4005_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4007_ = v___x_3983_;
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_3983_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4010_; 
if (v_isShared_4008_ == 0)
{
v___x_4010_ = v___x_4007_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4005_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
}
else
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4020_; 
lean_dec(v_a_3975_);
lean_dec_ref(v_toGoalState_3961_);
lean_dec_ref(v_kp_3944_);
v_a_4013_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4015_ = v___x_3976_;
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_3976_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4018_; 
if (v_isShared_4016_ == 0)
{
v___x_4018_ = v___x_4015_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
}
else
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4028_; 
lean_dec_ref(v___x_3973_);
lean_dec_ref(v_toGoalState_3961_);
lean_dec_ref(v_kp_3944_);
v_a_4021_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4023_ = v___x_3974_;
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___x_3974_);
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
else
{
lean_object* v___x_4029_; 
lean_dec(v_mvarId_3962_);
lean_dec_ref(v_toGoalState_3961_);
lean_dec(v_fvarId_3943_);
lean_inc(v___y_3971_);
lean_inc_ref(v___y_3970_);
lean_inc(v___y_3969_);
lean_inc_ref(v___y_3968_);
lean_inc(v___y_3967_);
lean_inc_ref(v___y_3966_);
lean_inc(v___y_3965_);
lean_inc_ref(v___y_3964_);
lean_inc(v___y_3963_);
v___x_4029_ = lean_apply_11(v_kp_3944_, v_goal_3960_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, lean_box(0));
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4038_; 
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4038_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4032_ = v___x_4029_;
v_isShared_4033_ = v_isSharedCheck_4038_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_4029_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4038_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4034_; lean_object* v___x_4036_; 
v___x_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4034_, 0, v_a_4030_);
if (v_isShared_4033_ == 0)
{
lean_ctor_set(v___x_4032_, 0, v___x_4034_);
v___x_4036_ = v___x_4032_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v___x_4034_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
return v___x_4036_;
}
}
}
else
{
lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4046_; 
v_a_4039_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4041_ = v___x_4029_;
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_dec(v___x_4029_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1___boxed(lean_object* v_fvarId_4169_, lean_object* v_kp_4170_, lean_object* v_goal_4171_, lean_object* v_toGoalState_4172_, lean_object* v_mvarId_4173_, lean_object* v___f_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_){
_start:
{
lean_object* v_res_4185_; 
v_res_4185_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1(v_fvarId_4169_, v_kp_4170_, v_goal_4171_, v_toGoalState_4172_, v_mvarId_4173_, v___f_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
lean_dec(v___y_4175_);
return v_res_4185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(lean_object* v_goal_4186_, lean_object* v_fvarId_4187_, lean_object* v_generation_4188_, lean_object* v_kp_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_){
_start:
{
lean_object* v_toGoalState_4200_; lean_object* v_mvarId_4201_; lean_object* v___f_4202_; lean_object* v___f_4203_; lean_object* v___x_4204_; 
v_toGoalState_4200_ = lean_ctor_get(v_goal_4186_, 0);
lean_inc_ref(v_toGoalState_4200_);
v_mvarId_4201_ = lean_ctor_get(v_goal_4186_, 1);
lean_inc_n(v_mvarId_4201_, 2);
lean_inc(v_fvarId_4187_);
lean_inc_ref(v_goal_4186_);
v___f_4202_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed), 13, 3);
lean_closure_set(v___f_4202_, 0, v_goal_4186_);
lean_closure_set(v___f_4202_, 1, v_fvarId_4187_);
lean_closure_set(v___f_4202_, 2, v_generation_4188_);
v___f_4203_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__1___boxed), 16, 6);
lean_closure_set(v___f_4203_, 0, v_fvarId_4187_);
lean_closure_set(v___f_4203_, 1, v_kp_4189_);
lean_closure_set(v___f_4203_, 2, v_goal_4186_);
lean_closure_set(v___f_4203_, 3, v_toGoalState_4200_);
lean_closure_set(v___f_4203_, 4, v_mvarId_4201_);
lean_closure_set(v___f_4203_, 5, v___f_4202_);
v___x_4204_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_4201_, v___f_4203_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_);
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___boxed(lean_object* v_goal_4205_, lean_object* v_fvarId_4206_, lean_object* v_generation_4207_, lean_object* v_kp_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_4205_, v_fvarId_4206_, v_generation_4207_, v_kp_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_);
lean_dec(v_a_4217_);
lean_dec_ref(v_a_4216_);
lean_dec(v_a_4215_);
lean_dec_ref(v_a_4214_);
lean_dec(v_a_4213_);
lean_dec_ref(v_a_4212_);
lean_dec(v_a_4211_);
lean_dec_ref(v_a_4210_);
lean_dec(v_a_4209_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(lean_object* v_kp_4220_, lean_object* v_as_4221_, lean_object* v_as_x27_4222_, lean_object* v_b_4223_, lean_object* v_a_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v___x_4235_; 
v___x_4235_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_4220_, v_as_x27_4222_, v_b_4223_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
return v___x_4235_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___boxed(lean_object* v_kp_4236_, lean_object* v_as_4237_, lean_object* v_as_x27_4238_, lean_object* v_b_4239_, lean_object* v_a_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_){
_start:
{
lean_object* v_res_4251_; 
v_res_4251_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(v_kp_4236_, v_as_4237_, v_as_x27_4238_, v_b_4239_, v_a_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_);
lean_dec(v___y_4249_);
lean_dec_ref(v___y_4248_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec(v___y_4241_);
lean_dec(v_as_x27_4238_);
lean_dec(v_as_4237_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0(lean_object* v_goal_4252_, lean_object* v_fvarId_4253_, lean_object* v_generation_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
lean_object* v___x_4265_; lean_object* v___x_4266_; 
v___x_4265_ = lean_st_mk_ref(v_goal_4252_);
v___x_4266_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_4253_, v_generation_4254_, v___x_4265_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_);
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4275_; 
v_isSharedCheck_4275_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4275_ == 0)
{
lean_object* v_unused_4276_; 
v_unused_4276_ = lean_ctor_get(v___x_4266_, 0);
lean_dec(v_unused_4276_);
v___x_4268_ = v___x_4266_;
v_isShared_4269_ = v_isSharedCheck_4275_;
goto v_resetjp_4267_;
}
else
{
lean_dec(v___x_4266_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4275_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4273_; 
v___x_4270_ = lean_st_ref_get(v___x_4265_);
v___x_4271_ = lean_st_ref_get(v___x_4265_);
lean_dec(v___x_4265_);
lean_dec(v___x_4271_);
if (v_isShared_4269_ == 0)
{
lean_ctor_set(v___x_4268_, 0, v___x_4270_);
v___x_4273_ = v___x_4268_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v___x_4270_);
v___x_4273_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
return v___x_4273_;
}
}
}
else
{
lean_object* v_a_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4284_; 
lean_dec(v___x_4265_);
v_a_4277_ = lean_ctor_get(v___x_4266_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4279_ = v___x_4266_;
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_a_4277_);
lean_dec(v___x_4266_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v___x_4282_; 
if (v_isShared_4280_ == 0)
{
v___x_4282_ = v___x_4279_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v_a_4277_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___lam__0___boxed(lean_object* v_goal_4285_, lean_object* v_fvarId_4286_, lean_object* v_generation_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_){
_start:
{
lean_object* v_res_4298_; 
v_res_4298_ = l_Lean_Meta_Grind_Action_intro___lam__0(v_goal_4285_, v_fvarId_4286_, v_generation_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec(v___y_4288_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro(lean_object* v_generation_4301_, lean_object* v_goal_4302_, lean_object* v_kna_4303_, lean_object* v_kp_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_){
_start:
{
lean_object* v_toGoalState_4315_; uint8_t v_inconsistent_4316_; 
v_toGoalState_4315_ = lean_ctor_get(v_goal_4302_, 0);
v_inconsistent_4316_ = lean_ctor_get_uint8(v_toGoalState_4315_, sizeof(void*)*20 + 8);
if (v_inconsistent_4316_ == 0)
{
lean_object* v_mvarId_4317_; lean_object* v___x_4318_; 
v_mvarId_4317_ = lean_ctor_get(v_goal_4302_, 1);
lean_inc(v_mvarId_4317_);
v___x_4318_ = l_Lean_MVarId_getType(v_mvarId_4317_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_);
if (lean_obj_tag(v___x_4318_) == 0)
{
lean_object* v_a_4319_; uint8_t v___x_4320_; 
v_a_4319_ = lean_ctor_get(v___x_4318_, 0);
lean_inc(v_a_4319_);
lean_dec_ref_known(v___x_4318_, 1);
v___x_4320_ = l_Lean_Expr_isFalse(v_a_4319_);
lean_dec(v_a_4319_);
if (v___x_4320_ == 0)
{
lean_object* v___x_4321_; 
lean_dec_ref(v_kna_4303_);
lean_inc(v_generation_4301_);
v___x_4321_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_4302_, v_generation_4301_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_);
if (lean_obj_tag(v___x_4321_) == 0)
{
lean_object* v_a_4322_; 
v_a_4322_ = lean_ctor_get(v___x_4321_, 0);
lean_inc(v_a_4322_);
lean_dec_ref_known(v___x_4321_, 1);
switch(lean_obj_tag(v_a_4322_))
{
case 0:
{
lean_object* v_goal_4323_; lean_object* v___x_4324_; 
lean_dec(v_generation_4301_);
v_goal_4323_ = lean_ctor_get(v_a_4322_, 0);
lean_inc_ref(v_goal_4323_);
lean_dec_ref_known(v_a_4322_, 1);
v___x_4324_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_4323_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_);
if (lean_obj_tag(v___x_4324_) == 0)
{
lean_object* v_a_4325_; lean_object* v___x_4326_; 
v_a_4325_ = lean_ctor_get(v___x_4324_, 0);
lean_inc(v_a_4325_);
lean_dec_ref_known(v___x_4324_, 1);
v___x_4326_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_simpTarget(v_a_4325_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_);
if (lean_obj_tag(v___x_4326_) == 0)
{
lean_object* v_a_4327_; lean_object* v_toGoalState_4328_; lean_object* v_mvarId_4329_; lean_object* v___x_4330_; 
v_a_4327_ = lean_ctor_get(v___x_4326_, 0);
lean_inc(v_a_4327_);
lean_dec_ref_known(v___x_4326_, 1);
v_toGoalState_4328_ = lean_ctor_get(v_a_4327_, 0);
v_mvarId_4329_ = lean_ctor_get(v_a_4327_, 1);
lean_inc(v_mvarId_4329_);
v___x_4330_ = l_Lean_MVarId_getType(v_mvarId_4329_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_);
if (lean_obj_tag(v___x_4330_) == 0)
{
lean_object* v_a_4331_; uint8_t v___x_4332_; 
v_a_4331_ = lean_ctor_get(v___x_4330_, 0);
lean_inc(v_a_4331_);
lean_dec_ref_known(v___x_4330_, 1);
v___x_4332_ = l_Lean_Expr_isForall(v_a_4331_);
if (v___x_4332_ == 0)
{
uint8_t v___x_4333_; 
v___x_4333_ = l_Lean_Expr_isLet(v_a_4331_);
lean_dec(v_a_4331_);
if (v___x_4333_ == 0)
{
lean_object* v___x_4334_; 
lean_inc(v_mvarId_4329_);
v___x_4334_ = l_Lean_MVarId_byContra_x3f(v_mvarId_4329_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_);
if (lean_obj_tag(v___x_4334_) == 0)
{
lean_object* v_a_4335_; 
v_a_4335_ = lean_ctor_get(v___x_4334_, 0);
lean_inc(v_a_4335_);
lean_dec_ref_known(v___x_4334_, 1);
if (lean_obj_tag(v_a_4335_) == 1)
{
lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4344_; 
lean_inc_ref(v_toGoalState_4328_);
v_isSharedCheck_4344_ = !lean_is_exclusive(v_a_4327_);
if (v_isSharedCheck_4344_ == 0)
{
lean_object* v_unused_4345_; lean_object* v_unused_4346_; 
v_unused_4345_ = lean_ctor_get(v_a_4327_, 1);
lean_dec(v_unused_4345_);
v_unused_4346_ = lean_ctor_get(v_a_4327_, 0);
lean_dec(v_unused_4346_);
v___x_4337_ = v_a_4327_;
v_isShared_4338_ = v_isSharedCheck_4344_;
goto v_resetjp_4336_;
}
else
{
lean_dec(v_a_4327_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4344_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v_val_4339_; lean_object* v___x_4341_; 
v_val_4339_ = lean_ctor_get(v_a_4335_, 0);
lean_inc(v_val_4339_);
lean_dec_ref_known(v_a_4335_, 1);
if (v_isShared_4338_ == 0)
{
lean_ctor_set(v___x_4337_, 1, v_val_4339_);
v___x_4341_ = v___x_4337_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_toGoalState_4328_);
lean_ctor_set(v_reuseFailAlloc_4343_, 1, v_val_4339_);
v___x_4341_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
lean_object* v___x_4342_; 
lean_inc(v_a_4313_);
lean_inc_ref(v_a_4312_);
lean_inc(v_a_4311_);
lean_inc_ref(v_a_4310_);
lean_inc(v_a_4309_);
lean_inc_ref(v_a_4308_);
lean_inc(v_a_4307_);
lean_inc_ref(v_a_4306_);
lean_inc(v_a_4305_);
v___x_4342_ = lean_apply_11(v_kp_4304_, v___x_4341_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, lean_box(0));
return v___x_4342_;
}
}
}
else
{
lean_object* v___x_4347_; 
lean_dec(v_a_4335_);
lean_inc(v_a_4313_);
lean_inc_ref(v_a_4312_);
lean_inc(v_a_4311_);
lean_inc_ref(v_a_4310_);
lean_inc(v_a_4309_);
lean_inc_ref(v_a_4308_);
lean_inc(v_a_4307_);
lean_inc_ref(v_a_4306_);
lean_inc(v_a_4305_);
v___x_4347_ = lean_apply_11(v_kp_4304_, v_a_4327_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, lean_box(0));
return v___x_4347_;
}
}
else
{
lean_object* v_a_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4355_; 
lean_dec(v_a_4327_);
lean_dec_ref(v_kp_4304_);
v_a_4348_ = lean_ctor_get(v___x_4334_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4334_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4350_ = v___x_4334_;
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_a_4348_);
lean_dec(v___x_4334_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4353_; 
if (v_isShared_4351_ == 0)
{
v___x_4353_ = v___x_4350_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4348_);
v___x_4353_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
return v___x_4353_;
}
}
}
}
else
{
lean_object* v___x_4356_; 
lean_inc(v_a_4313_);
lean_inc_ref(v_a_4312_);
lean_inc(v_a_4311_);
lean_inc_ref(v_a_4310_);
lean_inc(v_a_4309_);
lean_inc_ref(v_a_4308_);
lean_inc(v_a_4307_);
lean_inc_ref(v_a_4306_);
lean_inc(v_a_4305_);
v___x_4356_ = lean_apply_11(v_kp_4304_, v_a_4327_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, lean_box(0));
return v___x_4356_;
}
}
else
{
lean_object* v___x_4357_; 
lean_dec(v_a_4331_);
lean_inc(v_a_4313_);
lean_inc_ref(v_a_4312_);
lean_inc(v_a_4311_);
lean_inc_ref(v_a_4310_);
lean_inc(v_a_4309_);
lean_inc_ref(v_a_4308_);
lean_inc(v_a_4307_);
lean_inc_ref(v_a_4306_);
lean_inc(v_a_4305_);
v___x_4357_ = lean_apply_11(v_kp_4304_, v_a_4327_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, lean_box(0));
return v___x_4357_;
}
}
else
{
lean_object* v_a_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4365_; 
lean_dec(v_a_4327_);
lean_dec_ref(v_kp_4304_);
v_a_4358_ = lean_ctor_get(v___x_4330_, 0);
v_isSharedCheck_4365_ = !lean_is_exclusive(v___x_4330_);
if (v_isSharedCheck_4365_ == 0)
{
v___x_4360_ = v___x_4330_;
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_a_4358_);
lean_dec(v___x_4330_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v___x_4363_; 
if (v_isShared_4361_ == 0)
{
v___x_4363_ = v___x_4360_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v_a_4358_);
v___x_4363_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
return v___x_4363_;
}
}
}
}
else
{
lean_object* v_a_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4373_; 
lean_dec_ref(v_kp_4304_);
v_a_4366_ = lean_ctor_get(v___x_4326_, 0);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4368_ = v___x_4326_;
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_a_4366_);
lean_dec(v___x_4326_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4371_; 
if (v_isShared_4369_ == 0)
{
v___x_4371_ = v___x_4368_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_a_4366_);
v___x_4371_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
return v___x_4371_;
}
}
}
}
else
{
lean_object* v_a_4374_; lean_object* v___x_4376_; uint8_t v_isShared_4377_; uint8_t v_isSharedCheck_4381_; 
lean_dec_ref(v_kp_4304_);
v_a_4374_ = lean_ctor_get(v___x_4324_, 0);
v_isSharedCheck_4381_ = !lean_is_exclusive(v___x_4324_);
if (v_isSharedCheck_4381_ == 0)
{
v___x_4376_ = v___x_4324_;
v_isShared_4377_ = v_isSharedCheck_4381_;
goto v_resetjp_4375_;
}
else
{
lean_inc(v_a_4374_);
lean_dec(v___x_4324_);
v___x_4376_ = lean_box(0);
v_isShared_4377_ = v_isSharedCheck_4381_;
goto v_resetjp_4375_;
}
v_resetjp_4375_:
{
lean_object* v___x_4379_; 
if (v_isShared_4377_ == 0)
{
v___x_4379_ = v___x_4376_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v_a_4374_);
v___x_4379_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
return v___x_4379_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4382_; lean_object* v_goal_4383_; lean_object* v___f_4384_; lean_object* v___x_4385_; 
v_fvarId_4382_ = lean_ctor_get(v_a_4322_, 0);
lean_inc_n(v_fvarId_4382_, 3);
v_goal_4383_ = lean_ctor_get(v_a_4322_, 1);
lean_inc_ref_n(v_goal_4383_, 3);
lean_dec_ref_known(v_a_4322_, 2);
lean_inc(v_generation_4301_);
v___f_4384_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intro___lam__0___boxed), 13, 3);
lean_closure_set(v___f_4384_, 0, v_goal_4383_);
lean_closure_set(v___f_4384_, 1, v_fvarId_4382_);
lean_closure_set(v___f_4384_, 2, v_generation_4301_);
v___x_4385_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_4383_, v_fvarId_4382_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_);
if (lean_obj_tag(v___x_4385_) == 0)
{
lean_object* v_a_4386_; 
v_a_4386_ = lean_ctor_get(v___x_4385_, 0);
lean_inc(v_a_4386_);
lean_dec_ref_known(v___x_4385_, 1);
if (lean_obj_tag(v_a_4386_) == 1)
{
lean_object* v_val_4387_; lean_object* v___x_4388_; 
lean_dec_ref(v___f_4384_);
lean_dec_ref(v_goal_4383_);
lean_dec(v_fvarId_4382_);
lean_dec(v_generation_4301_);
v_val_4387_ = lean_ctor_get(v_a_4386_, 0);
lean_inc(v_val_4387_);
lean_dec_ref_known(v_a_4386_, 1);
lean_inc(v_a_4313_);
lean_inc_ref(v_a_4312_);
lean_inc(v_a_4311_);
lean_inc_ref(v_a_4310_);
lean_inc(v_a_4309_);
lean_inc_ref(v_a_4308_);
lean_inc(v_a_4307_);
lean_inc_ref(v_a_4306_);
lean_inc(v_a_4305_);
v___x_4388_ = lean_apply_11(v_kp_4304_, v_val_4387_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, lean_box(0));
return v___x_4388_;
}
else
{
lean_object* v___x_4389_; 
lean_dec(v_a_4386_);
lean_inc_ref(v_kp_4304_);
lean_inc_ref(v_goal_4383_);
v___x_4389_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_4383_, v_fvarId_4382_, v_generation_4301_, v_kp_4304_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_);
if (lean_obj_tag(v___x_4389_) == 0)
{
lean_object* v_a_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4410_; 
v_a_4390_ = lean_ctor_get(v___x_4389_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4389_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4392_ = v___x_4389_;
v_isShared_4393_ = v_isSharedCheck_4410_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_a_4390_);
lean_dec(v___x_4389_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4410_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
if (lean_obj_tag(v_a_4390_) == 1)
{
lean_object* v_val_4394_; lean_object* v___x_4396_; 
lean_dec_ref(v___f_4384_);
lean_dec_ref(v_goal_4383_);
lean_dec_ref(v_kp_4304_);
v_val_4394_ = lean_ctor_get(v_a_4390_, 0);
lean_inc(v_val_4394_);
lean_dec_ref_known(v_a_4390_, 1);
if (v_isShared_4393_ == 0)
{
lean_ctor_set(v___x_4392_, 0, v_val_4394_);
v___x_4396_ = v___x_4392_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_val_4394_);
v___x_4396_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
return v___x_4396_;
}
}
else
{
lean_object* v_mvarId_4398_; lean_object* v___x_4399_; 
lean_del_object(v___x_4392_);
lean_dec(v_a_4390_);
v_mvarId_4398_ = lean_ctor_get(v_goal_4383_, 1);
lean_inc(v_mvarId_4398_);
lean_dec_ref(v_goal_4383_);
v___x_4399_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_4398_, v___f_4384_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_);
if (lean_obj_tag(v___x_4399_) == 0)
{
lean_object* v_a_4400_; lean_object* v___x_4401_; 
v_a_4400_ = lean_ctor_get(v___x_4399_, 0);
lean_inc(v_a_4400_);
lean_dec_ref_known(v___x_4399_, 1);
lean_inc(v_a_4313_);
lean_inc_ref(v_a_4312_);
lean_inc(v_a_4311_);
lean_inc_ref(v_a_4310_);
lean_inc(v_a_4309_);
lean_inc_ref(v_a_4308_);
lean_inc(v_a_4307_);
lean_inc_ref(v_a_4306_);
lean_inc(v_a_4305_);
v___x_4401_ = lean_apply_11(v_kp_4304_, v_a_4400_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, lean_box(0));
return v___x_4401_;
}
else
{
lean_object* v_a_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4409_; 
lean_dec_ref(v_kp_4304_);
v_a_4402_ = lean_ctor_get(v___x_4399_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4399_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4404_ = v___x_4399_;
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_a_4402_);
lean_dec(v___x_4399_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4407_; 
if (v_isShared_4405_ == 0)
{
v___x_4407_ = v___x_4404_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_a_4402_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
return v___x_4407_;
}
}
}
}
}
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
lean_dec_ref(v___f_4384_);
lean_dec_ref(v_goal_4383_);
lean_dec_ref(v_kp_4304_);
v_a_4411_ = lean_ctor_get(v___x_4389_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4389_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4389_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4389_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_a_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
}
}
else
{
lean_object* v_a_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4426_; 
lean_dec_ref(v___f_4384_);
lean_dec_ref(v_goal_4383_);
lean_dec(v_fvarId_4382_);
lean_dec_ref(v_kp_4304_);
lean_dec(v_generation_4301_);
v_a_4419_ = lean_ctor_get(v___x_4385_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4421_ = v___x_4385_;
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_a_4419_);
lean_dec(v___x_4385_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___x_4424_; 
if (v_isShared_4422_ == 0)
{
v___x_4424_ = v___x_4421_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_a_4419_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
}
}
case 2:
{
lean_object* v_goal_4427_; lean_object* v___x_4428_; 
lean_dec(v_generation_4301_);
v_goal_4427_ = lean_ctor_get(v_a_4322_, 0);
lean_inc_ref(v_goal_4427_);
lean_dec_ref_known(v_a_4322_, 1);
lean_inc(v_a_4313_);
lean_inc_ref(v_a_4312_);
lean_inc(v_a_4311_);
lean_inc_ref(v_a_4310_);
lean_inc(v_a_4309_);
lean_inc_ref(v_a_4308_);
lean_inc(v_a_4307_);
lean_inc_ref(v_a_4306_);
lean_inc(v_a_4305_);
v___x_4428_ = lean_apply_11(v_kp_4304_, v_goal_4427_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, lean_box(0));
return v___x_4428_;
}
default: 
{
lean_object* v_fvarId_4429_; lean_object* v_goal_4430_; lean_object* v___x_4431_; 
v_fvarId_4429_ = lean_ctor_get(v_a_4322_, 0);
lean_inc(v_fvarId_4429_);
v_goal_4430_ = lean_ctor_get(v_a_4322_, 1);
lean_inc_ref_n(v_goal_4430_, 2);
lean_dec_ref_known(v_a_4322_, 2);
lean_inc_ref(v_kp_4304_);
v___x_4431_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_4430_, v_fvarId_4429_, v_generation_4301_, v_kp_4304_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_);
if (lean_obj_tag(v___x_4431_) == 0)
{
lean_object* v_a_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4441_; 
v_a_4432_ = lean_ctor_get(v___x_4431_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4431_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4434_ = v___x_4431_;
v_isShared_4435_ = v_isSharedCheck_4441_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_a_4432_);
lean_dec(v___x_4431_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4441_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
if (lean_obj_tag(v_a_4432_) == 1)
{
lean_object* v_val_4436_; lean_object* v___x_4438_; 
lean_dec_ref(v_goal_4430_);
lean_dec_ref(v_kp_4304_);
v_val_4436_ = lean_ctor_get(v_a_4432_, 0);
lean_inc(v_val_4436_);
lean_dec_ref_known(v_a_4432_, 1);
if (v_isShared_4435_ == 0)
{
lean_ctor_set(v___x_4434_, 0, v_val_4436_);
v___x_4438_ = v___x_4434_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_val_4436_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
else
{
lean_object* v___x_4440_; 
lean_del_object(v___x_4434_);
lean_dec(v_a_4432_);
lean_inc(v_a_4313_);
lean_inc_ref(v_a_4312_);
lean_inc(v_a_4311_);
lean_inc_ref(v_a_4310_);
lean_inc(v_a_4309_);
lean_inc_ref(v_a_4308_);
lean_inc(v_a_4307_);
lean_inc_ref(v_a_4306_);
lean_inc(v_a_4305_);
v___x_4440_ = lean_apply_11(v_kp_4304_, v_goal_4430_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, lean_box(0));
return v___x_4440_;
}
}
}
else
{
lean_object* v_a_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4449_; 
lean_dec_ref(v_goal_4430_);
lean_dec_ref(v_kp_4304_);
v_a_4442_ = lean_ctor_get(v___x_4431_, 0);
v_isSharedCheck_4449_ = !lean_is_exclusive(v___x_4431_);
if (v_isSharedCheck_4449_ == 0)
{
v___x_4444_ = v___x_4431_;
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_a_4442_);
lean_dec(v___x_4431_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4447_; 
if (v_isShared_4445_ == 0)
{
v___x_4447_ = v___x_4444_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_a_4442_);
v___x_4447_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
return v___x_4447_;
}
}
}
}
}
}
else
{
lean_object* v_a_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4457_; 
lean_dec_ref(v_kp_4304_);
lean_dec(v_generation_4301_);
v_a_4450_ = lean_ctor_get(v___x_4321_, 0);
v_isSharedCheck_4457_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4457_ == 0)
{
v___x_4452_ = v___x_4321_;
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_a_4450_);
lean_dec(v___x_4321_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4455_; 
if (v_isShared_4453_ == 0)
{
v___x_4455_ = v___x_4452_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_a_4450_);
v___x_4455_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
return v___x_4455_;
}
}
}
}
else
{
lean_object* v___x_4458_; 
lean_dec_ref(v_kp_4304_);
lean_dec(v_generation_4301_);
lean_inc(v_a_4313_);
lean_inc_ref(v_a_4312_);
lean_inc(v_a_4311_);
lean_inc_ref(v_a_4310_);
lean_inc(v_a_4309_);
lean_inc_ref(v_a_4308_);
lean_inc(v_a_4307_);
lean_inc_ref(v_a_4306_);
lean_inc(v_a_4305_);
v___x_4458_ = lean_apply_11(v_kna_4303_, v_goal_4302_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, lean_box(0));
return v___x_4458_;
}
}
else
{
lean_object* v_a_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4466_; 
lean_dec_ref(v_kp_4304_);
lean_dec_ref(v_kna_4303_);
lean_dec_ref(v_goal_4302_);
lean_dec(v_generation_4301_);
v_a_4459_ = lean_ctor_get(v___x_4318_, 0);
v_isSharedCheck_4466_ = !lean_is_exclusive(v___x_4318_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4461_ = v___x_4318_;
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_a_4459_);
lean_dec(v___x_4318_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v___x_4464_; 
if (v_isShared_4462_ == 0)
{
v___x_4464_ = v___x_4461_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_a_4459_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
return v___x_4464_;
}
}
}
}
else
{
lean_object* v___x_4467_; lean_object* v___x_4468_; 
lean_dec_ref(v_kp_4304_);
lean_dec_ref(v_kna_4303_);
lean_dec_ref(v_goal_4302_);
lean_dec(v_generation_4301_);
v___x_4467_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intro___closed__0));
v___x_4468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4468_, 0, v___x_4467_);
return v___x_4468_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intro___boxed(lean_object* v_generation_4469_, lean_object* v_goal_4470_, lean_object* v_kna_4471_, lean_object* v_kp_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_){
_start:
{
lean_object* v_res_4483_; 
v_res_4483_ = l_Lean_Meta_Grind_Action_intro(v_generation_4469_, v_goal_4470_, v_kna_4471_, v_kp_4472_, v_a_4473_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_, v_a_4480_, v_a_4481_);
lean_dec(v_a_4481_);
lean_dec_ref(v_a_4480_);
lean_dec(v_a_4479_);
lean_dec_ref(v_a_4478_);
lean_dec(v_a_4477_);
lean_dec_ref(v_a_4476_);
lean_dec(v_a_4475_);
lean_dec_ref(v_a_4474_);
lean_dec(v_a_4473_);
return v_res_4483_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_hugeNumber(void){
_start:
{
lean_object* v___x_4484_; 
v___x_4484_ = lean_unsigned_to_nat(1000000u);
return v___x_4484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0(lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_){
_start:
{
lean_object* v___x_4498_; 
v___x_4498_ = l_Lean_Meta_Grind_Action_group___redArg(v___y_4485_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
return v___x_4498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__0___boxed(lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_){
_start:
{
lean_object* v_res_4512_; 
v_res_4512_ = l_Lean_Meta_Grind_Action_intros___lam__0(v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_);
lean_dec(v___y_4510_);
lean_dec_ref(v___y_4509_);
lean_dec(v___y_4508_);
lean_dec_ref(v___y_4507_);
lean_dec(v___y_4506_);
lean_dec_ref(v___y_4505_);
lean_dec(v___y_4504_);
lean_dec_ref(v___y_4503_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4500_);
return v_res_4512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1(lean_object* v_generation_4513_, lean_object* v___f_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_){
_start:
{
lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4528_ = lean_unsigned_to_nat(1000000u);
v___x_4529_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intro___boxed), 14, 1);
lean_closure_set(v___x_4529_, 0, v_generation_4513_);
v___x_4530_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_loop___boxed), 15, 2);
lean_closure_set(v___x_4530_, 0, v___x_4528_);
lean_closure_set(v___x_4530_, 1, v___x_4529_);
v___x_4531_ = l_Lean_Meta_Grind_Action_andThen(v___x_4530_, v___f_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
return v___x_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___lam__1___boxed(lean_object* v_generation_4532_, lean_object* v___f_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_){
_start:
{
lean_object* v_res_4547_; 
v_res_4547_ = l_Lean_Meta_Grind_Action_intros___lam__1(v_generation_4532_, v___f_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_);
lean_dec(v___y_4545_);
lean_dec_ref(v___y_4544_);
lean_dec(v___y_4543_);
lean_dec_ref(v___y_4542_);
lean_dec(v___y_4541_);
lean_dec_ref(v___y_4540_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
lean_dec(v___y_4537_);
return v_res_4547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros(lean_object* v_generation_4550_, lean_object* v_a_4551_, lean_object* v_kna_4552_, lean_object* v_kp_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_){
_start:
{
lean_object* v___f_4564_; lean_object* v___f_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; 
v___f_4564_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intros___closed__0));
v___f_4565_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___lam__1___boxed), 15, 2);
lean_closure_set(v___f_4565_, 0, v_generation_4550_);
lean_closure_set(v___f_4565_, 1, v___f_4564_);
v___x_4566_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intros___closed__1));
v___x_4567_ = l_Lean_Meta_Grind_Action_andThen(v___x_4566_, v___f_4565_, v_a_4551_, v_kna_4552_, v_kp_4553_, v_a_4554_, v_a_4555_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_, v_a_4562_);
return v___x_4567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_intros___boxed(lean_object* v_generation_4568_, lean_object* v_a_4569_, lean_object* v_kna_4570_, lean_object* v_kp_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_){
_start:
{
lean_object* v_res_4582_; 
v_res_4582_ = l_Lean_Meta_Grind_Action_intros(v_generation_4568_, v_a_4569_, v_kna_4570_, v_kp_4571_, v_a_4572_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_);
lean_dec(v_a_4580_);
lean_dec_ref(v_a_4579_);
lean_dec(v_a_4578_);
lean_dec_ref(v_a_4577_);
lean_dec(v_a_4576_);
lean_dec_ref(v_a_4575_);
lean_dec(v_a_4574_);
lean_dec_ref(v_a_4573_);
lean_dec(v_a_4572_);
return v_res_4582_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; 
v___x_4590_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__2));
v___x_4591_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1));
v___x_4592_ = l_Lean_mkConst(v___x_4591_, v___x_4590_);
return v___x_4592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(lean_object* v_goal_4593_, lean_object* v_prop_4594_, lean_object* v_proof_4595_, lean_object* v_generation_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_){
_start:
{
lean_object* v___x_4607_; lean_object* v___x_4608_; 
v___x_4607_ = lean_st_mk_ref(v_goal_4593_);
lean_inc(v___y_4605_);
lean_inc_ref(v___y_4604_);
lean_inc(v___y_4603_);
lean_inc_ref(v___y_4602_);
lean_inc(v___y_4601_);
lean_inc_ref(v___y_4600_);
lean_inc(v___y_4599_);
lean_inc_ref(v___y_4598_);
lean_inc(v___y_4597_);
lean_inc(v___x_4607_);
lean_inc_ref(v_prop_4594_);
v___x_4608_ = lean_grind_preprocess(v_prop_4594_, v___x_4607_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_);
if (lean_obj_tag(v___x_4608_) == 0)
{
lean_object* v_a_4609_; lean_object* v_expr_4610_; lean_object* v___x_4611_; 
v_a_4609_ = lean_ctor_get(v___x_4608_, 0);
lean_inc(v_a_4609_);
lean_dec_ref_known(v___x_4608_, 1);
v_expr_4610_ = lean_ctor_get(v_a_4609_, 0);
lean_inc_ref(v_expr_4610_);
v___x_4611_ = l_Lean_Meta_Simp_Result_getProof(v_a_4609_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_);
if (lean_obj_tag(v___x_4611_) == 0)
{
lean_object* v_a_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; 
v_a_4612_ = lean_ctor_get(v___x_4611_, 0);
lean_inc(v_a_4612_);
lean_dec_ref_known(v___x_4611_, 1);
v___x_4613_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3);
lean_inc_ref(v_expr_4610_);
v___x_4614_ = l_Lean_mkApp4(v___x_4613_, v_prop_4594_, v_expr_4610_, v_a_4612_, v_proof_4595_);
v___x_4615_ = l_Lean_Meta_Grind_add(v_expr_4610_, v___x_4614_, v_generation_4596_, v___x_4607_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_);
if (lean_obj_tag(v___x_4615_) == 0)
{
lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4624_; 
v_isSharedCheck_4624_ = !lean_is_exclusive(v___x_4615_);
if (v_isSharedCheck_4624_ == 0)
{
lean_object* v_unused_4625_; 
v_unused_4625_ = lean_ctor_get(v___x_4615_, 0);
lean_dec(v_unused_4625_);
v___x_4617_ = v___x_4615_;
v_isShared_4618_ = v_isSharedCheck_4624_;
goto v_resetjp_4616_;
}
else
{
lean_dec(v___x_4615_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4624_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4622_; 
v___x_4619_ = lean_st_ref_get(v___x_4607_);
v___x_4620_ = lean_st_ref_get(v___x_4607_);
lean_dec(v___x_4607_);
lean_dec(v___x_4620_);
if (v_isShared_4618_ == 0)
{
lean_ctor_set(v___x_4617_, 0, v___x_4619_);
v___x_4622_ = v___x_4617_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v___x_4619_);
v___x_4622_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
return v___x_4622_;
}
}
}
else
{
lean_object* v_a_4626_; lean_object* v___x_4628_; uint8_t v_isShared_4629_; uint8_t v_isSharedCheck_4633_; 
lean_dec(v___x_4607_);
v_a_4626_ = lean_ctor_get(v___x_4615_, 0);
v_isSharedCheck_4633_ = !lean_is_exclusive(v___x_4615_);
if (v_isSharedCheck_4633_ == 0)
{
v___x_4628_ = v___x_4615_;
v_isShared_4629_ = v_isSharedCheck_4633_;
goto v_resetjp_4627_;
}
else
{
lean_inc(v_a_4626_);
lean_dec(v___x_4615_);
v___x_4628_ = lean_box(0);
v_isShared_4629_ = v_isSharedCheck_4633_;
goto v_resetjp_4627_;
}
v_resetjp_4627_:
{
lean_object* v___x_4631_; 
if (v_isShared_4629_ == 0)
{
v___x_4631_ = v___x_4628_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4632_; 
v_reuseFailAlloc_4632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4632_, 0, v_a_4626_);
v___x_4631_ = v_reuseFailAlloc_4632_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
return v___x_4631_;
}
}
}
}
else
{
lean_object* v_a_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4641_; 
lean_dec_ref(v_expr_4610_);
lean_dec(v___x_4607_);
lean_dec(v_generation_4596_);
lean_dec_ref(v_proof_4595_);
lean_dec_ref(v_prop_4594_);
v_a_4634_ = lean_ctor_get(v___x_4611_, 0);
v_isSharedCheck_4641_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4641_ == 0)
{
v___x_4636_ = v___x_4611_;
v_isShared_4637_ = v_isSharedCheck_4641_;
goto v_resetjp_4635_;
}
else
{
lean_inc(v_a_4634_);
lean_dec(v___x_4611_);
v___x_4636_ = lean_box(0);
v_isShared_4637_ = v_isSharedCheck_4641_;
goto v_resetjp_4635_;
}
v_resetjp_4635_:
{
lean_object* v___x_4639_; 
if (v_isShared_4637_ == 0)
{
v___x_4639_ = v___x_4636_;
goto v_reusejp_4638_;
}
else
{
lean_object* v_reuseFailAlloc_4640_; 
v_reuseFailAlloc_4640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4640_, 0, v_a_4634_);
v___x_4639_ = v_reuseFailAlloc_4640_;
goto v_reusejp_4638_;
}
v_reusejp_4638_:
{
return v___x_4639_;
}
}
}
}
else
{
lean_object* v_a_4642_; lean_object* v___x_4644_; uint8_t v_isShared_4645_; uint8_t v_isSharedCheck_4649_; 
lean_dec(v___x_4607_);
lean_dec(v_generation_4596_);
lean_dec_ref(v_proof_4595_);
lean_dec_ref(v_prop_4594_);
v_a_4642_ = lean_ctor_get(v___x_4608_, 0);
v_isSharedCheck_4649_ = !lean_is_exclusive(v___x_4608_);
if (v_isSharedCheck_4649_ == 0)
{
v___x_4644_ = v___x_4608_;
v_isShared_4645_ = v_isSharedCheck_4649_;
goto v_resetjp_4643_;
}
else
{
lean_inc(v_a_4642_);
lean_dec(v___x_4608_);
v___x_4644_ = lean_box(0);
v_isShared_4645_ = v_isSharedCheck_4649_;
goto v_resetjp_4643_;
}
v_resetjp_4643_:
{
lean_object* v___x_4647_; 
if (v_isShared_4645_ == 0)
{
v___x_4647_ = v___x_4644_;
goto v_reusejp_4646_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v_a_4642_);
v___x_4647_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4646_;
}
v_reusejp_4646_:
{
return v___x_4647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed(lean_object* v_goal_4650_, lean_object* v_prop_4651_, lean_object* v_proof_4652_, lean_object* v_generation_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_){
_start:
{
lean_object* v_res_4664_; 
v_res_4664_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(v_goal_4650_, v_prop_4651_, v_proof_4652_, v_generation_4653_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
lean_dec(v___y_4656_);
lean_dec_ref(v___y_4655_);
lean_dec(v___y_4654_);
return v_res_4664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(lean_object* v_goal_4665_, lean_object* v___f_4666_, lean_object* v_kp_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_){
_start:
{
lean_object* v_mvarId_4678_; lean_object* v___x_4679_; 
v_mvarId_4678_ = lean_ctor_get(v_goal_4665_, 1);
lean_inc(v_mvarId_4678_);
lean_dec_ref(v_goal_4665_);
v___x_4679_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_4678_, v___f_4666_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_);
if (lean_obj_tag(v___x_4679_) == 0)
{
lean_object* v_a_4680_; lean_object* v___x_4681_; 
v_a_4680_ = lean_ctor_get(v___x_4679_, 0);
lean_inc(v_a_4680_);
lean_dec_ref_known(v___x_4679_, 1);
lean_inc(v___y_4676_);
lean_inc_ref(v___y_4675_);
lean_inc(v___y_4674_);
lean_inc_ref(v___y_4673_);
lean_inc(v___y_4672_);
lean_inc_ref(v___y_4671_);
lean_inc(v___y_4670_);
lean_inc_ref(v___y_4669_);
lean_inc(v___y_4668_);
v___x_4681_ = lean_apply_11(v_kp_4667_, v_a_4680_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_, lean_box(0));
return v___x_4681_;
}
else
{
lean_object* v_a_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4689_; 
lean_dec_ref(v_kp_4667_);
v_a_4682_ = lean_ctor_get(v___x_4679_, 0);
v_isSharedCheck_4689_ = !lean_is_exclusive(v___x_4679_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4684_ = v___x_4679_;
v_isShared_4685_ = v_isSharedCheck_4689_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_a_4682_);
lean_dec(v___x_4679_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4689_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v___x_4687_; 
if (v_isShared_4685_ == 0)
{
v___x_4687_ = v___x_4684_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v_a_4682_);
v___x_4687_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
return v___x_4687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed(lean_object* v_goal_4690_, lean_object* v___f_4691_, lean_object* v_kp_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_){
_start:
{
lean_object* v_res_4703_; 
v_res_4703_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(v_goal_4690_, v___f_4691_, v_kp_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_, v___y_4701_);
lean_dec(v___y_4701_);
lean_dec_ref(v___y_4700_);
lean_dec(v___y_4699_);
lean_dec_ref(v___y_4698_);
lean_dec(v___y_4697_);
lean_dec_ref(v___y_4696_);
lean_dec(v___y_4695_);
lean_dec_ref(v___y_4694_);
lean_dec(v___y_4693_);
return v_res_4703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(lean_object* v_proof_4704_, lean_object* v_prop_4705_, lean_object* v_generation_4706_, lean_object* v_goal_4707_, lean_object* v_kna_4708_, lean_object* v_kp_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_){
_start:
{
lean_object* v___f_4720_; lean_object* v___f_4721_; lean_object* v___x_4722_; 
lean_inc(v_generation_4706_);
lean_inc_ref(v_proof_4704_);
lean_inc_ref(v_prop_4705_);
lean_inc_ref_n(v_goal_4707_, 2);
v___f_4720_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed), 14, 4);
lean_closure_set(v___f_4720_, 0, v_goal_4707_);
lean_closure_set(v___f_4720_, 1, v_prop_4705_);
lean_closure_set(v___f_4720_, 2, v_proof_4704_);
lean_closure_set(v___f_4720_, 3, v_generation_4706_);
lean_inc_ref(v_kp_4709_);
v___f_4721_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed), 13, 3);
lean_closure_set(v___f_4721_, 0, v_goal_4707_);
lean_closure_set(v___f_4721_, 1, v___f_4720_);
lean_closure_set(v___f_4721_, 2, v_kp_4709_);
v___x_4722_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_prop_4705_, v_a_4711_);
if (lean_obj_tag(v___x_4722_) == 0)
{
lean_object* v_a_4723_; uint8_t v___x_4724_; 
v_a_4723_ = lean_ctor_get(v___x_4722_, 0);
lean_inc(v_a_4723_);
lean_dec_ref_known(v___x_4722_, 1);
v___x_4724_ = lean_unbox(v_a_4723_);
lean_dec(v_a_4723_);
if (v___x_4724_ == 0)
{
lean_object* v_mvarId_4725_; lean_object* v___x_4726_; 
lean_dec_ref(v_kp_4709_);
lean_dec_ref(v_kna_4708_);
lean_dec(v_generation_4706_);
lean_dec_ref(v_prop_4705_);
lean_dec_ref(v_proof_4704_);
v_mvarId_4725_ = lean_ctor_get(v_goal_4707_, 1);
lean_inc(v_mvarId_4725_);
lean_dec_ref(v_goal_4707_);
v___x_4726_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_4725_, v___f_4721_, v_a_4710_, v_a_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_, v_a_4716_, v_a_4717_, v_a_4718_);
return v___x_4726_;
}
else
{
lean_object* v___x_4727_; lean_object* v___x_4728_; 
lean_dec_ref(v___f_4721_);
v___x_4727_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3));
v___x_4728_ = l_Lean_Core_mkFreshUserName(v___x_4727_, v_a_4717_, v_a_4718_);
if (lean_obj_tag(v___x_4728_) == 0)
{
lean_object* v_a_4729_; lean_object* v_toGoalState_4730_; lean_object* v_mvarId_4731_; lean_object* v___x_4733_; uint8_t v_isShared_4734_; uint8_t v_isSharedCheck_4762_; 
v_a_4729_ = lean_ctor_get(v___x_4728_, 0);
lean_inc(v_a_4729_);
lean_dec_ref_known(v___x_4728_, 1);
v_toGoalState_4730_ = lean_ctor_get(v_goal_4707_, 0);
v_mvarId_4731_ = lean_ctor_get(v_goal_4707_, 1);
v_isSharedCheck_4762_ = !lean_is_exclusive(v_goal_4707_);
if (v_isSharedCheck_4762_ == 0)
{
v___x_4733_ = v_goal_4707_;
v_isShared_4734_ = v_isSharedCheck_4762_;
goto v_resetjp_4732_;
}
else
{
lean_inc(v_mvarId_4731_);
lean_inc(v_toGoalState_4730_);
lean_dec(v_goal_4707_);
v___x_4733_ = lean_box(0);
v_isShared_4734_ = v_isSharedCheck_4762_;
goto v_resetjp_4732_;
}
v_resetjp_4732_:
{
lean_object* v___x_4735_; 
lean_inc_ref(v_prop_4705_);
lean_inc(v_mvarId_4731_);
v___x_4735_ = l_Lean_MVarId_assert(v_mvarId_4731_, v_a_4729_, v_prop_4705_, v_proof_4704_, v_a_4715_, v_a_4716_, v_a_4717_, v_a_4718_);
if (lean_obj_tag(v___x_4735_) == 0)
{
lean_object* v_a_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; 
v_a_4736_ = lean_ctor_get(v___x_4735_, 0);
lean_inc(v_a_4736_);
lean_dec_ref_known(v___x_4735_, 1);
v___x_4737_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_getAnchor___boxed), 11, 1);
lean_closure_set(v___x_4737_, 0, v_prop_4705_);
v___x_4738_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_4731_, v___x_4737_, v_a_4710_, v_a_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_, v_a_4716_, v_a_4717_, v_a_4718_);
if (lean_obj_tag(v___x_4738_) == 0)
{
lean_object* v_a_4739_; lean_object* v___x_4741_; 
v_a_4739_ = lean_ctor_get(v___x_4738_, 0);
lean_inc(v_a_4739_);
lean_dec_ref_known(v___x_4738_, 1);
if (v_isShared_4734_ == 0)
{
lean_ctor_set(v___x_4733_, 1, v_a_4736_);
v___x_4741_ = v___x_4733_;
goto v_reusejp_4740_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v_toGoalState_4730_);
lean_ctor_set(v_reuseFailAlloc_4745_, 1, v_a_4736_);
v___x_4741_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4740_;
}
v_reusejp_4740_:
{
uint64_t v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4742_ = lean_unbox_uint64(v_a_4739_);
lean_dec(v_a_4739_);
v___x_4743_ = l_Lean_Meta_Grind_Goal_setIntroBase(v___x_4741_, v___x_4742_);
v___x_4744_ = l_Lean_Meta_Grind_Action_intros(v_generation_4706_, v___x_4743_, v_kna_4708_, v_kp_4709_, v_a_4710_, v_a_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_, v_a_4716_, v_a_4717_, v_a_4718_);
return v___x_4744_;
}
}
else
{
lean_object* v_a_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4753_; 
lean_dec(v_a_4736_);
lean_del_object(v___x_4733_);
lean_dec_ref(v_toGoalState_4730_);
lean_dec_ref(v_kp_4709_);
lean_dec_ref(v_kna_4708_);
lean_dec(v_generation_4706_);
v_a_4746_ = lean_ctor_get(v___x_4738_, 0);
v_isSharedCheck_4753_ = !lean_is_exclusive(v___x_4738_);
if (v_isSharedCheck_4753_ == 0)
{
v___x_4748_ = v___x_4738_;
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
else
{
lean_inc(v_a_4746_);
lean_dec(v___x_4738_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v___x_4751_; 
if (v_isShared_4749_ == 0)
{
v___x_4751_ = v___x_4748_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v_a_4746_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
return v___x_4751_;
}
}
}
}
else
{
lean_object* v_a_4754_; lean_object* v___x_4756_; uint8_t v_isShared_4757_; uint8_t v_isSharedCheck_4761_; 
lean_del_object(v___x_4733_);
lean_dec(v_mvarId_4731_);
lean_dec_ref(v_toGoalState_4730_);
lean_dec_ref(v_kp_4709_);
lean_dec_ref(v_kna_4708_);
lean_dec(v_generation_4706_);
lean_dec_ref(v_prop_4705_);
v_a_4754_ = lean_ctor_get(v___x_4735_, 0);
v_isSharedCheck_4761_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4761_ == 0)
{
v___x_4756_ = v___x_4735_;
v_isShared_4757_ = v_isSharedCheck_4761_;
goto v_resetjp_4755_;
}
else
{
lean_inc(v_a_4754_);
lean_dec(v___x_4735_);
v___x_4756_ = lean_box(0);
v_isShared_4757_ = v_isSharedCheck_4761_;
goto v_resetjp_4755_;
}
v_resetjp_4755_:
{
lean_object* v___x_4759_; 
if (v_isShared_4757_ == 0)
{
v___x_4759_ = v___x_4756_;
goto v_reusejp_4758_;
}
else
{
lean_object* v_reuseFailAlloc_4760_; 
v_reuseFailAlloc_4760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4760_, 0, v_a_4754_);
v___x_4759_ = v_reuseFailAlloc_4760_;
goto v_reusejp_4758_;
}
v_reusejp_4758_:
{
return v___x_4759_;
}
}
}
}
}
else
{
lean_object* v_a_4763_; lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4770_; 
lean_dec_ref(v_kp_4709_);
lean_dec_ref(v_kna_4708_);
lean_dec_ref(v_goal_4707_);
lean_dec(v_generation_4706_);
lean_dec_ref(v_prop_4705_);
lean_dec_ref(v_proof_4704_);
v_a_4763_ = lean_ctor_get(v___x_4728_, 0);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___x_4728_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4765_ = v___x_4728_;
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
else
{
lean_inc(v_a_4763_);
lean_dec(v___x_4728_);
v___x_4765_ = lean_box(0);
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
v_resetjp_4764_:
{
lean_object* v___x_4768_; 
if (v_isShared_4766_ == 0)
{
v___x_4768_ = v___x_4765_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_a_4763_);
v___x_4768_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
return v___x_4768_;
}
}
}
}
}
else
{
lean_object* v_a_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4778_; 
lean_dec_ref(v___f_4721_);
lean_dec_ref(v_kp_4709_);
lean_dec_ref(v_kna_4708_);
lean_dec_ref(v_goal_4707_);
lean_dec(v_generation_4706_);
lean_dec_ref(v_prop_4705_);
lean_dec_ref(v_proof_4704_);
v_a_4771_ = lean_ctor_get(v___x_4722_, 0);
v_isSharedCheck_4778_ = !lean_is_exclusive(v___x_4722_);
if (v_isSharedCheck_4778_ == 0)
{
v___x_4773_ = v___x_4722_;
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_a_4771_);
lean_dec(v___x_4722_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
lean_object* v___x_4776_; 
if (v_isShared_4774_ == 0)
{
v___x_4776_ = v___x_4773_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_a_4771_);
v___x_4776_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
return v___x_4776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___boxed(lean_object* v_proof_4779_, lean_object* v_prop_4780_, lean_object* v_generation_4781_, lean_object* v_goal_4782_, lean_object* v_kna_4783_, lean_object* v_kp_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_){
_start:
{
lean_object* v_res_4795_; 
v_res_4795_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(v_proof_4779_, v_prop_4780_, v_generation_4781_, v_goal_4782_, v_kna_4783_, v_kp_4784_, v_a_4785_, v_a_4786_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_, v_a_4791_, v_a_4792_, v_a_4793_);
lean_dec(v_a_4793_);
lean_dec_ref(v_a_4792_);
lean_dec(v_a_4791_);
lean_dec_ref(v_a_4790_);
lean_dec(v_a_4789_);
lean_dec_ref(v_a_4788_);
lean_dec(v_a_4787_);
lean_dec_ref(v_a_4786_);
lean_dec(v_a_4785_);
return v_res_4795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext(lean_object* v_goal_4796_, lean_object* v_kna_4797_, lean_object* v_kp_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_){
_start:
{
lean_object* v_toGoalState_4809_; uint8_t v_inconsistent_4810_; 
v_toGoalState_4809_ = lean_ctor_get(v_goal_4796_, 0);
lean_inc_ref(v_toGoalState_4809_);
v_inconsistent_4810_ = lean_ctor_get_uint8(v_toGoalState_4809_, sizeof(void*)*20 + 8);
if (v_inconsistent_4810_ == 0)
{
lean_object* v_mvarId_4811_; lean_object* v_nextDeclIdx_4812_; lean_object* v_enodeMap_4813_; lean_object* v_exprs_4814_; lean_object* v_parents_4815_; lean_object* v_congrTable_4816_; lean_object* v_appMap_4817_; lean_object* v_indicesFound_4818_; lean_object* v_toProcess_4819_; lean_object* v_internalizing_4820_; lean_object* v_nextIdx_4821_; lean_object* v_newRawFacts_4822_; lean_object* v_facts_4823_; lean_object* v_extThms_4824_; lean_object* v_ematch_4825_; lean_object* v_inj_4826_; lean_object* v_split_4827_; lean_object* v_clean_4828_; lean_object* v_sstates_4829_; lean_object* v_goalStack_4830_; uint64_t v_introBase_4831_; lean_object* v_numIntros_4832_; lean_object* v___x_4834_; uint8_t v_isShared_4835_; uint8_t v_isSharedCheck_4875_; 
v_mvarId_4811_ = lean_ctor_get(v_goal_4796_, 1);
v_nextDeclIdx_4812_ = lean_ctor_get(v_toGoalState_4809_, 0);
v_enodeMap_4813_ = lean_ctor_get(v_toGoalState_4809_, 1);
v_exprs_4814_ = lean_ctor_get(v_toGoalState_4809_, 2);
v_parents_4815_ = lean_ctor_get(v_toGoalState_4809_, 3);
v_congrTable_4816_ = lean_ctor_get(v_toGoalState_4809_, 4);
v_appMap_4817_ = lean_ctor_get(v_toGoalState_4809_, 5);
v_indicesFound_4818_ = lean_ctor_get(v_toGoalState_4809_, 6);
v_toProcess_4819_ = lean_ctor_get(v_toGoalState_4809_, 7);
v_internalizing_4820_ = lean_ctor_get(v_toGoalState_4809_, 8);
v_nextIdx_4821_ = lean_ctor_get(v_toGoalState_4809_, 9);
v_newRawFacts_4822_ = lean_ctor_get(v_toGoalState_4809_, 10);
v_facts_4823_ = lean_ctor_get(v_toGoalState_4809_, 11);
v_extThms_4824_ = lean_ctor_get(v_toGoalState_4809_, 12);
v_ematch_4825_ = lean_ctor_get(v_toGoalState_4809_, 13);
v_inj_4826_ = lean_ctor_get(v_toGoalState_4809_, 14);
v_split_4827_ = lean_ctor_get(v_toGoalState_4809_, 15);
v_clean_4828_ = lean_ctor_get(v_toGoalState_4809_, 16);
v_sstates_4829_ = lean_ctor_get(v_toGoalState_4809_, 17);
v_goalStack_4830_ = lean_ctor_get(v_toGoalState_4809_, 18);
v_introBase_4831_ = lean_ctor_get_uint64(v_toGoalState_4809_, sizeof(void*)*20);
v_numIntros_4832_ = lean_ctor_get(v_toGoalState_4809_, 19);
v_isSharedCheck_4875_ = !lean_is_exclusive(v_toGoalState_4809_);
if (v_isSharedCheck_4875_ == 0)
{
v___x_4834_ = v_toGoalState_4809_;
v_isShared_4835_ = v_isSharedCheck_4875_;
goto v_resetjp_4833_;
}
else
{
lean_inc(v_numIntros_4832_);
lean_inc(v_goalStack_4830_);
lean_inc(v_sstates_4829_);
lean_inc(v_clean_4828_);
lean_inc(v_split_4827_);
lean_inc(v_inj_4826_);
lean_inc(v_ematch_4825_);
lean_inc(v_extThms_4824_);
lean_inc(v_facts_4823_);
lean_inc(v_newRawFacts_4822_);
lean_inc(v_nextIdx_4821_);
lean_inc(v_internalizing_4820_);
lean_inc(v_toProcess_4819_);
lean_inc(v_indicesFound_4818_);
lean_inc(v_appMap_4817_);
lean_inc(v_congrTable_4816_);
lean_inc(v_parents_4815_);
lean_inc(v_exprs_4814_);
lean_inc(v_enodeMap_4813_);
lean_inc(v_nextDeclIdx_4812_);
lean_dec(v_toGoalState_4809_);
v___x_4834_ = lean_box(0);
v_isShared_4835_ = v_isSharedCheck_4875_;
goto v_resetjp_4833_;
}
v_resetjp_4833_:
{
lean_object* v___x_4836_; 
v___x_4836_ = l_Std_Queue_dequeue_x3f___redArg(v_newRawFacts_4822_);
if (lean_obj_tag(v___x_4836_) == 1)
{
lean_object* v___x_4838_; uint8_t v_isShared_4839_; uint8_t v_isSharedCheck_4871_; 
lean_inc(v_mvarId_4811_);
v_isSharedCheck_4871_ = !lean_is_exclusive(v_goal_4796_);
if (v_isSharedCheck_4871_ == 0)
{
lean_object* v_unused_4872_; lean_object* v_unused_4873_; 
v_unused_4872_ = lean_ctor_get(v_goal_4796_, 1);
lean_dec(v_unused_4872_);
v_unused_4873_ = lean_ctor_get(v_goal_4796_, 0);
lean_dec(v_unused_4873_);
v___x_4838_ = v_goal_4796_;
v_isShared_4839_ = v_isSharedCheck_4871_;
goto v_resetjp_4837_;
}
else
{
lean_dec(v_goal_4796_);
v___x_4838_ = lean_box(0);
v_isShared_4839_ = v_isSharedCheck_4871_;
goto v_resetjp_4837_;
}
v_resetjp_4837_:
{
lean_object* v_val_4840_; lean_object* v_fst_4841_; lean_object* v_snd_4842_; lean_object* v_proof_4843_; lean_object* v_prop_4844_; lean_object* v_generation_4845_; lean_object* v_splitSource_4846_; lean_object* v_ematchDiagSource_4847_; lean_object* v_simp_4848_; lean_object* v_simpMethods_4849_; lean_object* v_symSimpMethods_4850_; lean_object* v_symDSimpMethods_4851_; lean_object* v_config_4852_; lean_object* v_identity_4853_; lean_object* v_activeSolvers_4854_; lean_object* v_anchorRefs_x3f_4855_; uint8_t v_anchors_4856_; uint8_t v_cheapCases_4857_; uint8_t v_reportMVarIssue_4858_; lean_object* v_symPrios_4859_; lean_object* v_extensions_4860_; uint8_t v_debug_4861_; uint8_t v_ematchDiag_4862_; lean_object* v___x_4864_; 
v_val_4840_ = lean_ctor_get(v___x_4836_, 0);
lean_inc(v_val_4840_);
lean_dec_ref_known(v___x_4836_, 1);
v_fst_4841_ = lean_ctor_get(v_val_4840_, 0);
lean_inc(v_fst_4841_);
v_snd_4842_ = lean_ctor_get(v_val_4840_, 1);
lean_inc(v_snd_4842_);
lean_dec(v_val_4840_);
v_proof_4843_ = lean_ctor_get(v_fst_4841_, 0);
lean_inc_ref(v_proof_4843_);
v_prop_4844_ = lean_ctor_get(v_fst_4841_, 1);
lean_inc_ref(v_prop_4844_);
v_generation_4845_ = lean_ctor_get(v_fst_4841_, 2);
lean_inc(v_generation_4845_);
v_splitSource_4846_ = lean_ctor_get(v_fst_4841_, 3);
lean_inc(v_splitSource_4846_);
v_ematchDiagSource_4847_ = lean_ctor_get(v_fst_4841_, 4);
lean_inc(v_ematchDiagSource_4847_);
lean_dec(v_fst_4841_);
v_simp_4848_ = lean_ctor_get(v_a_4800_, 0);
v_simpMethods_4849_ = lean_ctor_get(v_a_4800_, 1);
v_symSimpMethods_4850_ = lean_ctor_get(v_a_4800_, 2);
v_symDSimpMethods_4851_ = lean_ctor_get(v_a_4800_, 3);
v_config_4852_ = lean_ctor_get(v_a_4800_, 4);
v_identity_4853_ = lean_ctor_get(v_a_4800_, 5);
v_activeSolvers_4854_ = lean_ctor_get(v_a_4800_, 6);
v_anchorRefs_x3f_4855_ = lean_ctor_get(v_a_4800_, 7);
v_anchors_4856_ = lean_ctor_get_uint8(v_a_4800_, sizeof(void*)*12);
v_cheapCases_4857_ = lean_ctor_get_uint8(v_a_4800_, sizeof(void*)*12 + 1);
v_reportMVarIssue_4858_ = lean_ctor_get_uint8(v_a_4800_, sizeof(void*)*12 + 2);
v_symPrios_4859_ = lean_ctor_get(v_a_4800_, 10);
v_extensions_4860_ = lean_ctor_get(v_a_4800_, 11);
v_debug_4861_ = lean_ctor_get_uint8(v_a_4800_, sizeof(void*)*12 + 3);
v_ematchDiag_4862_ = lean_ctor_get_uint8(v_a_4800_, sizeof(void*)*12 + 4);
if (v_isShared_4835_ == 0)
{
lean_ctor_set(v___x_4834_, 10, v_snd_4842_);
v___x_4864_ = v___x_4834_;
goto v_reusejp_4863_;
}
else
{
lean_object* v_reuseFailAlloc_4870_; 
v_reuseFailAlloc_4870_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v_reuseFailAlloc_4870_, 0, v_nextDeclIdx_4812_);
lean_ctor_set(v_reuseFailAlloc_4870_, 1, v_enodeMap_4813_);
lean_ctor_set(v_reuseFailAlloc_4870_, 2, v_exprs_4814_);
lean_ctor_set(v_reuseFailAlloc_4870_, 3, v_parents_4815_);
lean_ctor_set(v_reuseFailAlloc_4870_, 4, v_congrTable_4816_);
lean_ctor_set(v_reuseFailAlloc_4870_, 5, v_appMap_4817_);
lean_ctor_set(v_reuseFailAlloc_4870_, 6, v_indicesFound_4818_);
lean_ctor_set(v_reuseFailAlloc_4870_, 7, v_toProcess_4819_);
lean_ctor_set(v_reuseFailAlloc_4870_, 8, v_internalizing_4820_);
lean_ctor_set(v_reuseFailAlloc_4870_, 9, v_nextIdx_4821_);
lean_ctor_set(v_reuseFailAlloc_4870_, 10, v_snd_4842_);
lean_ctor_set(v_reuseFailAlloc_4870_, 11, v_facts_4823_);
lean_ctor_set(v_reuseFailAlloc_4870_, 12, v_extThms_4824_);
lean_ctor_set(v_reuseFailAlloc_4870_, 13, v_ematch_4825_);
lean_ctor_set(v_reuseFailAlloc_4870_, 14, v_inj_4826_);
lean_ctor_set(v_reuseFailAlloc_4870_, 15, v_split_4827_);
lean_ctor_set(v_reuseFailAlloc_4870_, 16, v_clean_4828_);
lean_ctor_set(v_reuseFailAlloc_4870_, 17, v_sstates_4829_);
lean_ctor_set(v_reuseFailAlloc_4870_, 18, v_goalStack_4830_);
lean_ctor_set(v_reuseFailAlloc_4870_, 19, v_numIntros_4832_);
lean_ctor_set_uint8(v_reuseFailAlloc_4870_, sizeof(void*)*20 + 8, v_inconsistent_4810_);
lean_ctor_set_uint64(v_reuseFailAlloc_4870_, sizeof(void*)*20, v_introBase_4831_);
v___x_4864_ = v_reuseFailAlloc_4870_;
goto v_reusejp_4863_;
}
v_reusejp_4863_:
{
lean_object* v_goal_4866_; 
if (v_isShared_4839_ == 0)
{
lean_ctor_set(v___x_4838_, 0, v___x_4864_);
v_goal_4866_ = v___x_4838_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v___x_4864_);
lean_ctor_set(v_reuseFailAlloc_4869_, 1, v_mvarId_4811_);
v_goal_4866_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
lean_object* v___x_4867_; lean_object* v___x_4868_; 
lean_inc_ref(v_extensions_4860_);
lean_inc_ref(v_symPrios_4859_);
lean_inc(v_anchorRefs_x3f_4855_);
lean_inc_ref(v_activeSolvers_4854_);
lean_inc(v_identity_4853_);
lean_inc_ref(v_config_4852_);
lean_inc_ref(v_symDSimpMethods_4851_);
lean_inc_ref(v_symSimpMethods_4850_);
lean_inc_ref(v_simpMethods_4849_);
lean_inc_ref(v_simp_4848_);
v___x_4867_ = lean_alloc_ctor(0, 12, 5);
lean_ctor_set(v___x_4867_, 0, v_simp_4848_);
lean_ctor_set(v___x_4867_, 1, v_simpMethods_4849_);
lean_ctor_set(v___x_4867_, 2, v_symSimpMethods_4850_);
lean_ctor_set(v___x_4867_, 3, v_symDSimpMethods_4851_);
lean_ctor_set(v___x_4867_, 4, v_config_4852_);
lean_ctor_set(v___x_4867_, 5, v_identity_4853_);
lean_ctor_set(v___x_4867_, 6, v_activeSolvers_4854_);
lean_ctor_set(v___x_4867_, 7, v_anchorRefs_x3f_4855_);
lean_ctor_set(v___x_4867_, 8, v_splitSource_4846_);
lean_ctor_set(v___x_4867_, 9, v_ematchDiagSource_4847_);
lean_ctor_set(v___x_4867_, 10, v_symPrios_4859_);
lean_ctor_set(v___x_4867_, 11, v_extensions_4860_);
lean_ctor_set_uint8(v___x_4867_, sizeof(void*)*12, v_anchors_4856_);
lean_ctor_set_uint8(v___x_4867_, sizeof(void*)*12 + 1, v_cheapCases_4857_);
lean_ctor_set_uint8(v___x_4867_, sizeof(void*)*12 + 2, v_reportMVarIssue_4858_);
lean_ctor_set_uint8(v___x_4867_, sizeof(void*)*12 + 3, v_debug_4861_);
lean_ctor_set_uint8(v___x_4867_, sizeof(void*)*12 + 4, v_ematchDiag_4862_);
v___x_4868_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(v_proof_4843_, v_prop_4844_, v_generation_4845_, v_goal_4866_, v_kna_4797_, v_kp_4798_, v_a_4799_, v___x_4867_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_);
lean_dec_ref_known(v___x_4867_, 12);
return v___x_4868_;
}
}
}
}
else
{
lean_object* v___x_4874_; 
lean_dec(v___x_4836_);
lean_del_object(v___x_4834_);
lean_dec(v_numIntros_4832_);
lean_dec_ref(v_goalStack_4830_);
lean_dec_ref(v_sstates_4829_);
lean_dec_ref(v_clean_4828_);
lean_dec_ref(v_split_4827_);
lean_dec_ref(v_inj_4826_);
lean_dec_ref(v_ematch_4825_);
lean_dec_ref(v_extThms_4824_);
lean_dec_ref(v_facts_4823_);
lean_dec(v_nextIdx_4821_);
lean_dec_ref(v_internalizing_4820_);
lean_dec_ref(v_toProcess_4819_);
lean_dec_ref(v_indicesFound_4818_);
lean_dec_ref(v_appMap_4817_);
lean_dec_ref(v_congrTable_4816_);
lean_dec_ref(v_parents_4815_);
lean_dec_ref(v_exprs_4814_);
lean_dec_ref(v_enodeMap_4813_);
lean_dec(v_nextDeclIdx_4812_);
lean_dec_ref(v_kp_4798_);
lean_inc(v_a_4807_);
lean_inc_ref(v_a_4806_);
lean_inc(v_a_4805_);
lean_inc_ref(v_a_4804_);
lean_inc(v_a_4803_);
lean_inc_ref(v_a_4802_);
lean_inc(v_a_4801_);
lean_inc_ref(v_a_4800_);
lean_inc(v_a_4799_);
v___x_4874_ = lean_apply_11(v_kna_4797_, v_goal_4796_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_, lean_box(0));
return v___x_4874_;
}
}
}
else
{
lean_object* v___x_4876_; lean_object* v___x_4877_; 
lean_dec_ref(v_toGoalState_4809_);
lean_dec_ref(v_kp_4798_);
lean_dec_ref(v_kna_4797_);
lean_dec_ref(v_goal_4796_);
v___x_4876_ = ((lean_object*)(l_Lean_Meta_Grind_Action_intro___closed__0));
v___x_4877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4876_);
return v___x_4877_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertNext___boxed(lean_object* v_goal_4878_, lean_object* v_kna_4879_, lean_object* v_kp_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_){
_start:
{
lean_object* v_res_4891_; 
v_res_4891_ = l_Lean_Meta_Grind_Action_assertNext(v_goal_4878_, v_kna_4879_, v_kp_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_);
lean_dec(v_a_4889_);
lean_dec_ref(v_a_4888_);
lean_dec(v_a_4887_);
lean_dec_ref(v_a_4886_);
lean_dec(v_a_4885_);
lean_dec_ref(v_a_4884_);
lean_dec(v_a_4883_);
lean_dec_ref(v_a_4882_);
lean_dec(v_a_4881_);
return v_res_4891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg(lean_object* v_a_4892_, lean_object* v_kp_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_){
_start:
{
lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; 
v___x_4904_ = lean_unsigned_to_nat(1000000u);
v___x_4905_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_assertNext___boxed), 13, 0);
v___x_4906_ = l_Lean_Meta_Grind_Action_loop___redArg(v___x_4904_, v___x_4905_, v_a_4892_, v_kp_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_);
return v___x_4906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg___boxed(lean_object* v_a_4907_, lean_object* v_kp_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_){
_start:
{
lean_object* v_res_4919_; 
v_res_4919_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4907_, v_kp_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_);
lean_dec(v_a_4917_);
lean_dec_ref(v_a_4916_);
lean_dec(v_a_4915_);
lean_dec_ref(v_a_4914_);
lean_dec(v_a_4913_);
lean_dec_ref(v_a_4912_);
lean_dec(v_a_4911_);
lean_dec_ref(v_a_4910_);
lean_dec(v_a_4909_);
return v_res_4919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll(lean_object* v_a_4920_, lean_object* v_kna_4921_, lean_object* v_kp_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_){
_start:
{
lean_object* v___x_4933_; 
v___x_4933_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v_a_4920_, v_kp_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_);
return v___x_4933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_assertAll___boxed(lean_object* v_a_4934_, lean_object* v_kna_4935_, lean_object* v_kp_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_){
_start:
{
lean_object* v_res_4947_; 
v_res_4947_ = l_Lean_Meta_Grind_Action_assertAll(v_a_4934_, v_kna_4935_, v_kp_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_);
lean_dec(v_a_4945_);
lean_dec_ref(v_a_4944_);
lean_dec(v_a_4943_);
lean_dec_ref(v_a_4942_);
lean_dec(v_a_4941_);
lean_dec_ref(v_a_4940_);
lean_dec(v_a_4939_);
lean_dec_ref(v_a_4938_);
lean_dec(v_a_4937_);
lean_dec_ref(v_kna_4935_);
return v_res_4947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__0(lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_){
_start:
{
lean_object* v___x_4961_; 
v___x_4961_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_4948_, v___y_4950_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_, v___y_4959_);
return v___x_4961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__0___boxed(lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_){
_start:
{
lean_object* v_res_4975_; 
v_res_4975_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__0(v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_);
lean_dec(v___y_4973_);
lean_dec_ref(v___y_4972_);
lean_dec(v___y_4971_);
lean_dec_ref(v___y_4970_);
lean_dec(v___y_4969_);
lean_dec_ref(v___y_4968_);
lean_dec(v___y_4967_);
lean_dec_ref(v___y_4966_);
lean_dec(v___y_4965_);
lean_dec_ref(v___y_4963_);
return v_res_4975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__1(lean_object* v_a_4976_, lean_object* v___f_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_){
_start:
{
lean_object* v___x_4991_; 
v___x_4991_ = l_Lean_Meta_Grind_Action_andThen(v_a_4976_, v___f_4977_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_);
return v___x_4991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed(lean_object* v_a_4992_, lean_object* v___f_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_){
_start:
{
lean_object* v_res_5007_; 
v_res_5007_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__1(v_a_4992_, v___f_4993_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_);
lean_dec(v___y_5005_);
lean_dec_ref(v___y_5004_);
lean_dec(v___y_5003_);
lean_dec_ref(v___y_5002_);
lean_dec(v___y_5001_);
lean_dec_ref(v___y_5000_);
lean_dec(v___y_4999_);
lean_dec_ref(v___y_4998_);
lean_dec(v___y_4997_);
return v_res_5007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction(){
_start:
{
lean_object* v___f_5010_; lean_object* v___x_5011_; 
v___f_5010_ = ((lean_object*)(l_Lean_Meta_Grind_Solvers_mkAction___closed__0));
v___x_5011_ = l_Lean_Meta_Grind_Solvers_mkActionCore();
if (lean_obj_tag(v___x_5011_) == 0)
{
lean_object* v_a_5012_; lean_object* v___x_5014_; uint8_t v_isShared_5015_; uint8_t v_isSharedCheck_5020_; 
v_a_5012_ = lean_ctor_get(v___x_5011_, 0);
v_isSharedCheck_5020_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5020_ == 0)
{
v___x_5014_ = v___x_5011_;
v_isShared_5015_ = v_isSharedCheck_5020_;
goto v_resetjp_5013_;
}
else
{
lean_inc(v_a_5012_);
lean_dec(v___x_5011_);
v___x_5014_ = lean_box(0);
v_isShared_5015_ = v_isSharedCheck_5020_;
goto v_resetjp_5013_;
}
v_resetjp_5013_:
{
lean_object* v___f_5016_; lean_object* v___x_5018_; 
v___f_5016_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed), 15, 2);
lean_closure_set(v___f_5016_, 0, v_a_5012_);
lean_closure_set(v___f_5016_, 1, v___f_5010_);
if (v_isShared_5015_ == 0)
{
lean_ctor_set(v___x_5014_, 0, v___f_5016_);
v___x_5018_ = v___x_5014_;
goto v_reusejp_5017_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v___f_5016_);
v___x_5018_ = v_reuseFailAlloc_5019_;
goto v_reusejp_5017_;
}
v_reusejp_5017_:
{
return v___x_5018_;
}
}
}
else
{
return v___x_5011_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Solvers_mkAction___boxed(lean_object* v_a_5021_){
_start:
{
lean_object* v_res_5022_; 
v_res_5022_ = l_Lean_Meta_Grind_Solvers_mkAction();
return v_res_5022_;
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
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Anchor(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_MapIdx(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Tactic_Grind_Anchor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_MapIdx(builtin);
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
lean_object* initialize_Lean_Meta_Tactic_Grind_Anchor(uint8_t builtin);
lean_object* initialize_Init_Data_List_MapIdx(uint8_t builtin);
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
res = initialize_Lean_Meta_Tactic_Grind_Anchor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_MapIdx(builtin);
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
