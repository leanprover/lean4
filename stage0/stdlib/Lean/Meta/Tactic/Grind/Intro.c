// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Intro
// Imports: Init.Grind.Lemmas Lean.Meta.Tactic.Assert Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Cases Lean.Meta.Tactic.Grind.CasesMatch Lean.Meta.Tactic.Grind.Injection Lean.Meta.Tactic.Grind.Core Lean.Meta.Tactic.Grind.Combinators
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
static lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult___closed__1;
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_injection_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult___closed__8;
uint8_t l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
uint8_t l_String_anyAux___at_String_isNat___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_expandLet(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLet(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__3___closed__1;
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3;
static lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult___closed__9;
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_intros_go___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult___closed__4;
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLetFun(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult___closed__16;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__4;
lean_object* l_Lean_Meta_Grind_cheapCasesOnly___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_preprocessHypothesis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___spec__1;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Std_Queue_empty(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_intros_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__11___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__1;
uint8_t l_Lean_Meta_Grind_CasesTypes_isEagerSplit(lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_EMatch_instInhabitedState___spec__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_add(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_intros_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult___closed__19;
lean_object* l_Lean_Meta_Grind_addNewEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_Grind_closeGoal___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___boxed(lean_object**);
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Ext_instInhabitedExtTheorems___spec__1;
static lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult___closed__18;
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult___closed__11;
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_assertAll___closed__1;
lean_object* l_Lean_LocalDecl_value(lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_assertAt___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9___boxed(lean_object**);
lean_object* l_Lean_FVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Queue_dequeue_x3f___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_saveCases(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult___closed__20;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
lean_object* l_Lean_Meta_Grind_GrindTactic_iterate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__1;
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f(lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult___closed__2;
static lean_object* l_Lean_Meta_Grind_assertAt___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_assertAt___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_Split_instInhabitedState___spec__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__2;
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_String_findAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__3;
lean_object* l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAt___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__2(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_intros_go___lambda__3___closed__1;
static lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult___closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_intros_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult___closed__5;
lean_object* l_Lean_MVarId_intro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9___closed__1;
static lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult___closed__12;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_MVarId_byContra_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_instInhabitedEMatchTheorems___spec__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__3___closed__2;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__2;
static size_t l_Lean_Meta_Grind_instInhabitedIntroResult___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___boxed(lean_object**);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult___closed__3;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_assertAt___lambda__1___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__4___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Char_utf8Size(uint32_t);
static lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult___closed__10;
lean_object* l_Lean_Expr_letFun_x3f(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markAsPreMatchCond(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1;
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult___closed__14;
static lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult___closed__15;
lean_object* l_Lean_Expr_bindingInfo_x21(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__3;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_instInhabitedGoal___spec__1;
static lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult___closed__17;
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__4;
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__2;
x_2 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Queue_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__7() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__6;
x_2 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__4;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__7;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set_usize(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__2;
x_2 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_instInhabitedEMatchTheorems___spec__1;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__9;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__8;
x_4 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_EMatch_instInhabitedState___spec__1;
x_5 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Ext_instInhabitedExtTheorems___spec__1;
x_6 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_3);
lean_ctor_set(x_6, 4, x_2);
lean_ctor_set(x_6, 5, x_2);
lean_ctor_set(x_6, 6, x_4);
lean_ctor_set(x_6, 7, x_2);
lean_ctor_set(x_6, 8, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__11;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__12;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__2;
x_4 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__13;
x_5 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_Split_instInhabitedState___spec__1;
x_6 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
lean_ctor_set(x_6, 5, x_1);
lean_ctor_set(x_6, 6, x_1);
lean_ctor_set(x_6, 7, x_4);
lean_ctor_set(x_6, 8, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__8;
x_3 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__2;
x_4 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_3);
lean_ctor_set(x_4, 4, x_2);
lean_ctor_set(x_4, 5, x_2);
lean_ctor_set(x_4, 6, x_2);
lean_ctor_set(x_4, 7, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__8;
x_4 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__2;
x_5 = lean_unsigned_to_nat(0u);
x_6 = 0;
x_7 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___spec__1;
x_8 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_4);
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 4, x_4);
lean_ctor_set(x_8, 5, x_3);
lean_ctor_set(x_8, 6, x_3);
lean_ctor_set(x_8, 7, x_3);
lean_ctor_set(x_8, 8, x_3);
lean_ctor_set(x_8, 9, x_3);
lean_ctor_set(x_8, 10, x_1);
lean_ctor_set(x_8, 11, x_3);
lean_ctor_set(x_8, 12, x_3);
lean_ctor_set(x_8, 13, x_5);
lean_ctor_set(x_8, 14, x_2);
lean_ctor_set(x_8, 15, x_4);
lean_ctor_set(x_8, 16, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*17, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__15;
x_2 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__16;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Ext_instInhabitedExtTheorems___spec__1;
x_2 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__3;
x_3 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__2;
x_4 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_instInhabitedGoal___spec__1;
x_5 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__4;
x_6 = 0;
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__5;
x_9 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__8;
x_10 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__10;
x_11 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__14;
x_12 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__17;
x_13 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__18;
x_14 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_3);
lean_ctor_set(x_14, 3, x_3);
lean_ctor_set(x_14, 4, x_4);
lean_ctor_set(x_14, 5, x_3);
lean_ctor_set(x_14, 6, x_5);
lean_ctor_set(x_14, 7, x_7);
lean_ctor_set(x_14, 8, x_8);
lean_ctor_set(x_14, 9, x_9);
lean_ctor_set(x_14, 10, x_3);
lean_ctor_set(x_14, 11, x_10);
lean_ctor_set(x_14, 12, x_11);
lean_ctor_set(x_14, 13, x_12);
lean_ctor_set(x_14, 14, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*15, x_6);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__19;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instInhabitedIntroResult___closed__20;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("alreadyNorm", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = l_Lean_Expr_appArg(x_2, lean_box(0));
x_6 = l_Lean_Expr_appFnCleanup(x_2, lean_box(0));
x_7 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__4;
x_8 = l_Lean_Expr_isConstOf(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_5);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_preprocessHypothesis(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
lean_inc(x_1);
x_11 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_inc(x_1);
x_12 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f(x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_preprocess(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l_Lean_Meta_Grind_canon(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_Grind_shareCommon(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_box(0);
x_22 = 1;
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_22);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_box(0);
x_27 = 1;
x_28 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Lean_Meta_Grind_markAsPreMatchCond(x_1);
x_35 = l_Lean_Meta_Grind_preprocess(x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_35;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("h", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isProp(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__2;
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__2;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_8, 0);
lean_dec(x_18);
x_19 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__4;
lean_ctor_set(x_8, 0, x_19);
return x_8;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_dec(x_8);
x_21 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__4;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_8);
if (x_23 == 0)
{
return x_8;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__2(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 95;
x_3 = lean_uint32_dec_eq(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_string_utf8_extract(x_1, x_10, x_2);
x_12 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__3___closed__1;
x_13 = lean_string_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = l_Lean_Name_str___override(x_14, x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = lean_apply_6(x_3, x_17, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__4___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 95;
x_2 = l_Char_utf8Size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__4___closed__1;
x_12 = lean_nat_add(x_1, x_11);
x_13 = lean_string_utf8_extract(x_2, x_12, x_3);
lean_dec(x_12);
x_14 = lean_string_utf8_byte_size(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_14, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_String_anyAux___at_String_isNat___spec__1(x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__3(x_2, x_1, x_4, x_18, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_20 = lean_box(0);
x_21 = l_Lean_Name_str___override(x_20, x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_10);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_23 = lean_box(0);
x_24 = l_Lean_Name_str___override(x_23, x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__2___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___boxed), 7, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = lean_string_utf8_byte_size(x_8);
x_11 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1;
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_String_findAux(x_8, x_11, x_10, x_12);
x_14 = lean_nat_dec_lt(x_13, x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = l_Lean_Name_str___override(x_15, x_8);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__4(x_13, x_8, x_10, x_9, x_18, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_10);
lean_dec(x_13);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1(x_2, x_20, x_3, x_4, x_5, x_6, x_7);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__2___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__2(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
lean_inc(x_12);
lean_inc(x_1);
x_13 = lean_name_append_index_after(x_1, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_12, x_14);
lean_dec(x_12);
x_16 = lean_st_ref_get(x_3, x_11);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_18, 14);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(x_21, x_13);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_13);
lean_ctor_set(x_16, 0, x_23);
return x_16;
}
else
{
lean_object* x_24; 
lean_free_object(x_16);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_13);
x_2 = x_24;
x_11 = x_19;
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_ctor_get(x_26, 14);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(x_29, x_13);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_13);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_15);
lean_ctor_set(x_33, 1, x_13);
x_2 = x_33;
x_11 = x_27;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_st_ref_take(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_13, 14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_box(0);
lean_inc(x_1);
x_19 = l_Lean_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(x_17, x_1, x_18);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_16, 0);
lean_dec(x_21);
lean_ctor_set(x_16, 0, x_19);
x_22 = lean_st_ref_set(x_3, x_13, x_14);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_1);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_13, 14, x_28);
x_29 = lean_st_ref_set(x_3, x_13, x_14);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
x_35 = lean_ctor_get(x_13, 2);
x_36 = lean_ctor_get(x_13, 3);
x_37 = lean_ctor_get(x_13, 4);
x_38 = lean_ctor_get(x_13, 5);
x_39 = lean_ctor_get(x_13, 6);
x_40 = lean_ctor_get_uint8(x_13, sizeof(void*)*15);
x_41 = lean_ctor_get(x_13, 7);
x_42 = lean_ctor_get(x_13, 8);
x_43 = lean_ctor_get(x_13, 9);
x_44 = lean_ctor_get(x_13, 10);
x_45 = lean_ctor_get(x_13, 11);
x_46 = lean_ctor_get(x_13, 12);
x_47 = lean_ctor_get(x_13, 13);
x_48 = lean_ctor_get(x_13, 14);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_box(0);
lean_inc(x_1);
x_51 = l_Lean_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(x_49, x_1, x_50);
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_53 = x_48;
} else {
 lean_dec_ref(x_48);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_55, 0, x_33);
lean_ctor_set(x_55, 1, x_34);
lean_ctor_set(x_55, 2, x_35);
lean_ctor_set(x_55, 3, x_36);
lean_ctor_set(x_55, 4, x_37);
lean_ctor_set(x_55, 5, x_38);
lean_ctor_set(x_55, 6, x_39);
lean_ctor_set(x_55, 7, x_41);
lean_ctor_set(x_55, 8, x_42);
lean_ctor_set(x_55, 9, x_43);
lean_ctor_set(x_55, 10, x_44);
lean_ctor_set(x_55, 11, x_45);
lean_ctor_set(x_55, 12, x_46);
lean_ctor_set(x_55, 13, x_47);
lean_ctor_set(x_55, 14, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*15, x_40);
x_56 = lean_st_ref_set(x_3, x_55, x_14);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_1);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__1___boxed), 11, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_st_ref_get(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__2___closed__1;
x_17 = lean_ctor_get(x_14, 14);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(x_18, x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_apply_11(x_16, x_2, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_21;
}
else
{
lean_object* x_22; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_22 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(x_2, x_1, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_4, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_26, 14);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__1(x_30, x_23);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_86; 
x_86 = lean_unsigned_to_nat(1u);
x_32 = x_86;
goto block_85;
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_31, 0);
lean_inc(x_87);
lean_dec(x_31);
x_32 = x_87;
goto block_85;
}
block_85:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
if (lean_is_scalar(x_28)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_28;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_2);
lean_inc(x_23);
x_34 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___spec__1(x_23, x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_27);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_st_ref_take(x_4, x_36);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 14);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_40, 14);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_41, 1);
x_47 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__4(x_46, x_23, x_37);
lean_ctor_set(x_41, 1, x_47);
x_48 = lean_st_ref_set(x_4, x_40, x_42);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_box(0);
x_51 = lean_apply_11(x_16, x_38, x_50, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_49);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_41, 0);
x_53 = lean_ctor_get(x_41, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_41);
x_54 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__4(x_53, x_23, x_37);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_40, 14, x_55);
x_56 = lean_st_ref_set(x_4, x_40, x_42);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_box(0);
x_59 = lean_apply_11(x_16, x_38, x_58, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_57);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_60 = lean_ctor_get(x_40, 0);
x_61 = lean_ctor_get(x_40, 1);
x_62 = lean_ctor_get(x_40, 2);
x_63 = lean_ctor_get(x_40, 3);
x_64 = lean_ctor_get(x_40, 4);
x_65 = lean_ctor_get(x_40, 5);
x_66 = lean_ctor_get(x_40, 6);
x_67 = lean_ctor_get_uint8(x_40, sizeof(void*)*15);
x_68 = lean_ctor_get(x_40, 7);
x_69 = lean_ctor_get(x_40, 8);
x_70 = lean_ctor_get(x_40, 9);
x_71 = lean_ctor_get(x_40, 10);
x_72 = lean_ctor_get(x_40, 11);
x_73 = lean_ctor_get(x_40, 12);
x_74 = lean_ctor_get(x_40, 13);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_40);
x_75 = lean_ctor_get(x_41, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_41, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_77 = x_41;
} else {
 lean_dec_ref(x_41);
 x_77 = lean_box(0);
}
x_78 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__4(x_76, x_23, x_37);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_80, 0, x_60);
lean_ctor_set(x_80, 1, x_61);
lean_ctor_set(x_80, 2, x_62);
lean_ctor_set(x_80, 3, x_63);
lean_ctor_set(x_80, 4, x_64);
lean_ctor_set(x_80, 5, x_65);
lean_ctor_set(x_80, 6, x_66);
lean_ctor_set(x_80, 7, x_68);
lean_ctor_set(x_80, 8, x_69);
lean_ctor_set(x_80, 9, x_70);
lean_ctor_set(x_80, 10, x_71);
lean_ctor_set(x_80, 11, x_72);
lean_ctor_set(x_80, 12, x_73);
lean_ctor_set(x_80, 13, x_74);
lean_ctor_set(x_80, 14, x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*15, x_67);
x_81 = lean_st_ref_set(x_4, x_80, x_42);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_box(0);
x_84 = lean_apply_11(x_16, x_38, x_83, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_82);
return x_84;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_22);
if (x_88 == 0)
{
return x_22;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_22, 0);
x_90 = lean_ctor_get(x_22, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_22);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Name_hasMacroScopes(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__2(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_erase_macro_scopes(x_2);
x_17 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__2;
x_18 = lean_name_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__3___closed__2;
x_20 = lean_name_eq(x_16, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__2(x_1, x_16, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_22;
}
else
{
lean_object* x_23; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_23 = l_Lean_Meta_isProp(x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_box(0);
x_28 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__2(x_1, x_16, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_26);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_16);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__4;
x_31 = lean_box(0);
x_32 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__2(x_1, x_30, x_31, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
lean_object* x_37; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_37 = l_Lean_Meta_isProp(x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_box(0);
x_42 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__2(x_1, x_16, x_41, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_16);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_dec(x_37);
x_44 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__4;
x_45 = lean_box(0);
x_46 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__2(x_1, x_44, x_45, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_43);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_37);
if (x_47 == 0)
{
return x_37;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_37, 0);
x_49 = lean_ctor_get(x_37, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_37);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Meta_Grind_getConfig___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*6 + 11);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_box(0);
x_21 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__3(x_2, x_1, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_13 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_2, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_MVarId_intro(x_19, x_14, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_st_ref_take(x_2, x_22);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
lean_ctor_set(x_26, 0, x_24);
x_30 = lean_st_ref_set(x_2, x_26, x_27);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_23);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_35 = lean_ctor_get(x_26, 1);
x_36 = lean_ctor_get(x_26, 2);
x_37 = lean_ctor_get(x_26, 3);
x_38 = lean_ctor_get(x_26, 4);
x_39 = lean_ctor_get(x_26, 5);
x_40 = lean_ctor_get(x_26, 6);
x_41 = lean_ctor_get_uint8(x_26, sizeof(void*)*15);
x_42 = lean_ctor_get(x_26, 7);
x_43 = lean_ctor_get(x_26, 8);
x_44 = lean_ctor_get(x_26, 9);
x_45 = lean_ctor_get(x_26, 10);
x_46 = lean_ctor_get(x_26, 11);
x_47 = lean_ctor_get(x_26, 12);
x_48 = lean_ctor_get(x_26, 13);
x_49 = lean_ctor_get(x_26, 14);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_26);
x_50 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_50, 0, x_24);
lean_ctor_set(x_50, 1, x_35);
lean_ctor_set(x_50, 2, x_36);
lean_ctor_set(x_50, 3, x_37);
lean_ctor_set(x_50, 4, x_38);
lean_ctor_set(x_50, 5, x_39);
lean_ctor_set(x_50, 6, x_40);
lean_ctor_set(x_50, 7, x_42);
lean_ctor_set(x_50, 8, x_43);
lean_ctor_set(x_50, 9, x_44);
lean_ctor_set(x_50, 10, x_45);
lean_ctor_set(x_50, 11, x_46);
lean_ctor_set(x_50, 12, x_47);
lean_ctor_set(x_50, 13, x_48);
lean_ctor_set(x_50, 14, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*15, x_41);
x_51 = lean_st_ref_set(x_2, x_50, x_27);
lean_dec(x_2);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_23);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_20);
if (x_55 == 0)
{
return x_20;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_20, 0);
x_57 = lean_ctor_get(x_20, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_20);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_13);
if (x_59 == 0)
{
return x_13;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_13, 0);
x_61 = lean_ctor_get(x_13, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_13);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___lambda__1), 10, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`grind` internal error, binder expected", 39, 39);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_MVarId_getType(x_14, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1;
switch (lean_obj_tag(x_16)) {
case 7:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
lean_ctor_set(x_10, 1, x_20);
lean_ctor_set(x_10, 0, x_19);
x_21 = lean_apply_10(x_18, x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
return x_21;
}
case 8:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_dec(x_16);
lean_ctor_set(x_10, 1, x_23);
lean_ctor_set(x_10, 0, x_22);
x_24 = lean_apply_10(x_18, x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
return x_24;
}
default: 
{
lean_object* x_25; 
lean_free_object(x_10);
x_25 = l_Lean_Expr_letFun_x3f(x_16);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__3;
x_27 = l_Lean_throwError___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___spec__1(x_26, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_33, 0);
x_37 = lean_ctor_get(x_33, 1);
lean_dec(x_37);
lean_ctor_set(x_33, 1, x_36);
lean_ctor_set(x_33, 0, x_34);
x_38 = lean_apply_10(x_18, x_33, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_apply_10(x_18, x_40, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
return x_41;
}
}
}
}
}
else
{
uint8_t x_42; 
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_15);
if (x_42 == 0)
{
return x_15;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_15, 0);
x_44 = lean_ctor_get(x_15, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_15);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_10, 0);
x_47 = lean_ctor_get(x_10, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_10);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_MVarId_getType(x_48, x_5, x_6, x_7, x_8, x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1;
switch (lean_obj_tag(x_50)) {
case 7:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_apply_10(x_52, x_55, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_51);
return x_56;
}
case 8:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_50, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
lean_dec(x_50);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_apply_10(x_52, x_59, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_51);
return x_60;
}
default: 
{
lean_object* x_61; 
x_61 = l_Lean_Expr_letFun_x3f(x_50);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__3;
x_63 = l_Lean_throwError___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___spec__1(x_62, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_51);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_ctor_get(x_61, 0);
lean_inc(x_68);
lean_dec(x_61);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
x_74 = lean_apply_10(x_52, x_73, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_51);
return x_74;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = lean_ctor_get(x_49, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_49, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_77 = x_49;
} else {
 lean_dec_ref(x_49);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(x_1, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1___rarg), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_inc(x_8);
x_10 = l_Lean_Name_num___override(x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_9, x_11);
lean_dec(x_9);
lean_ctor_set(x_5, 1, x_12);
x_13 = lean_st_ref_take(x_1, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 2);
lean_dec(x_17);
lean_ctor_set(x_14, 2, x_5);
x_18 = lean_st_ref_set(x_1, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_10);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
x_25 = lean_ctor_get(x_14, 3);
x_26 = lean_ctor_get(x_14, 4);
x_27 = lean_ctor_get(x_14, 5);
x_28 = lean_ctor_get(x_14, 6);
x_29 = lean_ctor_get(x_14, 7);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_30 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_5);
lean_ctor_set(x_30, 3, x_25);
lean_ctor_set(x_30, 4, x_26);
lean_ctor_set(x_30, 5, x_27);
lean_ctor_set(x_30, 6, x_28);
lean_ctor_set(x_30, 7, x_29);
x_31 = lean_st_ref_set(x_1, x_30, x_15);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_10);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_35 = lean_ctor_get(x_5, 0);
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_5);
lean_inc(x_36);
lean_inc(x_35);
x_37 = l_Lean_Name_num___override(x_35, x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_36, x_38);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_st_ref_take(x_1, x_6);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_42, 4);
lean_inc(x_47);
x_48 = lean_ctor_get(x_42, 5);
lean_inc(x_48);
x_49 = lean_ctor_get(x_42, 6);
lean_inc(x_49);
x_50 = lean_ctor_get(x_42, 7);
lean_inc(x_50);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 lean_ctor_release(x_42, 4);
 lean_ctor_release(x_42, 5);
 lean_ctor_release(x_42, 6);
 lean_ctor_release(x_42, 7);
 x_51 = x_42;
} else {
 lean_dec_ref(x_42);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 8, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_44);
lean_ctor_set(x_52, 1, x_45);
lean_ctor_set(x_52, 2, x_40);
lean_ctor_set(x_52, 3, x_46);
lean_ctor_set(x_52, 4, x_47);
lean_ctor_set(x_52, 5, x_48);
lean_ctor_set(x_52, 6, x_49);
lean_ctor_set(x_52, 7, x_50);
x_53 = lean_st_ref_set(x_1, x_52, x_43);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_37);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3___rarg___boxed), 2, 0);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3___rarg(x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_mk_ref(x_1, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_FVarId_getDecl(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_LocalDecl_type(x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_13);
x_14 = l_Lean_Meta_isProp(x_13, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_8);
lean_inc(x_1);
x_18 = l_Lean_FVarId_getDecl(x_1, x_8, x_9, x_10, x_11, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_LocalDecl_value(x_19);
lean_dec(x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_preprocessHypothesis(x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_1);
x_25 = l_Lean_Expr_fvar___override(x_1);
x_26 = l_Lean_Meta_Grind_shareCommon(x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_23);
x_30 = l_Lean_Meta_Simp_Result_getProof(x_23, x_8, x_9, x_10, x_11, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
lean_dec(x_23);
lean_inc(x_4);
x_34 = l_Lean_Meta_Grind_addNewEq(x_28, x_33, x_31, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_get(x_4, x_35);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_ctor_set_tag(x_26, 3);
lean_ctor_set(x_26, 1, x_38);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_36, 0, x_26);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_36);
lean_ctor_set_tag(x_26, 3);
lean_ctor_set(x_26, 1, x_39);
lean_ctor_set(x_26, 0, x_1);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_26);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_free_object(x_26);
lean_dec(x_4);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
return x_34;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_34, 0);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_34);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_free_object(x_26);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_30);
if (x_46 == 0)
{
return x_30;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_30, 0);
x_48 = lean_ctor_get(x_30, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_30);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_26, 0);
x_51 = lean_ctor_get(x_26, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_23);
x_52 = l_Lean_Meta_Simp_Result_getProof(x_23, x_8, x_9, x_10, x_11, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_23, 0);
lean_inc(x_55);
lean_dec(x_23);
lean_inc(x_4);
x_56 = l_Lean_Meta_Grind_addNewEq(x_50, x_55, x_53, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_st_ref_get(x_4, x_57);
lean_dec(x_4);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
x_62 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_62, 0, x_1);
lean_ctor_set(x_62, 1, x_59);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_4);
lean_dec(x_1);
x_64 = lean_ctor_get(x_56, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_56, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_66 = x_56;
} else {
 lean_dec_ref(x_56);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_50);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_68 = lean_ctor_get(x_52, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_52, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_70 = x_52;
} else {
 lean_dec_ref(x_52);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_22);
if (x_72 == 0)
{
return x_22;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_22, 0);
x_74 = lean_ctor_get(x_22, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_22);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_18);
if (x_76 == 0)
{
return x_18;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_18, 0);
x_78 = lean_ctor_get(x_18, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_18);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_2);
x_80 = lean_ctor_get(x_14, 1);
lean_inc(x_80);
lean_dec(x_14);
x_81 = lean_st_ref_get(x_4, x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__4;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_13);
x_85 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(x_84, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_83);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_ctor_get(x_82, 0);
lean_inc(x_88);
lean_dec(x_82);
x_89 = l_Lean_Expr_fvar___override(x_1);
x_90 = l_Lean_MVarId_assert(x_88, x_86, x_13, x_89, x_8, x_9, x_10, x_11, x_87);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_st_ref_get(x_4, x_92);
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_93, 0);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_95, 0);
lean_dec(x_97);
lean_ctor_set(x_95, 0, x_91);
x_98 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_93, 0, x_98);
return x_93;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_99 = lean_ctor_get(x_95, 1);
x_100 = lean_ctor_get(x_95, 2);
x_101 = lean_ctor_get(x_95, 3);
x_102 = lean_ctor_get(x_95, 4);
x_103 = lean_ctor_get(x_95, 5);
x_104 = lean_ctor_get(x_95, 6);
x_105 = lean_ctor_get_uint8(x_95, sizeof(void*)*15);
x_106 = lean_ctor_get(x_95, 7);
x_107 = lean_ctor_get(x_95, 8);
x_108 = lean_ctor_get(x_95, 9);
x_109 = lean_ctor_get(x_95, 10);
x_110 = lean_ctor_get(x_95, 11);
x_111 = lean_ctor_get(x_95, 12);
x_112 = lean_ctor_get(x_95, 13);
x_113 = lean_ctor_get(x_95, 14);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_95);
x_114 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_114, 0, x_91);
lean_ctor_set(x_114, 1, x_99);
lean_ctor_set(x_114, 2, x_100);
lean_ctor_set(x_114, 3, x_101);
lean_ctor_set(x_114, 4, x_102);
lean_ctor_set(x_114, 5, x_103);
lean_ctor_set(x_114, 6, x_104);
lean_ctor_set(x_114, 7, x_106);
lean_ctor_set(x_114, 8, x_107);
lean_ctor_set(x_114, 9, x_108);
lean_ctor_set(x_114, 10, x_109);
lean_ctor_set(x_114, 11, x_110);
lean_ctor_set(x_114, 12, x_111);
lean_ctor_set(x_114, 13, x_112);
lean_ctor_set(x_114, 14, x_113);
lean_ctor_set_uint8(x_114, sizeof(void*)*15, x_105);
x_115 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_93, 0, x_115);
return x_93;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_116 = lean_ctor_get(x_93, 0);
x_117 = lean_ctor_get(x_93, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_93);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_116, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_116, 3);
lean_inc(x_120);
x_121 = lean_ctor_get(x_116, 4);
lean_inc(x_121);
x_122 = lean_ctor_get(x_116, 5);
lean_inc(x_122);
x_123 = lean_ctor_get(x_116, 6);
lean_inc(x_123);
x_124 = lean_ctor_get_uint8(x_116, sizeof(void*)*15);
x_125 = lean_ctor_get(x_116, 7);
lean_inc(x_125);
x_126 = lean_ctor_get(x_116, 8);
lean_inc(x_126);
x_127 = lean_ctor_get(x_116, 9);
lean_inc(x_127);
x_128 = lean_ctor_get(x_116, 10);
lean_inc(x_128);
x_129 = lean_ctor_get(x_116, 11);
lean_inc(x_129);
x_130 = lean_ctor_get(x_116, 12);
lean_inc(x_130);
x_131 = lean_ctor_get(x_116, 13);
lean_inc(x_131);
x_132 = lean_ctor_get(x_116, 14);
lean_inc(x_132);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 lean_ctor_release(x_116, 2);
 lean_ctor_release(x_116, 3);
 lean_ctor_release(x_116, 4);
 lean_ctor_release(x_116, 5);
 lean_ctor_release(x_116, 6);
 lean_ctor_release(x_116, 7);
 lean_ctor_release(x_116, 8);
 lean_ctor_release(x_116, 9);
 lean_ctor_release(x_116, 10);
 lean_ctor_release(x_116, 11);
 lean_ctor_release(x_116, 12);
 lean_ctor_release(x_116, 13);
 lean_ctor_release(x_116, 14);
 x_133 = x_116;
} else {
 lean_dec_ref(x_116);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(0, 15, 1);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_91);
lean_ctor_set(x_134, 1, x_118);
lean_ctor_set(x_134, 2, x_119);
lean_ctor_set(x_134, 3, x_120);
lean_ctor_set(x_134, 4, x_121);
lean_ctor_set(x_134, 5, x_122);
lean_ctor_set(x_134, 6, x_123);
lean_ctor_set(x_134, 7, x_125);
lean_ctor_set(x_134, 8, x_126);
lean_ctor_set(x_134, 9, x_127);
lean_ctor_set(x_134, 10, x_128);
lean_ctor_set(x_134, 11, x_129);
lean_ctor_set(x_134, 12, x_130);
lean_ctor_set(x_134, 13, x_131);
lean_ctor_set(x_134, 14, x_132);
lean_ctor_set_uint8(x_134, sizeof(void*)*15, x_124);
x_135 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_117);
return x_136;
}
}
else
{
uint8_t x_137; 
lean_dec(x_4);
x_137 = !lean_is_exclusive(x_90);
if (x_137 == 0)
{
return x_90;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_90, 0);
x_139 = lean_ctor_get(x_90, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_90);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_82);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
x_141 = !lean_is_exclusive(x_85);
if (x_141 == 0)
{
return x_85;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_85, 0);
x_143 = lean_ctor_get(x_85, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_85);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_145 = !lean_is_exclusive(x_14);
if (x_145 == 0)
{
return x_14;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_14, 0);
x_147 = lean_ctor_get(x_14, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_14);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_getTag(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_inc(x_9);
x_14 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_4, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_15);
x_17 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_closeGoal___spec__2(x_2, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_5, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Expr_mvarId_x21(x_15);
lean_dec(x_15);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
lean_ctor_set(x_20, 0, x_22);
x_25 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(x_20, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_26 = lean_ctor_get(x_20, 1);
x_27 = lean_ctor_get(x_20, 2);
x_28 = lean_ctor_get(x_20, 3);
x_29 = lean_ctor_get(x_20, 4);
x_30 = lean_ctor_get(x_20, 5);
x_31 = lean_ctor_get(x_20, 6);
x_32 = lean_ctor_get_uint8(x_20, sizeof(void*)*15);
x_33 = lean_ctor_get(x_20, 7);
x_34 = lean_ctor_get(x_20, 8);
x_35 = lean_ctor_get(x_20, 9);
x_36 = lean_ctor_get(x_20, 10);
x_37 = lean_ctor_get(x_20, 11);
x_38 = lean_ctor_get(x_20, 12);
x_39 = lean_ctor_get(x_20, 13);
x_40 = lean_ctor_get(x_20, 14);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_41 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_41, 0, x_22);
lean_ctor_set(x_41, 1, x_26);
lean_ctor_set(x_41, 2, x_27);
lean_ctor_set(x_41, 3, x_28);
lean_ctor_set(x_41, 4, x_29);
lean_ctor_set(x_41, 5, x_30);
lean_ctor_set(x_41, 6, x_31);
lean_ctor_set(x_41, 7, x_33);
lean_ctor_set(x_41, 8, x_34);
lean_ctor_set(x_41, 9, x_35);
lean_ctor_set(x_41, 10, x_36);
lean_ctor_set(x_41, 11, x_37);
lean_ctor_set(x_41, 12, x_38);
lean_ctor_set(x_41, 13, x_39);
lean_ctor_set(x_41, 14, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*15, x_32);
x_42 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(x_41, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_11 = 0;
x_12 = 1;
x_13 = 1;
x_14 = l_Lean_Meta_mkLambdaFVars(x_1, x_2, x_11, x_12, x_11, x_13, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_closeGoal___spec__2(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_st_ref_get(x_5, x_16);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 1, x_20);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_18, 0, x_14);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_ctor_get(x_20, 2);
x_25 = lean_ctor_get(x_20, 3);
x_26 = lean_ctor_get(x_20, 4);
x_27 = lean_ctor_get(x_20, 5);
x_28 = lean_ctor_get(x_20, 6);
x_29 = lean_ctor_get_uint8(x_20, sizeof(void*)*15);
x_30 = lean_ctor_get(x_20, 7);
x_31 = lean_ctor_get(x_20, 8);
x_32 = lean_ctor_get(x_20, 9);
x_33 = lean_ctor_get(x_20, 10);
x_34 = lean_ctor_get(x_20, 11);
x_35 = lean_ctor_get(x_20, 12);
x_36 = lean_ctor_get(x_20, 13);
x_37 = lean_ctor_get(x_20, 14);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_20);
x_38 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_23);
lean_ctor_set(x_38, 2, x_24);
lean_ctor_set(x_38, 3, x_25);
lean_ctor_set(x_38, 4, x_26);
lean_ctor_set(x_38, 5, x_27);
lean_ctor_set(x_38, 6, x_28);
lean_ctor_set(x_38, 7, x_30);
lean_ctor_set(x_38, 8, x_31);
lean_ctor_set(x_38, 9, x_32);
lean_ctor_set(x_38, 10, x_33);
lean_ctor_set(x_38, 11, x_34);
lean_ctor_set(x_38, 12, x_35);
lean_ctor_set(x_38, 13, x_36);
lean_ctor_set(x_38, 14, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*15, x_29);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 1, x_38);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_18, 0, x_14);
return x_18;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_39 = lean_ctor_get(x_18, 0);
x_40 = lean_ctor_get(x_18, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_18);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_39, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_39, 4);
lean_inc(x_44);
x_45 = lean_ctor_get(x_39, 5);
lean_inc(x_45);
x_46 = lean_ctor_get(x_39, 6);
lean_inc(x_46);
x_47 = lean_ctor_get_uint8(x_39, sizeof(void*)*15);
x_48 = lean_ctor_get(x_39, 7);
lean_inc(x_48);
x_49 = lean_ctor_get(x_39, 8);
lean_inc(x_49);
x_50 = lean_ctor_get(x_39, 9);
lean_inc(x_50);
x_51 = lean_ctor_get(x_39, 10);
lean_inc(x_51);
x_52 = lean_ctor_get(x_39, 11);
lean_inc(x_52);
x_53 = lean_ctor_get(x_39, 12);
lean_inc(x_53);
x_54 = lean_ctor_get(x_39, 13);
lean_inc(x_54);
x_55 = lean_ctor_get(x_39, 14);
lean_inc(x_55);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 lean_ctor_release(x_39, 7);
 lean_ctor_release(x_39, 8);
 lean_ctor_release(x_39, 9);
 lean_ctor_release(x_39, 10);
 lean_ctor_release(x_39, 11);
 lean_ctor_release(x_39, 12);
 lean_ctor_release(x_39, 13);
 lean_ctor_release(x_39, 14);
 x_56 = x_39;
} else {
 lean_dec_ref(x_39);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 15, 1);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_2);
lean_ctor_set(x_57, 1, x_41);
lean_ctor_set(x_57, 2, x_42);
lean_ctor_set(x_57, 3, x_43);
lean_ctor_set(x_57, 4, x_44);
lean_ctor_set(x_57, 5, x_45);
lean_ctor_set(x_57, 6, x_46);
lean_ctor_set(x_57, 7, x_48);
lean_ctor_set(x_57, 8, x_49);
lean_ctor_set(x_57, 9, x_50);
lean_ctor_set(x_57, 10, x_51);
lean_ctor_set(x_57, 11, x_52);
lean_ctor_set(x_57, 12, x_53);
lean_ctor_set(x_57, 13, x_54);
lean_ctor_set(x_57, 14, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*15, x_47);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 1, x_57);
lean_ctor_set(x_14, 0, x_3);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_14);
lean_ctor_set(x_58, 1, x_40);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_59 = lean_ctor_get(x_14, 1);
lean_inc(x_59);
lean_dec(x_14);
x_60 = lean_st_ref_get(x_5, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_61, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_61, 3);
lean_inc(x_66);
x_67 = lean_ctor_get(x_61, 4);
lean_inc(x_67);
x_68 = lean_ctor_get(x_61, 5);
lean_inc(x_68);
x_69 = lean_ctor_get(x_61, 6);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_61, sizeof(void*)*15);
x_71 = lean_ctor_get(x_61, 7);
lean_inc(x_71);
x_72 = lean_ctor_get(x_61, 8);
lean_inc(x_72);
x_73 = lean_ctor_get(x_61, 9);
lean_inc(x_73);
x_74 = lean_ctor_get(x_61, 10);
lean_inc(x_74);
x_75 = lean_ctor_get(x_61, 11);
lean_inc(x_75);
x_76 = lean_ctor_get(x_61, 12);
lean_inc(x_76);
x_77 = lean_ctor_get(x_61, 13);
lean_inc(x_77);
x_78 = lean_ctor_get(x_61, 14);
lean_inc(x_78);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 lean_ctor_release(x_61, 2);
 lean_ctor_release(x_61, 3);
 lean_ctor_release(x_61, 4);
 lean_ctor_release(x_61, 5);
 lean_ctor_release(x_61, 6);
 lean_ctor_release(x_61, 7);
 lean_ctor_release(x_61, 8);
 lean_ctor_release(x_61, 9);
 lean_ctor_release(x_61, 10);
 lean_ctor_release(x_61, 11);
 lean_ctor_release(x_61, 12);
 lean_ctor_release(x_61, 13);
 lean_ctor_release(x_61, 14);
 x_79 = x_61;
} else {
 lean_dec_ref(x_61);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 15, 1);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_2);
lean_ctor_set(x_80, 1, x_64);
lean_ctor_set(x_80, 2, x_65);
lean_ctor_set(x_80, 3, x_66);
lean_ctor_set(x_80, 4, x_67);
lean_ctor_set(x_80, 5, x_68);
lean_ctor_set(x_80, 6, x_69);
lean_ctor_set(x_80, 7, x_71);
lean_ctor_set(x_80, 8, x_72);
lean_ctor_set(x_80, 9, x_73);
lean_ctor_set(x_80, 10, x_74);
lean_ctor_set(x_80, 11, x_75);
lean_ctor_set(x_80, 12, x_76);
lean_ctor_set(x_80, 13, x_77);
lean_ctor_set(x_80, 14, x_78);
lean_ctor_set_uint8(x_80, sizeof(void*)*15, x_70);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_3);
lean_ctor_set(x_81, 1, x_80);
if (lean_is_scalar(x_63)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_63;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_62);
return x_82;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("intro_with_eq'", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_inc(x_2);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
x_21 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__2;
x_22 = l_Lean_Expr_const___override(x_21, x_20);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_2);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_array_mk(x_27);
x_29 = l_Lean_mkAppN(x_22, x_28);
lean_dec(x_28);
x_30 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_closeGoal___spec__2(x_7, x_29, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_30, 1);
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_st_ref_get(x_11, x_32);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_8);
lean_ctor_set_tag(x_30, 1);
lean_ctor_set(x_30, 1, x_36);
lean_ctor_set(x_30, 0, x_9);
lean_ctor_set(x_34, 0, x_30);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_39 = lean_ctor_get(x_36, 1);
x_40 = lean_ctor_get(x_36, 2);
x_41 = lean_ctor_get(x_36, 3);
x_42 = lean_ctor_get(x_36, 4);
x_43 = lean_ctor_get(x_36, 5);
x_44 = lean_ctor_get(x_36, 6);
x_45 = lean_ctor_get_uint8(x_36, sizeof(void*)*15);
x_46 = lean_ctor_get(x_36, 7);
x_47 = lean_ctor_get(x_36, 8);
x_48 = lean_ctor_get(x_36, 9);
x_49 = lean_ctor_get(x_36, 10);
x_50 = lean_ctor_get(x_36, 11);
x_51 = lean_ctor_get(x_36, 12);
x_52 = lean_ctor_get(x_36, 13);
x_53 = lean_ctor_get(x_36, 14);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_36);
x_54 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_54, 0, x_8);
lean_ctor_set(x_54, 1, x_39);
lean_ctor_set(x_54, 2, x_40);
lean_ctor_set(x_54, 3, x_41);
lean_ctor_set(x_54, 4, x_42);
lean_ctor_set(x_54, 5, x_43);
lean_ctor_set(x_54, 6, x_44);
lean_ctor_set(x_54, 7, x_46);
lean_ctor_set(x_54, 8, x_47);
lean_ctor_set(x_54, 9, x_48);
lean_ctor_set(x_54, 10, x_49);
lean_ctor_set(x_54, 11, x_50);
lean_ctor_set(x_54, 12, x_51);
lean_ctor_set(x_54, 13, x_52);
lean_ctor_set(x_54, 14, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*15, x_45);
lean_ctor_set_tag(x_30, 1);
lean_ctor_set(x_30, 1, x_54);
lean_ctor_set(x_30, 0, x_9);
lean_ctor_set(x_34, 0, x_30);
return x_34;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_55 = lean_ctor_get(x_34, 0);
x_56 = lean_ctor_get(x_34, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_34);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_55, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_55, 4);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 5);
lean_inc(x_61);
x_62 = lean_ctor_get(x_55, 6);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_55, sizeof(void*)*15);
x_64 = lean_ctor_get(x_55, 7);
lean_inc(x_64);
x_65 = lean_ctor_get(x_55, 8);
lean_inc(x_65);
x_66 = lean_ctor_get(x_55, 9);
lean_inc(x_66);
x_67 = lean_ctor_get(x_55, 10);
lean_inc(x_67);
x_68 = lean_ctor_get(x_55, 11);
lean_inc(x_68);
x_69 = lean_ctor_get(x_55, 12);
lean_inc(x_69);
x_70 = lean_ctor_get(x_55, 13);
lean_inc(x_70);
x_71 = lean_ctor_get(x_55, 14);
lean_inc(x_71);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 lean_ctor_release(x_55, 4);
 lean_ctor_release(x_55, 5);
 lean_ctor_release(x_55, 6);
 lean_ctor_release(x_55, 7);
 lean_ctor_release(x_55, 8);
 lean_ctor_release(x_55, 9);
 lean_ctor_release(x_55, 10);
 lean_ctor_release(x_55, 11);
 lean_ctor_release(x_55, 12);
 lean_ctor_release(x_55, 13);
 lean_ctor_release(x_55, 14);
 x_72 = x_55;
} else {
 lean_dec_ref(x_55);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 15, 1);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_8);
lean_ctor_set(x_73, 1, x_57);
lean_ctor_set(x_73, 2, x_58);
lean_ctor_set(x_73, 3, x_59);
lean_ctor_set(x_73, 4, x_60);
lean_ctor_set(x_73, 5, x_61);
lean_ctor_set(x_73, 6, x_62);
lean_ctor_set(x_73, 7, x_64);
lean_ctor_set(x_73, 8, x_65);
lean_ctor_set(x_73, 9, x_66);
lean_ctor_set(x_73, 10, x_67);
lean_ctor_set(x_73, 11, x_68);
lean_ctor_set(x_73, 12, x_69);
lean_ctor_set(x_73, 13, x_70);
lean_ctor_set(x_73, 14, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*15, x_63);
lean_ctor_set_tag(x_30, 1);
lean_ctor_set(x_30, 1, x_73);
lean_ctor_set(x_30, 0, x_9);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_30);
lean_ctor_set(x_74, 1, x_56);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_75 = lean_ctor_get(x_30, 1);
lean_inc(x_75);
lean_dec(x_30);
x_76 = lean_st_ref_get(x_11, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_77, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_77, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 4);
lean_inc(x_83);
x_84 = lean_ctor_get(x_77, 5);
lean_inc(x_84);
x_85 = lean_ctor_get(x_77, 6);
lean_inc(x_85);
x_86 = lean_ctor_get_uint8(x_77, sizeof(void*)*15);
x_87 = lean_ctor_get(x_77, 7);
lean_inc(x_87);
x_88 = lean_ctor_get(x_77, 8);
lean_inc(x_88);
x_89 = lean_ctor_get(x_77, 9);
lean_inc(x_89);
x_90 = lean_ctor_get(x_77, 10);
lean_inc(x_90);
x_91 = lean_ctor_get(x_77, 11);
lean_inc(x_91);
x_92 = lean_ctor_get(x_77, 12);
lean_inc(x_92);
x_93 = lean_ctor_get(x_77, 13);
lean_inc(x_93);
x_94 = lean_ctor_get(x_77, 14);
lean_inc(x_94);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 lean_ctor_release(x_77, 3);
 lean_ctor_release(x_77, 4);
 lean_ctor_release(x_77, 5);
 lean_ctor_release(x_77, 6);
 lean_ctor_release(x_77, 7);
 lean_ctor_release(x_77, 8);
 lean_ctor_release(x_77, 9);
 lean_ctor_release(x_77, 10);
 lean_ctor_release(x_77, 11);
 lean_ctor_release(x_77, 12);
 lean_ctor_release(x_77, 13);
 lean_ctor_release(x_77, 14);
 x_95 = x_77;
} else {
 lean_dec_ref(x_77);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 15, 1);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_8);
lean_ctor_set(x_96, 1, x_80);
lean_ctor_set(x_96, 2, x_81);
lean_ctor_set(x_96, 3, x_82);
lean_ctor_set(x_96, 4, x_83);
lean_ctor_set(x_96, 5, x_84);
lean_ctor_set(x_96, 6, x_85);
lean_ctor_set(x_96, 7, x_87);
lean_ctor_set(x_96, 8, x_88);
lean_ctor_set(x_96, 9, x_89);
lean_ctor_set(x_96, 10, x_90);
lean_ctor_set(x_96, 11, x_91);
lean_ctor_set(x_96, 12, x_92);
lean_ctor_set(x_96, 13, x_93);
lean_ctor_set(x_96, 14, x_94);
lean_ctor_set_uint8(x_96, sizeof(void*)*15, x_86);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_9);
lean_ctor_set(x_97, 1, x_96);
if (lean_is_scalar(x_79)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_79;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_78);
return x_98;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("intro_with_eq", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_inc(x_2);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
x_21 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9___closed__2;
x_22 = l_Lean_Expr_const___override(x_21, x_20);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_2);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_array_mk(x_27);
x_29 = l_Lean_mkAppN(x_22, x_28);
lean_dec(x_28);
x_30 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_closeGoal___spec__2(x_7, x_29, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_30, 1);
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_st_ref_get(x_11, x_32);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_8);
lean_ctor_set_tag(x_30, 1);
lean_ctor_set(x_30, 1, x_36);
lean_ctor_set(x_30, 0, x_9);
lean_ctor_set(x_34, 0, x_30);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_39 = lean_ctor_get(x_36, 1);
x_40 = lean_ctor_get(x_36, 2);
x_41 = lean_ctor_get(x_36, 3);
x_42 = lean_ctor_get(x_36, 4);
x_43 = lean_ctor_get(x_36, 5);
x_44 = lean_ctor_get(x_36, 6);
x_45 = lean_ctor_get_uint8(x_36, sizeof(void*)*15);
x_46 = lean_ctor_get(x_36, 7);
x_47 = lean_ctor_get(x_36, 8);
x_48 = lean_ctor_get(x_36, 9);
x_49 = lean_ctor_get(x_36, 10);
x_50 = lean_ctor_get(x_36, 11);
x_51 = lean_ctor_get(x_36, 12);
x_52 = lean_ctor_get(x_36, 13);
x_53 = lean_ctor_get(x_36, 14);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_36);
x_54 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_54, 0, x_8);
lean_ctor_set(x_54, 1, x_39);
lean_ctor_set(x_54, 2, x_40);
lean_ctor_set(x_54, 3, x_41);
lean_ctor_set(x_54, 4, x_42);
lean_ctor_set(x_54, 5, x_43);
lean_ctor_set(x_54, 6, x_44);
lean_ctor_set(x_54, 7, x_46);
lean_ctor_set(x_54, 8, x_47);
lean_ctor_set(x_54, 9, x_48);
lean_ctor_set(x_54, 10, x_49);
lean_ctor_set(x_54, 11, x_50);
lean_ctor_set(x_54, 12, x_51);
lean_ctor_set(x_54, 13, x_52);
lean_ctor_set(x_54, 14, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*15, x_45);
lean_ctor_set_tag(x_30, 1);
lean_ctor_set(x_30, 1, x_54);
lean_ctor_set(x_30, 0, x_9);
lean_ctor_set(x_34, 0, x_30);
return x_34;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_55 = lean_ctor_get(x_34, 0);
x_56 = lean_ctor_get(x_34, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_34);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_55, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_55, 4);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 5);
lean_inc(x_61);
x_62 = lean_ctor_get(x_55, 6);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_55, sizeof(void*)*15);
x_64 = lean_ctor_get(x_55, 7);
lean_inc(x_64);
x_65 = lean_ctor_get(x_55, 8);
lean_inc(x_65);
x_66 = lean_ctor_get(x_55, 9);
lean_inc(x_66);
x_67 = lean_ctor_get(x_55, 10);
lean_inc(x_67);
x_68 = lean_ctor_get(x_55, 11);
lean_inc(x_68);
x_69 = lean_ctor_get(x_55, 12);
lean_inc(x_69);
x_70 = lean_ctor_get(x_55, 13);
lean_inc(x_70);
x_71 = lean_ctor_get(x_55, 14);
lean_inc(x_71);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 lean_ctor_release(x_55, 4);
 lean_ctor_release(x_55, 5);
 lean_ctor_release(x_55, 6);
 lean_ctor_release(x_55, 7);
 lean_ctor_release(x_55, 8);
 lean_ctor_release(x_55, 9);
 lean_ctor_release(x_55, 10);
 lean_ctor_release(x_55, 11);
 lean_ctor_release(x_55, 12);
 lean_ctor_release(x_55, 13);
 lean_ctor_release(x_55, 14);
 x_72 = x_55;
} else {
 lean_dec_ref(x_55);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 15, 1);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_8);
lean_ctor_set(x_73, 1, x_57);
lean_ctor_set(x_73, 2, x_58);
lean_ctor_set(x_73, 3, x_59);
lean_ctor_set(x_73, 4, x_60);
lean_ctor_set(x_73, 5, x_61);
lean_ctor_set(x_73, 6, x_62);
lean_ctor_set(x_73, 7, x_64);
lean_ctor_set(x_73, 8, x_65);
lean_ctor_set(x_73, 9, x_66);
lean_ctor_set(x_73, 10, x_67);
lean_ctor_set(x_73, 11, x_68);
lean_ctor_set(x_73, 12, x_69);
lean_ctor_set(x_73, 13, x_70);
lean_ctor_set(x_73, 14, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*15, x_63);
lean_ctor_set_tag(x_30, 1);
lean_ctor_set(x_30, 1, x_73);
lean_ctor_set(x_30, 0, x_9);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_30);
lean_ctor_set(x_74, 1, x_56);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_75 = lean_ctor_get(x_30, 1);
lean_inc(x_75);
lean_dec(x_30);
x_76 = lean_st_ref_get(x_11, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_77, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_77, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 4);
lean_inc(x_83);
x_84 = lean_ctor_get(x_77, 5);
lean_inc(x_84);
x_85 = lean_ctor_get(x_77, 6);
lean_inc(x_85);
x_86 = lean_ctor_get_uint8(x_77, sizeof(void*)*15);
x_87 = lean_ctor_get(x_77, 7);
lean_inc(x_87);
x_88 = lean_ctor_get(x_77, 8);
lean_inc(x_88);
x_89 = lean_ctor_get(x_77, 9);
lean_inc(x_89);
x_90 = lean_ctor_get(x_77, 10);
lean_inc(x_90);
x_91 = lean_ctor_get(x_77, 11);
lean_inc(x_91);
x_92 = lean_ctor_get(x_77, 12);
lean_inc(x_92);
x_93 = lean_ctor_get(x_77, 13);
lean_inc(x_93);
x_94 = lean_ctor_get(x_77, 14);
lean_inc(x_94);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 lean_ctor_release(x_77, 3);
 lean_ctor_release(x_77, 4);
 lean_ctor_release(x_77, 5);
 lean_ctor_release(x_77, 6);
 lean_ctor_release(x_77, 7);
 lean_ctor_release(x_77, 8);
 lean_ctor_release(x_77, 9);
 lean_ctor_release(x_77, 10);
 lean_ctor_release(x_77, 11);
 lean_ctor_release(x_77, 12);
 lean_ctor_release(x_77, 13);
 lean_ctor_release(x_77, 14);
 x_95 = x_77;
} else {
 lean_dec_ref(x_77);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 15, 1);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_8);
lean_ctor_set(x_96, 1, x_80);
lean_ctor_set(x_96, 2, x_81);
lean_ctor_set(x_96, 3, x_82);
lean_ctor_set(x_96, 4, x_83);
lean_ctor_set(x_96, 5, x_84);
lean_ctor_set(x_96, 6, x_85);
lean_ctor_set(x_96, 7, x_87);
lean_ctor_set(x_96, 8, x_88);
lean_ctor_set(x_96, 9, x_89);
lean_ctor_set(x_96, 10, x_90);
lean_ctor_set(x_96, 11, x_91);
lean_ctor_set(x_96, 12, x_92);
lean_ctor_set(x_96, 13, x_93);
lean_ctor_set(x_96, 14, x_94);
lean_ctor_set_uint8(x_96, sizeof(void*)*15, x_86);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_9);
lean_ctor_set(x_97, 1, x_96);
if (lean_is_scalar(x_79)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_79;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_78);
return x_98;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mpr_prop", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
x_24 = l_Lean_Expr_isArrow(x_2);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_expr_instantiate1(x_3, x_4);
lean_dec(x_3);
x_26 = 2;
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lean_Meta_mkFreshExprMVarAt(x_5, x_13, x_25, x_26, x_6, x_27, x_19, x_20, x_21, x_22, x_23);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = l_Lean_Expr_mvarId_x21(x_30);
x_33 = lean_box(0);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 1, x_33);
lean_ctor_set(x_28, 0, x_4);
x_34 = lean_array_mk(x_28);
x_35 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6___boxed), 10, 2);
lean_closure_set(x_35, 0, x_34);
lean_closure_set(x_35, 1, x_30);
x_36 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_36, 0, x_35);
lean_inc(x_32);
x_37 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___boxed), 13, 3);
lean_closure_set(x_37, 0, x_7);
lean_closure_set(x_37, 1, x_32);
lean_closure_set(x_37, 2, x_8);
x_38 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__1___rarg), 11, 2);
lean_closure_set(x_38, 0, x_36);
lean_closure_set(x_38, 1, x_37);
x_39 = l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1___rarg(x_32, x_38, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_31);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_40 = lean_ctor_get(x_28, 0);
x_41 = lean_ctor_get(x_28, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_28);
x_42 = l_Lean_Expr_mvarId_x21(x_40);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_array_mk(x_44);
x_46 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6___boxed), 10, 2);
lean_closure_set(x_46, 0, x_45);
lean_closure_set(x_46, 1, x_40);
x_47 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_47, 0, x_46);
lean_inc(x_42);
x_48 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___boxed), 13, 3);
lean_closure_set(x_48, 0, x_7);
lean_closure_set(x_48, 1, x_42);
lean_closure_set(x_48, 2, x_8);
x_49 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__1___rarg), 11, 2);
lean_closure_set(x_49, 0, x_47);
lean_closure_set(x_49, 1, x_48);
x_50 = l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1___rarg(x_42, x_49, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_41);
return x_50;
}
}
else
{
uint8_t x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = 2;
x_52 = lean_unsigned_to_nat(0u);
x_53 = l_Lean_Meta_mkFreshExprMVarAt(x_5, x_13, x_3, x_51, x_6, x_52, x_19, x_20, x_21, x_22, x_23);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
x_57 = l_Lean_Expr_mvarId_x21(x_55);
x_58 = lean_box(0);
lean_ctor_set_tag(x_53, 1);
lean_ctor_set(x_53, 1, x_58);
lean_ctor_set(x_53, 0, x_4);
x_59 = lean_array_mk(x_53);
x_60 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6___boxed), 10, 2);
lean_closure_set(x_60, 0, x_59);
lean_closure_set(x_60, 1, x_55);
x_61 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_61, 0, x_60);
lean_inc(x_57);
x_62 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___boxed), 13, 3);
lean_closure_set(x_62, 0, x_7);
lean_closure_set(x_62, 1, x_57);
lean_closure_set(x_62, 2, x_8);
x_63 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__1___rarg), 11, 2);
lean_closure_set(x_63, 0, x_61);
lean_closure_set(x_63, 1, x_62);
x_64 = l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1___rarg(x_57, x_63, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_56);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_65 = lean_ctor_get(x_53, 0);
x_66 = lean_ctor_get(x_53, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_53);
x_67 = l_Lean_Expr_mvarId_x21(x_65);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_4);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_array_mk(x_69);
x_71 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6___boxed), 10, 2);
lean_closure_set(x_71, 0, x_70);
lean_closure_set(x_71, 1, x_65);
x_72 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_72, 0, x_71);
lean_inc(x_67);
x_73 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___boxed), 13, 3);
lean_closure_set(x_73, 0, x_7);
lean_closure_set(x_73, 1, x_67);
lean_closure_set(x_73, 2, x_8);
x_74 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__1___rarg), 11, 2);
lean_closure_set(x_74, 0, x_72);
lean_closure_set(x_74, 1, x_73);
x_75 = l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1___rarg(x_67, x_74, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_66);
return x_75;
}
}
}
else
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_1, 0);
lean_inc(x_76);
lean_dec(x_1);
x_77 = l_Lean_Expr_isArrow(x_2);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_inc(x_3);
lean_inc(x_10);
x_78 = l_Lean_Expr_lam___override(x_9, x_10, x_3, x_11);
x_79 = lean_box(0);
x_80 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__4;
lean_inc(x_4);
lean_inc(x_76);
lean_inc(x_12);
lean_inc(x_10);
x_81 = l_Lean_mkApp4(x_80, x_10, x_12, x_76, x_4);
x_82 = lean_expr_instantiate1(x_3, x_81);
lean_dec(x_81);
lean_dec(x_3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_82);
x_83 = l_Lean_Meta_getLevel(x_82, x_19, x_20, x_21, x_22, x_23);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = 2;
x_87 = lean_unsigned_to_nat(0u);
x_88 = l_Lean_Meta_mkFreshExprMVarAt(x_5, x_13, x_82, x_86, x_6, x_87, x_19, x_20, x_21, x_22, x_85);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = lean_ctor_get(x_88, 1);
x_92 = l_Lean_Expr_mvarId_x21(x_90);
lean_ctor_set_tag(x_88, 1);
lean_ctor_set(x_88, 1, x_79);
lean_ctor_set(x_88, 0, x_4);
x_93 = lean_array_mk(x_88);
x_94 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6___boxed), 10, 2);
lean_closure_set(x_94, 0, x_93);
lean_closure_set(x_94, 1, x_90);
x_95 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_95, 0, x_94);
lean_inc(x_92);
x_96 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___boxed), 19, 9);
lean_closure_set(x_96, 0, x_84);
lean_closure_set(x_96, 1, x_79);
lean_closure_set(x_96, 2, x_76);
lean_closure_set(x_96, 3, x_78);
lean_closure_set(x_96, 4, x_12);
lean_closure_set(x_96, 5, x_10);
lean_closure_set(x_96, 6, x_7);
lean_closure_set(x_96, 7, x_92);
lean_closure_set(x_96, 8, x_8);
x_97 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__1___rarg), 11, 2);
lean_closure_set(x_97, 0, x_95);
lean_closure_set(x_97, 1, x_96);
x_98 = l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1___rarg(x_92, x_97, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_91);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_99 = lean_ctor_get(x_88, 0);
x_100 = lean_ctor_get(x_88, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_88);
x_101 = l_Lean_Expr_mvarId_x21(x_99);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_4);
lean_ctor_set(x_102, 1, x_79);
x_103 = lean_array_mk(x_102);
x_104 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6___boxed), 10, 2);
lean_closure_set(x_104, 0, x_103);
lean_closure_set(x_104, 1, x_99);
x_105 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_105, 0, x_104);
lean_inc(x_101);
x_106 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___boxed), 19, 9);
lean_closure_set(x_106, 0, x_84);
lean_closure_set(x_106, 1, x_79);
lean_closure_set(x_106, 2, x_76);
lean_closure_set(x_106, 3, x_78);
lean_closure_set(x_106, 4, x_12);
lean_closure_set(x_106, 5, x_10);
lean_closure_set(x_106, 6, x_7);
lean_closure_set(x_106, 7, x_101);
lean_closure_set(x_106, 8, x_8);
x_107 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__1___rarg), 11, 2);
lean_closure_set(x_107, 0, x_105);
lean_closure_set(x_107, 1, x_106);
x_108 = l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1___rarg(x_101, x_107, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_100);
return x_108;
}
}
else
{
uint8_t x_109; 
lean_dec(x_82);
lean_dec(x_78);
lean_dec(x_76);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_109 = !lean_is_exclusive(x_83);
if (x_109 == 0)
{
return x_83;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_83, 0);
x_111 = lean_ctor_get(x_83, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_83);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
lean_object* x_113; 
lean_dec(x_9);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_3);
x_113 = l_Lean_Meta_getLevel(x_3, x_19, x_20, x_21, x_22, x_23);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = 2;
x_117 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_118 = l_Lean_Meta_mkFreshExprMVarAt(x_5, x_13, x_3, x_116, x_6, x_117, x_19, x_20, x_21, x_22, x_115);
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = lean_ctor_get(x_118, 1);
x_122 = l_Lean_Expr_mvarId_x21(x_120);
x_123 = lean_box(0);
lean_ctor_set_tag(x_118, 1);
lean_ctor_set(x_118, 1, x_123);
lean_ctor_set(x_118, 0, x_4);
x_124 = lean_array_mk(x_118);
x_125 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6___boxed), 10, 2);
lean_closure_set(x_125, 0, x_124);
lean_closure_set(x_125, 1, x_120);
x_126 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_126, 0, x_125);
lean_inc(x_122);
x_127 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9___boxed), 19, 9);
lean_closure_set(x_127, 0, x_114);
lean_closure_set(x_127, 1, x_123);
lean_closure_set(x_127, 2, x_76);
lean_closure_set(x_127, 3, x_3);
lean_closure_set(x_127, 4, x_12);
lean_closure_set(x_127, 5, x_10);
lean_closure_set(x_127, 6, x_7);
lean_closure_set(x_127, 7, x_122);
lean_closure_set(x_127, 8, x_8);
x_128 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__1___rarg), 11, 2);
lean_closure_set(x_128, 0, x_126);
lean_closure_set(x_128, 1, x_127);
x_129 = l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1___rarg(x_122, x_128, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_121);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_130 = lean_ctor_get(x_118, 0);
x_131 = lean_ctor_get(x_118, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_118);
x_132 = l_Lean_Expr_mvarId_x21(x_130);
x_133 = lean_box(0);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_4);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_array_mk(x_134);
x_136 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6___boxed), 10, 2);
lean_closure_set(x_136, 0, x_135);
lean_closure_set(x_136, 1, x_130);
x_137 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_137, 0, x_136);
lean_inc(x_132);
x_138 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9___boxed), 19, 9);
lean_closure_set(x_138, 0, x_114);
lean_closure_set(x_138, 1, x_133);
lean_closure_set(x_138, 2, x_76);
lean_closure_set(x_138, 3, x_3);
lean_closure_set(x_138, 4, x_12);
lean_closure_set(x_138, 5, x_10);
lean_closure_set(x_138, 6, x_7);
lean_closure_set(x_138, 7, x_132);
lean_closure_set(x_138, 8, x_8);
x_139 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__1___rarg), 11, 2);
lean_closure_set(x_139, 0, x_137);
lean_closure_set(x_139, 1, x_138);
x_140 = l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1___rarg(x_132, x_139, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_131);
return x_140;
}
}
else
{
uint8_t x_141; 
lean_dec(x_76);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_141 = !lean_is_exclusive(x_113);
if (x_141 == 0)
{
return x_113;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_113, 0);
x_143 = lean_ctor_get(x_113, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_113);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__11___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_st_ref_get(x_3, x_11);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_MVarId_getType(x_26, x_7, x_8, x_9, x_10, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_76; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_76 = l_Lean_Expr_isForall(x_28);
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = l_Lean_Expr_isLet(x_28);
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = l_Lean_Expr_isLetFun(x_28);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_2);
x_12 = x_79;
x_13 = x_29;
goto block_22;
}
else
{
lean_object* x_80; 
lean_dec(x_2);
x_80 = lean_box(0);
x_30 = x_80;
goto block_75;
}
}
else
{
lean_object* x_81; 
lean_dec(x_2);
x_81 = lean_box(0);
x_30 = x_81;
goto block_75;
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_2);
lean_dec(x_1);
x_82 = l_Lean_Expr_bindingDomain_x21(x_28);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_82);
x_83 = l_Lean_Meta_isProp(x_82, x_7, x_8, x_9, x_10, x_29);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_82);
lean_dec(x_28);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
lean_inc(x_3);
x_87 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_st_ref_get(x_3, x_89);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_ctor_get(x_90, 1);
lean_ctor_set_tag(x_90, 3);
lean_ctor_set(x_90, 1, x_92);
lean_ctor_set(x_90, 0, x_88);
x_12 = x_90;
x_13 = x_93;
goto block_22;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_90, 0);
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_90);
x_96 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_96, 0, x_88);
lean_ctor_set(x_96, 1, x_94);
x_12 = x_96;
x_13 = x_95;
goto block_22;
}
}
else
{
uint8_t x_97; 
lean_dec(x_3);
x_97 = !lean_is_exclusive(x_87);
if (x_97 == 0)
{
return x_87;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_87, 0);
x_99 = lean_ctor_get(x_87, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_87);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_83, 1);
lean_inc(x_101);
lean_dec(x_83);
x_102 = lean_st_ref_get(x_3, x_101);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
lean_inc(x_105);
x_106 = l_Lean_MVarId_getTag(x_105, x_7, x_8, x_9, x_10, x_104);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l_Lean_Expr_bindingBody_x21(x_28);
x_110 = l_Lean_mkFreshFVarId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_108);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
lean_inc(x_111);
x_113 = l_Lean_Expr_fvar___override(x_111);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_82);
x_114 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_preprocessHypothesis(x_82, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_112);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_ctor_get(x_7, 2);
lean_inc(x_117);
x_118 = l_Lean_Expr_bindingName_x21(x_28);
x_119 = lean_ctor_get(x_115, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
lean_dec(x_115);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_119);
lean_inc(x_118);
x_121 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(x_118, x_119, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_116);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = l_Lean_Expr_bindingInfo_x21(x_28);
x_125 = lean_unbox(x_124);
lean_dec(x_124);
x_126 = 0;
lean_inc(x_119);
lean_inc(x_111);
x_127 = l_Lean_LocalContext_mkLocalDecl(x_117, x_111, x_122, x_119, x_125, x_126);
x_128 = l_Lean_Meta_getLocalInstances(x_7, x_8, x_9, x_10, x_123);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_128, 0);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_119);
x_132 = l_Lean_Meta_isClass_x3f(x_119, x_7, x_8, x_9, x_10, x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_free_object(x_128);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_box(0);
lean_inc(x_3);
x_136 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10(x_120, x_28, x_109, x_113, x_127, x_107, x_105, x_111, x_118, x_82, x_125, x_119, x_130, x_135, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_134);
lean_dec(x_28);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_12 = x_137;
x_13 = x_138;
goto block_22;
}
else
{
uint8_t x_139; 
lean_dec(x_3);
x_139 = !lean_is_exclusive(x_136);
if (x_139 == 0)
{
return x_136;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_136, 0);
x_141 = lean_ctor_get(x_136, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_136);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_143 = lean_ctor_get(x_132, 1);
lean_inc(x_143);
lean_dec(x_132);
x_144 = lean_ctor_get(x_133, 0);
lean_inc(x_144);
lean_dec(x_133);
lean_inc(x_113);
lean_ctor_set(x_128, 1, x_113);
lean_ctor_set(x_128, 0, x_144);
x_145 = lean_array_push(x_130, x_128);
x_146 = lean_box(0);
lean_inc(x_3);
x_147 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10(x_120, x_28, x_109, x_113, x_127, x_107, x_105, x_111, x_118, x_82, x_125, x_119, x_145, x_146, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_143);
lean_dec(x_28);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_12 = x_148;
x_13 = x_149;
goto block_22;
}
else
{
uint8_t x_150; 
lean_dec(x_3);
x_150 = !lean_is_exclusive(x_147);
if (x_150 == 0)
{
return x_147;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_147, 0);
x_152 = lean_ctor_get(x_147, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_147);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
}
else
{
uint8_t x_154; 
lean_free_object(x_128);
lean_dec(x_130);
lean_dec(x_127);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_105);
lean_dec(x_82);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_154 = !lean_is_exclusive(x_132);
if (x_154 == 0)
{
return x_132;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_132, 0);
x_156 = lean_ctor_get(x_132, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_132);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_128, 0);
x_159 = lean_ctor_get(x_128, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_128);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_119);
x_160 = l_Lean_Meta_isClass_x3f(x_119, x_7, x_8, x_9, x_10, x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_box(0);
lean_inc(x_3);
x_164 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10(x_120, x_28, x_109, x_113, x_127, x_107, x_105, x_111, x_118, x_82, x_125, x_119, x_158, x_163, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_162);
lean_dec(x_28);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_12 = x_165;
x_13 = x_166;
goto block_22;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_3);
x_167 = lean_ctor_get(x_164, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_164, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_169 = x_164;
} else {
 lean_dec_ref(x_164);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_171 = lean_ctor_get(x_160, 1);
lean_inc(x_171);
lean_dec(x_160);
x_172 = lean_ctor_get(x_161, 0);
lean_inc(x_172);
lean_dec(x_161);
lean_inc(x_113);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_113);
x_174 = lean_array_push(x_158, x_173);
x_175 = lean_box(0);
lean_inc(x_3);
x_176 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10(x_120, x_28, x_109, x_113, x_127, x_107, x_105, x_111, x_118, x_82, x_125, x_119, x_174, x_175, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_171);
lean_dec(x_28);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_12 = x_177;
x_13 = x_178;
goto block_22;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_3);
x_179 = lean_ctor_get(x_176, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_176, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_181 = x_176;
} else {
 lean_dec_ref(x_176);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_158);
lean_dec(x_127);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_105);
lean_dec(x_82);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_183 = lean_ctor_get(x_160, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_160, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_185 = x_160;
} else {
 lean_dec_ref(x_160);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
}
else
{
uint8_t x_187; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_105);
lean_dec(x_82);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_187 = !lean_is_exclusive(x_121);
if (x_187 == 0)
{
return x_121;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_121, 0);
x_189 = lean_ctor_get(x_121, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_121);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_105);
lean_dec(x_82);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_191 = !lean_is_exclusive(x_114);
if (x_191 == 0)
{
return x_114;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_114, 0);
x_193 = lean_ctor_get(x_114, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_114);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
else
{
uint8_t x_195; 
lean_dec(x_105);
lean_dec(x_82);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_195 = !lean_is_exclusive(x_106);
if (x_195 == 0)
{
return x_106;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_106, 0);
x_197 = lean_ctor_get(x_106, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_106);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_82);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_199 = !lean_is_exclusive(x_83);
if (x_199 == 0)
{
return x_83;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_83, 0);
x_201 = lean_ctor_get(x_83, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_83);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
block_75:
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_30);
x_31 = l_Lean_Meta_Grind_getConfig___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_32, sizeof(void*)*6 + 14);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_28);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_35 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_st_ref_get(x_3, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_36);
x_42 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed), 9, 1);
lean_closure_set(x_42, 0, x_36);
x_43 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_43, 0, x_42);
x_44 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3___boxed), 12, 2);
lean_closure_set(x_44, 0, x_36);
lean_closure_set(x_44, 1, x_1);
x_45 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__1___rarg), 11, 2);
lean_closure_set(x_45, 0, x_43);
lean_closure_set(x_45, 1, x_44);
lean_inc(x_3);
x_46 = l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1___rarg(x_41, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_40);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_12 = x_47;
x_13 = x_48;
goto block_22;
}
else
{
uint8_t x_49; 
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_46);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_35);
if (x_53 == 0)
{
return x_35;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_35, 0);
x_55 = lean_ctor_get(x_35, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_35);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_57 = lean_ctor_get(x_31, 1);
lean_inc(x_57);
lean_dec(x_31);
x_58 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__11___closed__1;
x_59 = l_Lean_Meta_expandLet(x_28, x_58);
x_60 = lean_st_ref_get(x_3, x_57);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_63);
x_64 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__4___boxed), 9, 1);
lean_closure_set(x_64, 0, x_63);
x_65 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_65, 0, x_64);
lean_inc(x_63);
x_66 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___boxed), 13, 3);
lean_closure_set(x_66, 0, x_59);
lean_closure_set(x_66, 1, x_63);
lean_closure_set(x_66, 2, x_1);
x_67 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___spec__1___rarg), 11, 2);
lean_closure_set(x_67, 0, x_65);
lean_closure_set(x_67, 1, x_66);
lean_inc(x_3);
x_68 = l_Lean_MVarId_withContext___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__1___rarg(x_63, x_67, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_62);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_12 = x_69;
x_13 = x_70;
goto block_22;
}
else
{
uint8_t x_71; 
lean_dec(x_3);
x_71 = !lean_is_exclusive(x_68);
if (x_71 == 0)
{
return x_68;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_68, 0);
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_68);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
else
{
uint8_t x_203; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_203 = !lean_is_exclusive(x_27);
if (x_203 == 0)
{
return x_27;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_27, 0);
x_205 = lean_ctor_get(x_27, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_27);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
block_22:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_st_ref_get(x_3, x_13);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__1___boxed), 9, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__11), 11, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_1);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_11, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkFreshId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_mkFreshFVarId___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
lean_object* x_20; 
x_20 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
lean_object* x_20; 
x_20 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
_start:
{
uint8_t x_24; lean_object* x_25; 
x_24 = lean_unbox(x_11);
lean_dec(x_11);
x_25 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_24, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
lean_dec(x_14);
lean_dec(x_2);
return x_25;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 12);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Meta_Grind_CasesTypes_isEagerSplit(x_6, x_4);
lean_dec(x_4);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = 0;
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(x_6, x_2, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 5)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_InductiveVal_numCtors(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_dec_le(x_12, x_13);
lean_dec(x_12);
x_15 = lean_box(x_14);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
lean_dec(x_8);
x_18 = l_Lean_InductiveVal_numCtors(x_17);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_dec_le(x_18, x_19);
lean_dec(x_18);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_8);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 0);
lean_dec(x_24);
x_25 = 0;
x_26 = lean_box(x_25);
lean_ctor_set(x_7, 0, x_26);
return x_7;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_dec(x_7);
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
return x_7;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_7);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_5);
x_35 = 0;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_4);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_ctor_get(x_1, 5);
x_13 = lean_ctor_get(x_1, 6);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*15);
x_15 = lean_ctor_get(x_1, 7);
x_16 = lean_ctor_get(x_1, 8);
x_17 = lean_ctor_get(x_1, 9);
x_18 = lean_ctor_get(x_1, 10);
x_19 = lean_ctor_get(x_1, 11);
x_20 = lean_ctor_get(x_1, 12);
x_21 = lean_ctor_get(x_1, 13);
x_22 = lean_ctor_get(x_1, 14);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_23 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_8);
lean_ctor_set(x_23, 2, x_9);
lean_ctor_set(x_23, 3, x_10);
lean_ctor_set(x_23, 4, x_11);
lean_ctor_set(x_23, 5, x_12);
lean_ctor_set(x_23, 6, x_13);
lean_ctor_set(x_23, 7, x_15);
lean_ctor_set(x_23, 8, x_16);
lean_ctor_set(x_23, 9, x_17);
lean_ctor_set(x_23, 10, x_18);
lean_ctor_set(x_23, 11, x_19);
lean_ctor_set(x_23, 12, x_20);
lean_ctor_set(x_23, 13, x_21);
lean_ctor_set(x_23, 14, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*15, x_14);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_23);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_27 = lean_ctor_get(x_1, 1);
x_28 = lean_ctor_get(x_1, 2);
x_29 = lean_ctor_get(x_1, 3);
x_30 = lean_ctor_get(x_1, 4);
x_31 = lean_ctor_get(x_1, 5);
x_32 = lean_ctor_get(x_1, 6);
x_33 = lean_ctor_get_uint8(x_1, sizeof(void*)*15);
x_34 = lean_ctor_get(x_1, 7);
x_35 = lean_ctor_get(x_1, 8);
x_36 = lean_ctor_get(x_1, 9);
x_37 = lean_ctor_get(x_1, 10);
x_38 = lean_ctor_get(x_1, 11);
x_39 = lean_ctor_get(x_1, 12);
x_40 = lean_ctor_get(x_1, 13);
x_41 = lean_ctor_get(x_1, 14);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_42 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_42, 0, x_25);
lean_ctor_set(x_42, 1, x_27);
lean_ctor_set(x_42, 2, x_28);
lean_ctor_set(x_42, 3, x_29);
lean_ctor_set(x_42, 4, x_30);
lean_ctor_set(x_42, 5, x_31);
lean_ctor_set(x_42, 6, x_32);
lean_ctor_set(x_42, 7, x_34);
lean_ctor_set(x_42, 8, x_35);
lean_ctor_set(x_42, 9, x_36);
lean_ctor_set(x_42, 10, x_37);
lean_ctor_set(x_42, 11, x_38);
lean_ctor_set(x_42, 12, x_39);
lean_ctor_set(x_42, 13, x_40);
lean_ctor_set(x_42, 14, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*15, x_33);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_3);
x_2 = x_26;
x_3 = x_43;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_FVarId_getType(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Expr_fvar___override(x_1);
x_14 = l_Lean_Meta_Grind_cases(x_2, x_13, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_box(0);
x_18 = l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___spec__1(x_3, x_16, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___spec__1(x_3, x_20, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Expr_getAppFn(x_4);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = 1;
x_17 = l_Lean_Meta_Grind_saveCases(x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__2(x_1, x_2, x_3, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
lean_dec(x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__2(x_1, x_2, x_3, x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_13 = lean_whnf(x_4, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_1);
x_17 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(x_1, x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_free_object(x_13);
x_19 = l_Lean_Meta_Grind_cheapCasesOnly___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__3(x_2, x_3, x_1, x_15, x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
lean_dec(x_15);
lean_dec(x_1);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(x_15, x_10, x_11, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
x_36 = lean_box(0);
x_37 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__3(x_2, x_3, x_1, x_15, x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_35);
lean_dec(x_15);
lean_dec(x_1);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_26);
if (x_38 == 0)
{
return x_26;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_26, 0);
x_40 = lean_ctor_get(x_26, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_26);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_13, 0);
x_43 = lean_ctor_get(x_13, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_13);
lean_inc(x_1);
x_44 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(x_1, x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_42);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = l_Lean_Meta_Grind_cheapCasesOnly___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_43);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_box(0);
x_52 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__3(x_2, x_3, x_1, x_42, x_51, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_50);
lean_dec(x_42);
lean_dec(x_1);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_dec(x_47);
x_54 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(x_42, x_10, x_11, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_42);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_58 = x_54;
} else {
 lean_dec_ref(x_54);
 x_58 = lean_box(0);
}
x_59 = lean_box(0);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
lean_dec(x_54);
x_62 = lean_box(0);
x_63 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__3(x_2, x_3, x_1, x_42, x_62, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_61);
lean_dec(x_42);
lean_dec(x_1);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_42);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_ctor_get(x_54, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_54, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_66 = x_54;
} else {
 lean_dec_ref(x_54);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_13);
if (x_68 == 0)
{
return x_13;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_13, 0);
x_70 = lean_ctor_get(x_13, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_13);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_inc(x_2);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__1___boxed), 9, 1);
lean_closure_set(x_12, 0, x_2);
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__4___boxed), 12, 3);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_11);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_11, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTR_loop___at___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_ctor_get(x_1, 4);
x_14 = lean_ctor_get(x_1, 5);
x_15 = lean_ctor_get(x_1, 6);
x_16 = lean_ctor_get(x_1, 7);
x_17 = lean_ctor_get(x_1, 8);
x_18 = lean_ctor_get(x_1, 9);
x_19 = lean_ctor_get(x_1, 10);
x_20 = lean_ctor_get(x_1, 11);
x_21 = lean_ctor_get(x_1, 12);
x_22 = lean_ctor_get(x_1, 13);
x_23 = lean_ctor_get(x_1, 14);
x_24 = l_Lean_Meta_Grind_injection_x3f(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_free_object(x_1);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_1, 0, x_35);
lean_ctor_set(x_25, 0, x_1);
return x_24;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_25, 0);
lean_inc(x_36);
lean_dec(x_25);
lean_ctor_set(x_1, 0, x_36);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_24, 0, x_37);
return x_24;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
lean_dec(x_24);
x_39 = lean_ctor_get(x_25, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_40 = x_25;
} else {
 lean_dec_ref(x_25);
 x_40 = lean_box(0);
}
lean_ctor_set(x_1, 0, x_39);
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_1);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_free_object(x_1);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_43 = !lean_is_exclusive(x_24);
if (x_43 == 0)
{
return x_24;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_24, 0);
x_45 = lean_ctor_get(x_24, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_24);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_47 = lean_ctor_get(x_1, 0);
x_48 = lean_ctor_get(x_1, 1);
x_49 = lean_ctor_get(x_1, 2);
x_50 = lean_ctor_get(x_1, 3);
x_51 = lean_ctor_get(x_1, 4);
x_52 = lean_ctor_get(x_1, 5);
x_53 = lean_ctor_get(x_1, 6);
x_54 = lean_ctor_get_uint8(x_1, sizeof(void*)*15);
x_55 = lean_ctor_get(x_1, 7);
x_56 = lean_ctor_get(x_1, 8);
x_57 = lean_ctor_get(x_1, 9);
x_58 = lean_ctor_get(x_1, 10);
x_59 = lean_ctor_get(x_1, 11);
x_60 = lean_ctor_get(x_1, 12);
x_61 = lean_ctor_get(x_1, 13);
x_62 = lean_ctor_get(x_1, 14);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_1);
x_63 = l_Lean_Meta_Grind_injection_x3f(x_47, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = lean_box(0);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_70 = x_63;
} else {
 lean_dec_ref(x_63);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_64, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_72 = x_64;
} else {
 lean_dec_ref(x_64);
 x_72 = lean_box(0);
}
x_73 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_48);
lean_ctor_set(x_73, 2, x_49);
lean_ctor_set(x_73, 3, x_50);
lean_ctor_set(x_73, 4, x_51);
lean_ctor_set(x_73, 5, x_52);
lean_ctor_set(x_73, 6, x_53);
lean_ctor_set(x_73, 7, x_55);
lean_ctor_set(x_73, 8, x_56);
lean_ctor_set(x_73, 9, x_57);
lean_ctor_set(x_73, 10, x_58);
lean_ctor_set(x_73, 11, x_59);
lean_ctor_set(x_73, 12, x_60);
lean_ctor_set(x_73, 13, x_61);
lean_ctor_set(x_73, 14, x_62);
lean_ctor_set_uint8(x_73, sizeof(void*)*15, x_54);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
if (lean_is_scalar(x_70)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_70;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_69);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
x_76 = lean_ctor_get(x_63, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_63, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_78 = x_63;
} else {
 lean_dec_ref(x_63);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_MVarId_getType(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_Meta_isProp(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_MVarId_exfalso(x_1, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 4);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 5);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 6);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_2, sizeof(void*)*15);
x_25 = lean_ctor_get(x_2, 7);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 8);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 9);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 10);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 11);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 12);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 13);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 14);
lean_inc(x_32);
lean_dec(x_2);
x_33 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_33, 0, x_17);
lean_ctor_set(x_33, 1, x_18);
lean_ctor_set(x_33, 2, x_19);
lean_ctor_set(x_33, 3, x_20);
lean_ctor_set(x_33, 4, x_21);
lean_ctor_set(x_33, 5, x_22);
lean_ctor_set(x_33, 6, x_23);
lean_ctor_set(x_33, 7, x_25);
lean_ctor_set(x_33, 8, x_26);
lean_ctor_set(x_33, 9, x_27);
lean_ctor_set(x_33, 10, x_28);
lean_ctor_set(x_33, 11, x_29);
lean_ctor_set(x_33, 12, x_30);
lean_ctor_set(x_33, 13, x_31);
lean_ctor_set(x_33, 14, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*15, x_24);
lean_ctor_set(x_15, 0, x_33);
return x_15;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_34 = lean_ctor_get(x_15, 0);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_15);
x_36 = lean_ctor_get(x_2, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 4);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 5);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 6);
lean_inc(x_41);
x_42 = lean_ctor_get_uint8(x_2, sizeof(void*)*15);
x_43 = lean_ctor_get(x_2, 7);
lean_inc(x_43);
x_44 = lean_ctor_get(x_2, 8);
lean_inc(x_44);
x_45 = lean_ctor_get(x_2, 9);
lean_inc(x_45);
x_46 = lean_ctor_get(x_2, 10);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 11);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 12);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 13);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 14);
lean_inc(x_50);
lean_dec(x_2);
x_51 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_51, 0, x_34);
lean_ctor_set(x_51, 1, x_36);
lean_ctor_set(x_51, 2, x_37);
lean_ctor_set(x_51, 3, x_38);
lean_ctor_set(x_51, 4, x_39);
lean_ctor_set(x_51, 5, x_40);
lean_ctor_set(x_51, 6, x_41);
lean_ctor_set(x_51, 7, x_43);
lean_ctor_set(x_51, 8, x_44);
lean_ctor_set(x_51, 9, x_45);
lean_ctor_set(x_51, 10, x_46);
lean_ctor_set(x_51, 11, x_47);
lean_ctor_set(x_51, 12, x_48);
lean_ctor_set(x_51, 13, x_49);
lean_ctor_set(x_51, 14, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*15, x_42);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_35);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_15);
if (x_53 == 0)
{
return x_15;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_15, 0);
x_55 = lean_ctor_get(x_15, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_15);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_11);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_11, 0);
lean_dec(x_58);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_11, 1);
lean_inc(x_59);
lean_dec(x_11);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_2);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_11);
if (x_61 == 0)
{
return x_11;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_11, 0);
x_63 = lean_ctor_get(x_11, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_11);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_8);
if (x_65 == 0)
{
return x_8;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_8, 0);
x_67 = lean_ctor_get(x_8, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_8);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lambda__1), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_7, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_intros_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_16 = l_Lean_Meta_Grind_intros_go(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_2 = x_15;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_intros_go___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_16 = l_Lean_Meta_Grind_intros_go(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_2 = x_15;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_3);
x_12 = l_Lean_Meta_Grind_addHypothesis(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_3, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_st_ref_get(x_3, x_16);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_14, 1, x_19);
lean_ctor_set(x_17, 0, x_14);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_14, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_st_ref_get(x_3, x_24);
lean_dec(x_3);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_26);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_12);
if (x_31 == 0)
{
return x_12;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_12, 0);
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_12);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 1);
lean_dec(x_11);
lean_ctor_set(x_1, 1, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_intros_go___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_intros_go___lambda__2___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_13 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_17 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(x_16, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_18, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_18, 4);
lean_inc(x_24);
x_25 = lean_ctor_get(x_18, 5);
lean_inc(x_25);
x_26 = lean_ctor_get(x_18, 6);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_18, sizeof(void*)*15);
x_28 = lean_ctor_get(x_18, 7);
lean_inc(x_28);
x_29 = lean_ctor_get(x_18, 8);
lean_inc(x_29);
x_30 = lean_ctor_get(x_18, 9);
lean_inc(x_30);
x_31 = lean_ctor_get(x_18, 10);
lean_inc(x_31);
x_32 = lean_ctor_get(x_18, 11);
lean_inc(x_32);
x_33 = lean_ctor_get(x_18, 12);
lean_inc(x_33);
x_34 = lean_ctor_get(x_18, 13);
lean_inc(x_34);
x_35 = lean_ctor_get(x_18, 14);
lean_inc(x_35);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_36 = l_Lean_MVarId_byContra_x3f(x_20, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_st_ref_take(x_4, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_array_push(x_40, x_18);
x_43 = lean_st_ref_set(x_4, x_42, x_41);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = lean_box(0);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_18);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_51 = lean_ctor_get(x_18, 14);
lean_dec(x_51);
x_52 = lean_ctor_get(x_18, 13);
lean_dec(x_52);
x_53 = lean_ctor_get(x_18, 12);
lean_dec(x_53);
x_54 = lean_ctor_get(x_18, 11);
lean_dec(x_54);
x_55 = lean_ctor_get(x_18, 10);
lean_dec(x_55);
x_56 = lean_ctor_get(x_18, 9);
lean_dec(x_56);
x_57 = lean_ctor_get(x_18, 8);
lean_dec(x_57);
x_58 = lean_ctor_get(x_18, 7);
lean_dec(x_58);
x_59 = lean_ctor_get(x_18, 6);
lean_dec(x_59);
x_60 = lean_ctor_get(x_18, 5);
lean_dec(x_60);
x_61 = lean_ctor_get(x_18, 4);
lean_dec(x_61);
x_62 = lean_ctor_get(x_18, 3);
lean_dec(x_62);
x_63 = lean_ctor_get(x_18, 2);
lean_dec(x_63);
x_64 = lean_ctor_get(x_18, 1);
lean_dec(x_64);
x_65 = lean_ctor_get(x_18, 0);
lean_dec(x_65);
x_66 = lean_ctor_get(x_36, 1);
lean_inc(x_66);
lean_dec(x_36);
x_67 = lean_ctor_get(x_37, 0);
lean_inc(x_67);
lean_dec(x_37);
lean_ctor_set(x_18, 0, x_67);
x_68 = l_Lean_Meta_Grind_intros_go(x_2, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_18);
x_69 = lean_ctor_get(x_36, 1);
lean_inc(x_69);
lean_dec(x_36);
x_70 = lean_ctor_get(x_37, 0);
lean_inc(x_70);
lean_dec(x_37);
x_71 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_21);
lean_ctor_set(x_71, 2, x_22);
lean_ctor_set(x_71, 3, x_23);
lean_ctor_set(x_71, 4, x_24);
lean_ctor_set(x_71, 5, x_25);
lean_ctor_set(x_71, 6, x_26);
lean_ctor_set(x_71, 7, x_28);
lean_ctor_set(x_71, 8, x_29);
lean_ctor_set(x_71, 9, x_30);
lean_ctor_set(x_71, 10, x_31);
lean_ctor_set(x_71, 11, x_32);
lean_ctor_set(x_71, 12, x_33);
lean_ctor_set(x_71, 13, x_34);
lean_ctor_set(x_71, 14, x_35);
lean_ctor_set_uint8(x_71, sizeof(void*)*15, x_27);
x_72 = l_Lean_Meta_Grind_intros_go(x_2, x_71, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_69);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_36);
if (x_73 == 0)
{
return x_36;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_36, 0);
x_75 = lean_ctor_get(x_36, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_36);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_17);
if (x_77 == 0)
{
return x_17;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_17, 0);
x_79 = lean_ctor_get(x_17, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_17);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
case 1:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_13, 1);
lean_inc(x_81);
lean_dec(x_13);
x_82 = lean_ctor_get(x_14, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_14, 1);
lean_inc(x_83);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_82);
lean_inc(x_83);
x_84 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f(x_83, x_82, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_81);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_82);
lean_inc(x_83);
x_87 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(x_83, x_82, x_8, x_9, x_10, x_11, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_83, 0);
lean_inc(x_90);
x_91 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__1___boxed), 9, 1);
lean_closure_set(x_91, 0, x_83);
lean_inc(x_2);
x_92 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_intros_go___lambda__1), 11, 2);
lean_closure_set(x_92, 0, x_82);
lean_closure_set(x_92, 1, x_2);
x_93 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_93, 0, x_91);
lean_closure_set(x_93, 1, x_92);
x_94 = l_Lean_Meta_Grind_intros_go___lambda__3___closed__1;
x_95 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_95, 0, x_93);
lean_closure_set(x_95, 1, x_94);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_96 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_90, x_95, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_89);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l_Lean_Meta_Grind_intros_go(x_2, x_97, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_98);
return x_99;
}
else
{
uint8_t x_100; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_100 = !lean_is_exclusive(x_96);
if (x_100 == 0)
{
return x_96;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_96, 0);
x_102 = lean_ctor_get(x_96, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_96);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_83);
lean_dec(x_82);
x_104 = lean_ctor_get(x_87, 1);
lean_inc(x_104);
lean_dec(x_87);
x_105 = lean_ctor_get(x_88, 0);
lean_inc(x_105);
lean_dec(x_88);
x_106 = l_Lean_Meta_Grind_intros_go(x_2, x_105, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_104);
return x_106;
}
}
else
{
uint8_t x_107; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_107 = !lean_is_exclusive(x_87);
if (x_107 == 0)
{
return x_87;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_87, 0);
x_109 = lean_ctor_get(x_87, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_87);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_83);
lean_dec(x_82);
x_111 = lean_ctor_get(x_84, 1);
lean_inc(x_111);
lean_dec(x_84);
x_112 = lean_ctor_get(x_85, 0);
lean_inc(x_112);
lean_dec(x_85);
x_113 = l_List_forM___at_Lean_Meta_Grind_intros_go___spec__1(x_2, x_112, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_111);
return x_113;
}
}
else
{
uint8_t x_114; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_114 = !lean_is_exclusive(x_84);
if (x_114 == 0)
{
return x_84;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_84, 0);
x_116 = lean_ctor_get(x_84, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_84);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
case 2:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_13, 1);
lean_inc(x_118);
lean_dec(x_13);
x_119 = lean_ctor_get(x_14, 0);
lean_inc(x_119);
lean_dec(x_14);
x_120 = l_Lean_Meta_Grind_intros_go(x_2, x_119, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_118);
return x_120;
}
default: 
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_13, 1);
lean_inc(x_121);
lean_dec(x_13);
x_122 = lean_ctor_get(x_14, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_14, 1);
lean_inc(x_123);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_123);
x_124 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f(x_123, x_122, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_121);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = l_Lean_Meta_Grind_intros_go(x_2, x_123, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_126);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_123);
x_128 = lean_ctor_get(x_124, 1);
lean_inc(x_128);
lean_dec(x_124);
x_129 = lean_ctor_get(x_125, 0);
lean_inc(x_129);
lean_dec(x_125);
x_130 = l_List_forM___at_Lean_Meta_Grind_intros_go___spec__2(x_2, x_129, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_128);
return x_130;
}
}
else
{
uint8_t x_131; 
lean_dec(x_123);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_131 = !lean_is_exclusive(x_124);
if (x_131 == 0)
{
return x_124;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_124, 0);
x_133 = lean_ctor_get(x_124, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_124);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_135 = !lean_is_exclusive(x_13);
if (x_135 == 0)
{
return x_13;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_13, 0);
x_137 = lean_ctor_get(x_13, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_13);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*15);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Meta_Grind_intros_go___lambda__3(x_2, x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_intros_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forM___at_Lean_Meta_Grind_intros_go___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_intros_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forM___at_Lean_Meta_Grind_intros_go___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_intros_go___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_intros_go___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_intros_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__11___closed__1;
x_12 = lean_st_mk_ref(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_Grind_intros_go(x_1, x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_13, x_16);
lean_dec(x_13);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_array_to_list(x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_array_to_list(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_13);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_assertAt___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mp", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_assertAt___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__1;
x_2 = l_Lean_Meta_Grind_assertAt___lambda__1___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_assertAt___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_levelZero;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_assertAt___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_assertAt___lambda__1___closed__2;
x_2 = l_Lean_Meta_Grind_assertAt___lambda__1___closed__3;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAt___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_13 = l_Lean_Meta_Grind_preprocess(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_17 = l_Lean_Meta_Simp_Result_getProof(x_14, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_Grind_assertAt___lambda__1___closed__4;
lean_inc(x_16);
x_21 = l_Lean_mkApp4(x_20, x_1, x_16, x_18, x_2);
lean_inc(x_4);
x_22 = l_Lean_Meta_Grind_add(x_16, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_st_ref_get(x_4, x_23);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_24, 1);
x_27 = lean_st_ref_get(x_4, x_26);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_ctor_set(x_24, 1, x_29);
lean_ctor_set(x_27, 0, x_24);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_27);
lean_ctor_set(x_24, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_35 = lean_st_ref_get(x_4, x_34);
lean_dec(x_4);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_36);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_22);
if (x_41 == 0)
{
return x_22;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_22, 0);
x_43 = lean_ctor_get(x_22, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_22);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_17);
if (x_45 == 0)
{
return x_17;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_17, 0);
x_47 = lean_ctor_get(x_17, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_17);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_13);
if (x_49 == 0)
{
return x_13;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_13, 0);
x_51 = lean_ctor_get(x_13, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_13);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
lean_inc(x_4);
x_13 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(x_4, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__1___boxed), 9, 1);
lean_closure_set(x_15, 0, x_4);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_assertAt___lambda__1), 12, 3);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_3);
x_17 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
x_18 = l_Lean_Meta_Grind_intros_go___lambda__3___closed__1;
x_19 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_14, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*15);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_21);
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_20, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_20, 0, x_33);
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_dec(x_20);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_20);
if (x_37 == 0)
{
return x_20;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_20, 0);
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_20);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__4;
x_42 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_41, x_10, x_11, x_12);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = !lean_is_exclusive(x_4);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_46 = lean_ctor_get(x_4, 0);
x_47 = lean_ctor_get(x_4, 1);
x_48 = lean_ctor_get(x_4, 2);
x_49 = lean_ctor_get(x_4, 3);
x_50 = lean_ctor_get(x_4, 4);
x_51 = lean_ctor_get(x_4, 5);
x_52 = lean_ctor_get(x_4, 6);
x_53 = lean_ctor_get(x_4, 7);
x_54 = lean_ctor_get(x_4, 8);
x_55 = lean_ctor_get(x_4, 9);
x_56 = lean_ctor_get(x_4, 10);
x_57 = lean_ctor_get(x_4, 11);
x_58 = lean_ctor_get(x_4, 12);
x_59 = lean_ctor_get(x_4, 13);
x_60 = lean_ctor_get(x_4, 14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_61 = l_Lean_MVarId_assert(x_46, x_43, x_2, x_1, x_8, x_9, x_10, x_11, x_44);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_ctor_set(x_4, 0, x_62);
x_64 = l_Lean_Meta_Grind_intros(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_63);
return x_64;
}
else
{
uint8_t x_65; 
lean_free_object(x_4);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_61, 0);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_61);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_69 = lean_ctor_get(x_4, 0);
x_70 = lean_ctor_get(x_4, 1);
x_71 = lean_ctor_get(x_4, 2);
x_72 = lean_ctor_get(x_4, 3);
x_73 = lean_ctor_get(x_4, 4);
x_74 = lean_ctor_get(x_4, 5);
x_75 = lean_ctor_get(x_4, 6);
x_76 = lean_ctor_get_uint8(x_4, sizeof(void*)*15);
x_77 = lean_ctor_get(x_4, 7);
x_78 = lean_ctor_get(x_4, 8);
x_79 = lean_ctor_get(x_4, 9);
x_80 = lean_ctor_get(x_4, 10);
x_81 = lean_ctor_get(x_4, 11);
x_82 = lean_ctor_get(x_4, 12);
x_83 = lean_ctor_get(x_4, 13);
x_84 = lean_ctor_get(x_4, 14);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_85 = l_Lean_MVarId_assert(x_69, x_43, x_2, x_1, x_8, x_9, x_10, x_11, x_44);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_70);
lean_ctor_set(x_88, 2, x_71);
lean_ctor_set(x_88, 3, x_72);
lean_ctor_set(x_88, 4, x_73);
lean_ctor_set(x_88, 5, x_74);
lean_ctor_set(x_88, 6, x_75);
lean_ctor_set(x_88, 7, x_77);
lean_ctor_set(x_88, 8, x_78);
lean_ctor_set(x_88, 9, x_79);
lean_ctor_set(x_88, 10, x_80);
lean_ctor_set(x_88, 11, x_81);
lean_ctor_set(x_88, 12, x_82);
lean_ctor_set(x_88, 13, x_83);
lean_ctor_set(x_88, 14, x_84);
lean_ctor_set_uint8(x_88, sizeof(void*)*15, x_76);
x_89 = l_Lean_Meta_Grind_intros(x_3, x_88, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_87);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_90 = lean_ctor_get(x_85, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_92 = x_85;
} else {
 lean_dec_ref(x_85);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertNext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get(x_1, 3);
x_15 = lean_ctor_get(x_1, 4);
x_16 = lean_ctor_get(x_1, 5);
x_17 = lean_ctor_get(x_1, 6);
x_18 = lean_ctor_get(x_1, 7);
x_19 = lean_ctor_get(x_1, 8);
x_20 = lean_ctor_get(x_1, 9);
x_21 = lean_ctor_get(x_1, 10);
x_22 = lean_ctor_get(x_1, 11);
x_23 = lean_ctor_get(x_1, 12);
x_24 = lean_ctor_get(x_1, 13);
x_25 = lean_ctor_get(x_1, 14);
x_26 = l_Std_Queue_dequeue_x3f___rarg(x_19);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_free_object(x_1);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_9);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 2);
lean_inc(x_35);
lean_dec(x_31);
lean_ctor_set(x_1, 8, x_32);
x_36 = l_Lean_Meta_Grind_assertAt(x_33, x_34, x_35, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_ctor_set(x_26, 0, x_38);
lean_ctor_set(x_36, 0, x_26);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_36);
lean_ctor_set(x_26, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_26);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_free_object(x_26);
x_42 = !lean_is_exclusive(x_36);
if (x_42 == 0)
{
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_36, 0);
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_36);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_26, 0);
lean_inc(x_46);
lean_dec(x_26);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 2);
lean_inc(x_51);
lean_dec(x_47);
lean_ctor_set(x_1, 8, x_48);
x_52 = l_Lean_Meta_Grind_assertAt(x_49, x_50, x_51, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_53);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_52, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_60 = x_52;
} else {
 lean_dec_ref(x_52);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_62 = lean_ctor_get(x_1, 0);
x_63 = lean_ctor_get(x_1, 1);
x_64 = lean_ctor_get(x_1, 2);
x_65 = lean_ctor_get(x_1, 3);
x_66 = lean_ctor_get(x_1, 4);
x_67 = lean_ctor_get(x_1, 5);
x_68 = lean_ctor_get(x_1, 6);
x_69 = lean_ctor_get_uint8(x_1, sizeof(void*)*15);
x_70 = lean_ctor_get(x_1, 7);
x_71 = lean_ctor_get(x_1, 8);
x_72 = lean_ctor_get(x_1, 9);
x_73 = lean_ctor_get(x_1, 10);
x_74 = lean_ctor_get(x_1, 11);
x_75 = lean_ctor_get(x_1, 12);
x_76 = lean_ctor_get(x_1, 13);
x_77 = lean_ctor_get(x_1, 14);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_1);
x_78 = l_Std_Queue_dequeue_x3f___rarg(x_71);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_9);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_82 = x_78;
} else {
 lean_dec_ref(x_78);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_83, 2);
lean_inc(x_87);
lean_dec(x_83);
x_88 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_88, 0, x_62);
lean_ctor_set(x_88, 1, x_63);
lean_ctor_set(x_88, 2, x_64);
lean_ctor_set(x_88, 3, x_65);
lean_ctor_set(x_88, 4, x_66);
lean_ctor_set(x_88, 5, x_67);
lean_ctor_set(x_88, 6, x_68);
lean_ctor_set(x_88, 7, x_70);
lean_ctor_set(x_88, 8, x_84);
lean_ctor_set(x_88, 9, x_72);
lean_ctor_set(x_88, 10, x_73);
lean_ctor_set(x_88, 11, x_74);
lean_ctor_set(x_88, 12, x_75);
lean_ctor_set(x_88, 13, x_76);
lean_ctor_set(x_88, 14, x_77);
lean_ctor_set_uint8(x_88, sizeof(void*)*15, x_69);
x_89 = l_Lean_Meta_Grind_assertAt(x_85, x_86, x_87, x_88, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_93 = lean_alloc_ctor(1, 1, 0);
} else {
 x_93 = x_82;
}
lean_ctor_set(x_93, 0, x_90);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_82);
x_95 = lean_ctor_get(x_89, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_89, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_97 = x_89;
} else {
 lean_dec_ref(x_89);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_assertAll___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_assertNext), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Meta_Grind_assertAll___closed__1;
x_11 = l_Lean_Meta_Grind_GrindTactic_iterate(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_CasesMatch(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Injection(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Core(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Combinators(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Intro(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Cases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Injection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Core(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Combinators(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_instInhabitedIntroResult___closed__1 = _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedIntroResult___closed__1);
l_Lean_Meta_Grind_instInhabitedIntroResult___closed__2 = _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedIntroResult___closed__2);
l_Lean_Meta_Grind_instInhabitedIntroResult___closed__3 = _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedIntroResult___closed__3);
l_Lean_Meta_Grind_instInhabitedIntroResult___closed__4 = _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedIntroResult___closed__4);
l_Lean_Meta_Grind_instInhabitedIntroResult___closed__5 = _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedIntroResult___closed__5);
l_Lean_Meta_Grind_instInhabitedIntroResult___closed__6 = _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedIntroResult___closed__6);
l_Lean_Meta_Grind_instInhabitedIntroResult___closed__7 = _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__7();
l_Lean_Meta_Grind_instInhabitedIntroResult___closed__8 = _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedIntroResult___closed__8);
l_Lean_Meta_Grind_instInhabitedIntroResult___closed__9 = _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedIntroResult___closed__9);
l_Lean_Meta_Grind_instInhabitedIntroResult___closed__10 = _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedIntroResult___closed__10);
l_Lean_Meta_Grind_instInhabitedIntroResult___closed__11 = _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedIntroResult___closed__11);
l_Lean_Meta_Grind_instInhabitedIntroResult___closed__12 = _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedIntroResult___closed__12);
l_Lean_Meta_Grind_instInhabitedIntroResult___closed__13 = _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedIntroResult___closed__13);
l_Lean_Meta_Grind_instInhabitedIntroResult___closed__14 = _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__14();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedIntroResult___closed__14);
l_Lean_Meta_Grind_instInhabitedIntroResult___closed__15 = _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__15();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedIntroResult___closed__15);
l_Lean_Meta_Grind_instInhabitedIntroResult___closed__16 = _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__16();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedIntroResult___closed__16);
l_Lean_Meta_Grind_instInhabitedIntroResult___closed__17 = _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__17();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedIntroResult___closed__17);
l_Lean_Meta_Grind_instInhabitedIntroResult___closed__18 = _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__18();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedIntroResult___closed__18);
l_Lean_Meta_Grind_instInhabitedIntroResult___closed__19 = _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__19();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedIntroResult___closed__19);
l_Lean_Meta_Grind_instInhabitedIntroResult___closed__20 = _init_l_Lean_Meta_Grind_instInhabitedIntroResult___closed__20();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedIntroResult___closed__20);
l_Lean_Meta_Grind_instInhabitedIntroResult = _init_l_Lean_Meta_Grind_instInhabitedIntroResult();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedIntroResult);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__1);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__2);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__4);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__2);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__3);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__1___closed__4);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__3___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__3___closed__1);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__4___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__4___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lambda__4___closed__1);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__2___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__2___closed__1);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__3___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__3___closed__1);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__3___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___lambda__3___closed__2);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__2);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__3);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__1);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__8___closed__2);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9___closed__1);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__9___closed__2);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__1);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__2);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__3);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__10___closed__4);
l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__11___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__11___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lambda__11___closed__1);
l_Lean_Meta_Grind_intros_go___lambda__3___closed__1 = _init_l_Lean_Meta_Grind_intros_go___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_intros_go___lambda__3___closed__1);
l_Lean_Meta_Grind_assertAt___lambda__1___closed__1 = _init_l_Lean_Meta_Grind_assertAt___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_assertAt___lambda__1___closed__1);
l_Lean_Meta_Grind_assertAt___lambda__1___closed__2 = _init_l_Lean_Meta_Grind_assertAt___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_assertAt___lambda__1___closed__2);
l_Lean_Meta_Grind_assertAt___lambda__1___closed__3 = _init_l_Lean_Meta_Grind_assertAt___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_assertAt___lambda__1___closed__3);
l_Lean_Meta_Grind_assertAt___lambda__1___closed__4 = _init_l_Lean_Meta_Grind_assertAt___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_assertAt___lambda__1___closed__4);
l_Lean_Meta_Grind_assertAll___closed__1 = _init_l_Lean_Meta_Grind_assertAll___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_assertAll___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
