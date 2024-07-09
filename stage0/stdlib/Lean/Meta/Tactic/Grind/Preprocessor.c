// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Preprocessor
// Imports: Init.Grind.Lemmas Lean.Meta.Canonicalizer Lean.Meta.Tactic.Util Lean.Meta.Tactic.Intro Lean.Meta.Tactic.Simp.Main Lean.Meta.Tactic.Grind.Attr Lean.Meta.Tactic.Grind.RevertAll Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Util Lean.Meta.Tactic.Grind.Cases Lean.Meta.Tactic.Grind.Injection Lean.Meta.Tactic.Grind.Core
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Grind_Preprocessor_introNext___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_map___at_Lean_Meta_Grind_Preprocessor_applyCases_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_injection_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__5;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_State_goals___default;
LEAN_EXPORT lean_object* l_List_map___at_Lean_Meta_Grind_Preprocessor_applyCases_x3f___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__2;
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__4;
uint32_t l_UInt32_ofNatTruncate(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Meta_Grind_Preprocessor_introNext___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__4;
uint8_t l_Lean_Expr_isLet(lean_object*);
static uint32_t l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__5;
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Grind_Preprocessor_introNext___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__5;
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_applyCases_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__2;
static lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__6;
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__3;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_toList___rarg(lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__6;
lean_object* l_Lean_MVarId_revertAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__7;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_Grind_Preprocessor_introNext___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_simp___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__4;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static size_t l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__2;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_Grind_Preprocessor_introNext___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_simp___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__1;
lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__1;
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__6;
static lean_object* l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__3;
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_simp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_main___closed__2;
static lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__3;
static lean_object* l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__6;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_pushResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isGrindCasesTarget(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__3;
lean_object* l_ShareCommon_mkStateImpl(lean_object*);
lean_object* l_Lean_FVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Grind_Preprocessor_introNext___spec__4___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__6;
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_Preprocessor_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
lean_object* l_Lean_MVarId_clearAuxDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_State_simpStats___default;
lean_object* l_Lean_MVarId_abstractNestedProofs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Grind_Preprocessor_introNext___spec__4___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
extern lean_object* l_Lean_Meta_Grind_grindNormSimprocExt;
static lean_object* l_Lean_Meta_Grind_main___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_simp(lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedContext;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_PreM_run(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_isCasesCandidate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Meta_Grind_Preprocessor_introNext___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_ensureNoMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_applyCases_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_main___closed__4;
lean_object* l_Lean_Meta_Grind_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_main___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__6___boxed(lean_object**);
static lean_object* l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__4;
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Meta_Grind_Preprocessor_introNext___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_grindNormExt;
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_pushResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_applyInjection_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_transformTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Meta_Grind_main___closed__5;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Meta_Grind_Preprocessor_introNext___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_byContra_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Meta_Grind_mkInputClause(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_ensureProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Simp_defaultMaxSteps;
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__8;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Meta_Grind_Preprocessor_introNext___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___boxed(lean_object**);
lean_object* l_Lean_Meta_Grind_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Meta_Grind_Preprocessor_introNext___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_map___at_Lean_Meta_Grind_main___spec__1(lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_loop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedState;
lean_object* l_Lean_Meta_Grind_mkGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_ShareCommon_objectFactory;
static lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__1;
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__1;
lean_object* l_Lean_Meta_Grind_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__2;
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__5;
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_isCasesCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingInfo_x21(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_betaReduce___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_applyCases_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 19);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 3, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 4, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 5, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 6, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 7, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 8, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 9, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 10, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 11, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 12, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 13, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 14, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 15, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 16, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 17, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 18, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__3;
x_3 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__5;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__7() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_1 = 0;
x_2 = lean_box(0);
x_3 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__1;
x_4 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__2;
x_5 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__6;
x_6 = lean_unsigned_to_nat(0u);
x_7 = 0;
x_8 = lean_alloc_ctor(0, 5, 9);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_2);
lean_ctor_set(x_8, 4, x_6);
lean_ctor_set_uint32(x_8, sizeof(void*)*5, x_1);
lean_ctor_set_uint32(x_8, sizeof(void*)*5 + 4, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*5 + 8, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__7;
x_2 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__8;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__4() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__3;
x_3 = l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__2;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__5;
x_2 = l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__4;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__1;
x_2 = l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_State_simpStats___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_State_goals___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__2() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__1;
x_2 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__2;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__2;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set_usize(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__5;
x_2 = l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__3;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__1;
x_2 = l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__5;
x_2 = l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_grindNormExt;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_grindNormSimprocExt;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Simp_defaultMaxSteps;
x_2 = lean_unsigned_to_nat(2u);
x_3 = 0;
x_4 = 1;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 2, 19);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 4, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 5, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 6, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 7, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 8, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 9, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 10, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 11, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 12, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 13, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 14, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 15, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 16, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 17, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 18, x_3);
return x_6;
}
}
static uint32_t _init_l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__5() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_UInt32_ofNatTruncate(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__6;
x_2 = l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_9 = l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__1;
x_10 = l_Lean_Meta_SimpExtension_getTheorems(x_9, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__2;
x_14 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs(x_13, x_6, x_7, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__3;
x_18 = lean_array_push(x_17, x_15);
x_19 = l_Lean_Meta_getSimpCongrTheorems___rarg(x_7, x_16);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint32_t x_25; lean_object* x_26; uint32_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_array_push(x_17, x_11);
x_24 = lean_box(0);
x_25 = 0;
x_26 = l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__4;
x_27 = l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__5;
x_28 = lean_unsigned_to_nat(0u);
x_29 = 0;
x_30 = lean_alloc_ctor(0, 5, 9);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_21);
lean_ctor_set(x_30, 3, x_24);
lean_ctor_set(x_30, 4, x_28);
lean_ctor_set_uint32(x_30, sizeof(void*)*5, x_27);
lean_ctor_set_uint32(x_30, sizeof(void*)*5 + 4, x_25);
lean_ctor_set_uint8(x_30, sizeof(void*)*5 + 8, x_29);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 0, x_30);
x_31 = l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__6;
x_32 = lean_st_mk_ref(x_31, x_22);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_33);
x_35 = lean_apply_9(x_1, x_19, x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_st_ref_get(x_33, x_37);
lean_dec(x_33);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_36);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_33);
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
return x_35;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_35, 0);
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_35);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint32_t x_51; lean_object* x_52; uint32_t x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_47 = lean_ctor_get(x_19, 0);
x_48 = lean_ctor_get(x_19, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_19);
x_49 = lean_array_push(x_17, x_11);
x_50 = lean_box(0);
x_51 = 0;
x_52 = l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__4;
x_53 = l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__5;
x_54 = lean_unsigned_to_nat(0u);
x_55 = 0;
x_56 = lean_alloc_ctor(0, 5, 9);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_49);
lean_ctor_set(x_56, 2, x_47);
lean_ctor_set(x_56, 3, x_50);
lean_ctor_set(x_56, 4, x_54);
lean_ctor_set_uint32(x_56, sizeof(void*)*5, x_53);
lean_ctor_set_uint32(x_56, sizeof(void*)*5 + 4, x_51);
lean_ctor_set_uint8(x_56, sizeof(void*)*5 + 8, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_18);
x_58 = l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__6;
x_59 = lean_st_mk_ref(x_58, x_48);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_60);
x_62 = lean_apply_9(x_1, x_57, x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_st_ref_get(x_60, x_64);
lean_dec(x_60);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_60);
x_69 = lean_ctor_get(x_62, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_62, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_71 = x_62;
} else {
 lean_dec_ref(x_62);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_PreM_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_simp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_st_ref_get(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_box(0);
x_18 = l_Lean_Meta_simp(x_1, x_15, x_16, x_17, x_14, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_st_ref_take(x_3, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
lean_ctor_set(x_24, 0, x_22);
x_28 = lean_st_ref_set(x_3, x_24, x_25);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_21);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_st_ref_set(x_3, x_34, x_25);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_simp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_simp___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_simp___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Preprocessor_simp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_simp___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Preprocessor_simp(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_Grind_Preprocessor_introNext___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_apply_10(x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_Grind_Preprocessor_introNext___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_Preprocessor_introNext___spec__1___rarg), 11, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Meta_Grind_Preprocessor_introNext___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Meta_Grind_Preprocessor_introNext___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at_Lean_Meta_Grind_Preprocessor_introNext___spec__2___rarg), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Grind_Preprocessor_introNext___spec__4___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
x_25 = lean_ctor_get(x_14, 3);
x_26 = lean_ctor_get(x_14, 4);
x_27 = lean_ctor_get(x_14, 5);
x_28 = lean_ctor_get(x_14, 6);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_29 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_5);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
lean_ctor_set(x_29, 5, x_27);
lean_ctor_set(x_29, 6, x_28);
x_30 = lean_st_ref_set(x_1, x_29, x_15);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_10);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_34 = lean_ctor_get(x_5, 0);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_5);
lean_inc(x_35);
lean_inc(x_34);
x_36 = l_Lean_Name_num___override(x_34, x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_35, x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_st_ref_take(x_1, x_6);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_41, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_41, 5);
lean_inc(x_47);
x_48 = lean_ctor_get(x_41, 6);
lean_inc(x_48);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 lean_ctor_release(x_41, 4);
 lean_ctor_release(x_41, 5);
 lean_ctor_release(x_41, 6);
 x_49 = x_41;
} else {
 lean_dec_ref(x_41);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 7, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_44);
lean_ctor_set(x_50, 2, x_39);
lean_ctor_set(x_50, 3, x_45);
lean_ctor_set(x_50, 4, x_46);
lean_ctor_set(x_50, 5, x_47);
lean_ctor_set(x_50, 6, x_48);
x_51 = lean_st_ref_set(x_1, x_50, x_42);
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
lean_ctor_set(x_54, 0, x_36);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Grind_Preprocessor_introNext___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at_Lean_Meta_Grind_Preprocessor_introNext___spec__4___rarg___boxed), 2, 0);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Meta_Grind_Preprocessor_introNext___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_mkFreshId___at_Lean_Meta_Grind_Preprocessor_introNext___spec__4___rarg(x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Meta_Grind_Preprocessor_introNext___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_st_ref_take(x_8, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_14, 7);
x_20 = l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(x_19, x_1, x_2);
lean_ctor_set(x_14, 7, x_20);
x_21 = lean_st_ref_set(x_8, x_13, x_15);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
x_30 = lean_ctor_get(x_14, 2);
x_31 = lean_ctor_get(x_14, 3);
x_32 = lean_ctor_get(x_14, 4);
x_33 = lean_ctor_get(x_14, 5);
x_34 = lean_ctor_get(x_14, 6);
x_35 = lean_ctor_get(x_14, 7);
x_36 = lean_ctor_get(x_14, 8);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_37 = l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(x_35, x_1, x_2);
x_38 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set(x_38, 1, x_29);
lean_ctor_set(x_38, 2, x_30);
lean_ctor_set(x_38, 3, x_31);
lean_ctor_set(x_38, 4, x_32);
lean_ctor_set(x_38, 5, x_33);
lean_ctor_set(x_38, 6, x_34);
lean_ctor_set(x_38, 7, x_37);
lean_ctor_set(x_38, 8, x_36);
lean_ctor_set(x_13, 0, x_38);
x_39 = lean_st_ref_set(x_8, x_13, x_15);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
x_42 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_44 = lean_ctor_get(x_13, 1);
x_45 = lean_ctor_get(x_13, 2);
x_46 = lean_ctor_get(x_13, 3);
x_47 = lean_ctor_get(x_13, 4);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_13);
x_48 = lean_ctor_get(x_14, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_14, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_14, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_14, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_14, 4);
lean_inc(x_52);
x_53 = lean_ctor_get(x_14, 5);
lean_inc(x_53);
x_54 = lean_ctor_get(x_14, 6);
lean_inc(x_54);
x_55 = lean_ctor_get(x_14, 7);
lean_inc(x_55);
x_56 = lean_ctor_get(x_14, 8);
lean_inc(x_56);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 lean_ctor_release(x_14, 5);
 lean_ctor_release(x_14, 6);
 lean_ctor_release(x_14, 7);
 lean_ctor_release(x_14, 8);
 x_57 = x_14;
} else {
 lean_dec_ref(x_14);
 x_57 = lean_box(0);
}
x_58 = l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(x_55, x_1, x_2);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 9, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_48);
lean_ctor_set(x_59, 1, x_49);
lean_ctor_set(x_59, 2, x_50);
lean_ctor_set(x_59, 3, x_51);
lean_ctor_set(x_59, 4, x_52);
lean_ctor_set(x_59, 5, x_53);
lean_ctor_set(x_59, 6, x_54);
lean_ctor_set(x_59, 7, x_58);
lean_ctor_set(x_59, 8, x_56);
x_60 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_44);
lean_ctor_set(x_60, 2, x_45);
lean_ctor_set(x_60, 3, x_46);
lean_ctor_set(x_60, 4, x_47);
x_61 = lean_st_ref_set(x_8, x_60, x_15);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_FVarId_getDecl(x_1, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_LocalDecl_type(x_8);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_18);
x_19 = l_Lean_Meta_isProp(x_18, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_2);
lean_ctor_set(x_24, 2, x_3);
lean_ctor_set(x_24, 3, x_4);
lean_ctor_set(x_24, 4, x_6);
lean_ctor_set_uint8(x_24, sizeof(void*)*5, x_5);
x_25 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_2);
lean_ctor_set(x_27, 2, x_3);
lean_ctor_set(x_27, 3, x_4);
lean_ctor_set(x_27, 4, x_6);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_5);
x_28 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_dec(x_19);
x_31 = l_Lean_LocalDecl_userName(x_8);
x_32 = l_Lean_Expr_fvar___override(x_7);
x_33 = l_Lean_MVarId_assert(x_1, x_31, x_18, x_32, x_13, x_14, x_15, x_16, x_30);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_2);
lean_ctor_set(x_36, 2, x_3);
lean_ctor_set(x_36, 3, x_4);
lean_ctor_set(x_36, 4, x_6);
lean_ctor_set_uint8(x_36, sizeof(void*)*5, x_5);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_33, 0, x_37);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
x_40 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_2);
lean_ctor_set(x_40, 2, x_3);
lean_ctor_set(x_40, 3, x_4);
lean_ctor_set(x_40, 4, x_6);
lean_ctor_set_uint8(x_40, sizeof(void*)*5, x_5);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_33);
if (x_43 == 0)
{
return x_33;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_33, 0);
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_33);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_19);
if (x_47 == 0)
{
return x_19;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_19, 0);
x_49 = lean_ctor_get(x_19, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_19);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_isProp(x_1, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = 0;
x_13 = 1;
x_14 = 1;
x_15 = l_Lean_Meta_mkLambdaFVars(x_1, x_2, x_12, x_13, x_12, x_14, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("intro_with_eq", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__1;
x_2 = l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__2;
x_3 = l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22) {
_start:
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_24 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_Preprocessor_introNext___spec__5(x_2, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_27, 2, x_5);
lean_ctor_set(x_27, 3, x_6);
lean_ctor_set(x_27, 4, x_8);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_9);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_30, 0, x_3);
lean_ctor_set(x_30, 1, x_4);
lean_ctor_set(x_30, 2, x_5);
lean_ctor_set(x_30, 3, x_6);
lean_ctor_set(x_30, 4, x_8);
lean_ctor_set_uint8(x_30, sizeof(void*)*5, x_7);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_9);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
lean_dec(x_23);
x_34 = l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__6;
x_35 = lean_array_push(x_34, x_10);
x_36 = lean_array_push(x_35, x_11);
x_37 = lean_array_push(x_36, x_12);
x_38 = lean_array_push(x_37, x_33);
x_39 = lean_array_push(x_38, x_13);
x_40 = l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__5;
x_41 = l_Lean_mkAppN(x_40, x_39);
lean_dec(x_39);
x_42 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_Preprocessor_introNext___spec__5(x_2, x_41, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_45, 0, x_3);
lean_ctor_set(x_45, 1, x_4);
lean_ctor_set(x_45, 2, x_5);
lean_ctor_set(x_45, 3, x_6);
lean_ctor_set(x_45, 4, x_8);
lean_ctor_set_uint8(x_45, sizeof(void*)*5, x_7);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_9);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_42, 0, x_46);
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_dec(x_42);
x_48 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_48, 0, x_3);
lean_ctor_set(x_48, 1, x_4);
lean_ctor_set(x_48, 2, x_5);
lean_ctor_set(x_48, 3, x_6);
lean_ctor_set(x_48, 4, x_8);
lean_ctor_set_uint8(x_48, sizeof(void*)*5, x_7);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_9);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
if (x_9 == 0)
{
uint8_t x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_19 = 1;
x_20 = l_Lean_Meta_intro1Core(x_1, x_19, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 1);
x_25 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_2);
lean_ctor_set(x_25, 2, x_3);
lean_ctor_set(x_25, 3, x_4);
lean_ctor_set(x_25, 4, x_6);
lean_ctor_set_uint8(x_25, sizeof(void*)*5, x_5);
lean_ctor_set_tag(x_22, 3);
lean_ctor_set(x_22, 1, x_25);
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_3);
lean_ctor_set(x_28, 3, x_4);
lean_ctor_set(x_28, 4, x_6);
lean_ctor_set_uint8(x_28, sizeof(void*)*5, x_5);
x_29 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_20, 0, x_29);
return x_20;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_20);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_34 = x_30;
} else {
 lean_dec_ref(x_30);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_2);
lean_ctor_set(x_35, 2, x_3);
lean_ctor_set(x_35, 3, x_4);
lean_ctor_set(x_35, 4, x_6);
lean_ctor_set_uint8(x_35, sizeof(void*)*5, x_5);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(3, 2, 0);
} else {
 x_36 = x_34;
 lean_ctor_set_tag(x_36, 3);
}
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_20);
if (x_38 == 0)
{
return x_20;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_20, 0);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_20);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; 
lean_inc(x_1);
x_42 = l_Lean_MVarId_getTag(x_1, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Expr_bindingBody_x21(x_7);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_10);
lean_inc(x_8);
x_46 = l_Lean_Meta_Grind_Preprocessor_simp___rarg(x_8, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_44);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_50 = l_Lean_Meta_Grind_canon(x_49, x_12, x_13, x_14, x_15, x_16, x_17, x_48);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Meta_Grind_shareCommon(x_51, x_12, x_13, x_14, x_15, x_16, x_17, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_mkFreshFVarId___at_Lean_Meta_Grind_Preprocessor_introNext___spec__3(x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_14, 1);
lean_inc(x_59);
x_60 = l_Lean_Expr_bindingName_x21(x_7);
x_61 = l_Lean_Expr_bindingInfo_x21(x_7);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
x_63 = 0;
lean_inc(x_54);
lean_inc(x_57);
x_64 = l_Lean_LocalContext_mkLocalDecl(x_59, x_57, x_60, x_54, x_62, x_63);
x_65 = l_Lean_Meta_getLocalInstances(x_14, x_15, x_16, x_17, x_58);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = 2;
x_69 = lean_unsigned_to_nat(0u);
lean_inc(x_45);
x_70 = l_Lean_Meta_mkFreshExprMVarAt(x_64, x_66, x_45, x_68, x_43, x_69, x_14, x_15, x_16, x_17, x_67);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Expr_mvarId_x21(x_71);
lean_inc(x_57);
x_74 = l_Lean_Expr_fvar___override(x_57);
x_75 = l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__3;
x_76 = lean_array_push(x_75, x_74);
x_77 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_introNext___lambda__4___boxed), 11, 2);
lean_closure_set(x_77, 0, x_76);
lean_closure_set(x_77, 1, x_71);
x_78 = lean_box(x_5);
lean_inc(x_73);
x_79 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___boxed), 22, 12);
lean_closure_set(x_79, 0, x_47);
lean_closure_set(x_79, 1, x_1);
lean_closure_set(x_79, 2, x_73);
lean_closure_set(x_79, 3, x_2);
lean_closure_set(x_79, 4, x_3);
lean_closure_set(x_79, 5, x_4);
lean_closure_set(x_79, 6, x_78);
lean_closure_set(x_79, 7, x_6);
lean_closure_set(x_79, 8, x_57);
lean_closure_set(x_79, 9, x_8);
lean_closure_set(x_79, 10, x_54);
lean_closure_set(x_79, 11, x_45);
x_80 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_Preprocessor_introNext___spec__1___rarg), 11, 2);
lean_closure_set(x_80, 0, x_77);
lean_closure_set(x_80, 1, x_79);
x_81 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_Preprocessor_introNext___spec__2___rarg(x_73, x_80, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_72);
return x_81;
}
else
{
uint8_t x_82; 
lean_dec(x_47);
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_50);
if (x_82 == 0)
{
return x_50;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_50, 0);
x_84 = lean_ctor_get(x_50, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_50);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_46);
if (x_86 == 0)
{
return x_46;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_46, 0);
x_88 = lean_ctor_get(x_46, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_46);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_42);
if (x_90 == 0)
{
return x_42;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_42, 0);
x_92 = lean_ctor_get(x_42, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_42);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_16 = lean_ctor_get(x_1, 4);
lean_inc(x_16);
lean_dec(x_1);
lean_inc(x_11);
x_17 = l_Lean_MVarId_getType(x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_38; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_38 = l_Lean_Expr_isArrow(x_19);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = l_Lean_Expr_isLet(x_19);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = l_Lean_Expr_isForall(x_19);
lean_dec(x_19);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_box(0);
lean_ctor_set(x_17, 0, x_41);
return x_17;
}
else
{
lean_object* x_42; 
lean_free_object(x_17);
x_42 = lean_box(0);
x_21 = x_42;
goto block_37;
}
}
else
{
lean_object* x_43; 
lean_free_object(x_17);
lean_dec(x_19);
x_43 = lean_box(0);
x_21 = x_43;
goto block_37;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_free_object(x_17);
x_44 = l_Lean_Expr_bindingDomain_x21(x_19);
lean_inc(x_44);
x_45 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_introNext___lambda__3___boxed), 10, 1);
lean_closure_set(x_45, 0, x_44);
x_46 = lean_box(x_15);
lean_inc(x_11);
x_47 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_introNext___lambda__6___boxed), 18, 8);
lean_closure_set(x_47, 0, x_11);
lean_closure_set(x_47, 1, x_12);
lean_closure_set(x_47, 2, x_13);
lean_closure_set(x_47, 3, x_14);
lean_closure_set(x_47, 4, x_46);
lean_closure_set(x_47, 5, x_16);
lean_closure_set(x_47, 6, x_19);
lean_closure_set(x_47, 7, x_44);
x_48 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_Preprocessor_introNext___spec__1___rarg), 11, 2);
lean_closure_set(x_48, 0, x_45);
lean_closure_set(x_48, 1, x_47);
x_49 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_Preprocessor_introNext___spec__2___rarg(x_11, x_48, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
return x_49;
}
block_37:
{
uint8_t x_22; lean_object* x_23; 
lean_dec(x_21);
x_22 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_23 = l_Lean_Meta_intro1Core(x_11, x_22, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
lean_inc(x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_introNext___lambda__1___boxed), 10, 1);
lean_closure_set(x_28, 0, x_26);
x_29 = lean_box(x_15);
lean_inc(x_27);
x_30 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_introNext___lambda__2___boxed), 17, 7);
lean_closure_set(x_30, 0, x_27);
lean_closure_set(x_30, 1, x_12);
lean_closure_set(x_30, 2, x_13);
lean_closure_set(x_30, 3, x_14);
lean_closure_set(x_30, 4, x_29);
lean_closure_set(x_30, 5, x_16);
lean_closure_set(x_30, 6, x_26);
x_31 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_Preprocessor_introNext___spec__1___rarg), 11, 2);
lean_closure_set(x_31, 0, x_28);
lean_closure_set(x_31, 1, x_30);
x_32 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_Preprocessor_introNext___spec__2___rarg(x_27, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_25);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_69; 
x_50 = lean_ctor_get(x_17, 0);
x_51 = lean_ctor_get(x_17, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_17);
x_69 = l_Lean_Expr_isArrow(x_50);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l_Lean_Expr_isLet(x_50);
if (x_70 == 0)
{
uint8_t x_71; 
x_71 = l_Lean_Expr_isForall(x_50);
lean_dec(x_50);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_51);
return x_73;
}
else
{
lean_object* x_74; 
x_74 = lean_box(0);
x_52 = x_74;
goto block_68;
}
}
else
{
lean_object* x_75; 
lean_dec(x_50);
x_75 = lean_box(0);
x_52 = x_75;
goto block_68;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = l_Lean_Expr_bindingDomain_x21(x_50);
lean_inc(x_76);
x_77 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_introNext___lambda__3___boxed), 10, 1);
lean_closure_set(x_77, 0, x_76);
x_78 = lean_box(x_15);
lean_inc(x_11);
x_79 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_introNext___lambda__6___boxed), 18, 8);
lean_closure_set(x_79, 0, x_11);
lean_closure_set(x_79, 1, x_12);
lean_closure_set(x_79, 2, x_13);
lean_closure_set(x_79, 3, x_14);
lean_closure_set(x_79, 4, x_78);
lean_closure_set(x_79, 5, x_16);
lean_closure_set(x_79, 6, x_50);
lean_closure_set(x_79, 7, x_76);
x_80 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_Preprocessor_introNext___spec__1___rarg), 11, 2);
lean_closure_set(x_80, 0, x_77);
lean_closure_set(x_80, 1, x_79);
x_81 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_Preprocessor_introNext___spec__2___rarg(x_11, x_80, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_51);
return x_81;
}
block_68:
{
uint8_t x_53; lean_object* x_54; 
lean_dec(x_52);
x_53 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_54 = l_Lean_Meta_intro1Core(x_11, x_53, x_6, x_7, x_8, x_9, x_51);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
lean_inc(x_57);
x_59 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_introNext___lambda__1___boxed), 10, 1);
lean_closure_set(x_59, 0, x_57);
x_60 = lean_box(x_15);
lean_inc(x_58);
x_61 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_introNext___lambda__2___boxed), 17, 7);
lean_closure_set(x_61, 0, x_58);
lean_closure_set(x_61, 1, x_12);
lean_closure_set(x_61, 2, x_13);
lean_closure_set(x_61, 3, x_14);
lean_closure_set(x_61, 4, x_60);
lean_closure_set(x_61, 5, x_16);
lean_closure_set(x_61, 6, x_57);
x_62 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_Preprocessor_introNext___spec__1___rarg), 11, 2);
lean_closure_set(x_62, 0, x_59);
lean_closure_set(x_62, 1, x_61);
x_63 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_Preprocessor_introNext___spec__2___rarg(x_58, x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_56);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
uint8_t x_82; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_17);
if (x_82 == 0)
{
return x_17;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_17, 0);
x_84 = lean_ctor_get(x_17, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_17);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Grind_Preprocessor_introNext___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at_Lean_Meta_Grind_Preprocessor_introNext___spec__4___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Meta_Grind_Preprocessor_introNext___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkFreshId___at_Lean_Meta_Grind_Preprocessor_introNext___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Meta_Grind_Preprocessor_introNext___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_mkFreshFVarId___at_Lean_Meta_Grind_Preprocessor_introNext___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Meta_Grind_Preprocessor_introNext___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_Preprocessor_introNext___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Preprocessor_introNext___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__2___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_5);
lean_dec(x_5);
x_19 = l_Lean_Meta_Grind_Preprocessor_introNext___lambda__2(x_1, x_2, x_3, x_4, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Preprocessor_introNext___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Preprocessor_introNext___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_23; lean_object* x_24; 
x_23 = lean_unbox(x_7);
lean_dec(x_7);
x_24 = l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_23, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__6___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_5);
lean_dec(x_5);
x_20 = lean_unbox(x_9);
lean_dec(x_9);
x_21 = l_Lean_Meta_Grind_Preprocessor_introNext___lambda__6(x_1, x_2, x_3, x_4, x_19, x_6, x_7, x_8, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_7);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_pushResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_st_ref_take(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_PersistentArray_push___rarg(x_15, x_1);
lean_ctor_set(x_12, 1, x_16);
x_17 = lean_st_ref_set(x_3, x_12, x_13);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = l_Lean_PersistentArray_push___rarg(x_25, x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_st_ref_set(x_3, x_27, x_13);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
x_31 = lean_box(0);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_pushResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Preprocessor_pushResult(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_isCasesCandidate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_FVarId_getType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_Expr_getAppFn(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Meta_Grind_isGrindCasesTarget(x_12, x_4, x_5, x_10);
lean_dec(x_12);
return x_13;
}
else
{
uint8_t x_14; lean_object* x_15; 
lean_dec(x_11);
x_14 = 0;
x_15 = lean_box(x_14);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = l_Lean_Expr_getAppFn(x_16);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 4)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Meta_Grind_isGrindCasesTarget(x_19, x_4, x_5, x_17);
lean_dec(x_19);
return x_20;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_18);
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
return x_7;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_isCasesCandidate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_Preprocessor_isCasesCandidate(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_map___at_Lean_Meta_Grind_Preprocessor_applyCases_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_9);
lean_ctor_set(x_12, 4, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_10);
x_13 = l_List_map___at_Lean_Meta_Grind_Preprocessor_applyCases_x3f___spec__1(x_1, x_6);
lean_ctor_set(x_2, 1, x_13);
lean_ctor_set(x_2, 0, x_12);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_1, 2);
x_18 = lean_ctor_get(x_1, 3);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_20 = lean_ctor_get(x_1, 4);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_21 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_16);
lean_ctor_set(x_21, 2, x_17);
lean_ctor_set(x_21, 3, x_18);
lean_ctor_set(x_21, 4, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_19);
x_22 = l_List_map___at_Lean_Meta_Grind_Preprocessor_applyCases_x3f___spec__1(x_1, x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_applyCases_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_4);
lean_inc(x_1);
x_9 = l_Lean_Meta_Grind_Preprocessor_isCasesCandidate(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = l_Lean_Meta_Grind_cases(x_2, x_1, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_List_map___at_Lean_Meta_Grind_Preprocessor_applyCases_x3f___spec__1(x_3, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = l_List_map___at_Lean_Meta_Grind_Preprocessor_applyCases_x3f___spec__1(x_3, x_24);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
return x_19;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_9);
if (x_33 == 0)
{
return x_9;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_applyCases_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_applyCases_x3f___lambda__1___boxed), 8, 3);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_1);
x_10 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_map___at_Lean_Meta_Grind_Preprocessor_applyCases_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___at_Lean_Meta_Grind_Preprocessor_applyCases_x3f___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_applyCases_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_Preprocessor_applyCases_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_applyInjection_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_ctor_get(x_1, 4);
x_14 = l_Lean_Meta_Grind_injection_x3f(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_14, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_1, 0, x_25);
lean_ctor_set(x_15, 0, x_1);
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
lean_ctor_set(x_1, 0, x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_14, 0, x_27);
return x_14;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_ctor_get(x_15, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_30 = x_15;
} else {
 lean_dec_ref(x_15);
 x_30 = lean_box(0);
}
lean_ctor_set(x_1, 0, x_29);
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 1, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
return x_14;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_14);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
x_39 = lean_ctor_get(x_1, 2);
x_40 = lean_ctor_get(x_1, 3);
x_41 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_42 = lean_ctor_get(x_1, 4);
lean_inc(x_42);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_43 = l_Lean_Meta_Grind_injection_x3f(x_37, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_47 = lean_box(0);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_50 = x_43;
} else {
 lean_dec_ref(x_43);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_44, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_52 = x_44;
} else {
 lean_dec_ref(x_44);
 x_52 = lean_box(0);
}
x_53 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_38);
lean_ctor_set(x_53, 2, x_39);
lean_ctor_set(x_53, 3, x_40);
lean_ctor_set(x_53, 4, x_42);
lean_ctor_set_uint8(x_53, sizeof(void*)*5, x_41);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
if (lean_is_scalar(x_50)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_50;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
x_56 = lean_ctor_get(x_43, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_43, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_58 = x_43;
} else {
 lean_dec_ref(x_43);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_Preprocessor_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_Meta_Grind_Preprocessor_loop(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_1 = x_14;
x_10 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_mkInputClause(x_1, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Lean_Meta_Grind_Preprocessor_introNext(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 3);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_19 = lean_ctor_get(x_1, 4);
lean_inc(x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_MVarId_byContra_x3f(x_14, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_Grind_Preprocessor_pushResult(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_1);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_1, 4);
lean_dec(x_25);
x_26 = lean_ctor_get(x_1, 3);
lean_dec(x_26);
x_27 = lean_ctor_get(x_1, 2);
lean_dec(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_1, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_ctor_get(x_21, 0);
lean_inc(x_31);
lean_dec(x_21);
lean_ctor_set(x_1, 0, x_31);
x_10 = x_30;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_dec(x_20);
x_34 = lean_ctor_get(x_21, 0);
lean_inc(x_34);
lean_dec(x_21);
x_35 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_15);
lean_ctor_set(x_35, 2, x_16);
lean_ctor_set(x_35, 3, x_17);
lean_ctor_set(x_35, 4, x_19);
lean_ctor_set_uint8(x_35, sizeof(void*)*5, x_18);
x_1 = x_35;
x_10 = x_33;
goto _start;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
case 1:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_1);
x_41 = lean_ctor_get(x_11, 1);
lean_inc(x_41);
lean_dec(x_11);
x_42 = lean_ctor_get(x_12, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_12, 1);
lean_inc(x_43);
lean_dec(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_42);
lean_inc(x_43);
x_44 = l_Lean_Meta_Grind_Preprocessor_applyCases_x3f(x_43, x_42, x_6, x_7, x_8, x_9, x_41);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_42);
lean_inc(x_43);
x_47 = l_Lean_Meta_Grind_Preprocessor_applyInjection_x3f(x_43, x_42, x_6, x_7, x_8, x_9, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = !lean_is_exclusive(x_43);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_43, 0);
x_52 = lean_ctor_get(x_43, 1);
x_53 = lean_ctor_get(x_43, 2);
x_54 = lean_ctor_get(x_43, 3);
x_55 = lean_ctor_get(x_43, 4);
x_56 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_loop___lambda__1___boxed), 10, 1);
lean_closure_set(x_56, 0, x_42);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_51);
x_57 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_Preprocessor_introNext___spec__2___rarg(x_51, x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_49);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_PersistentArray_push___rarg(x_52, x_58);
lean_ctor_set(x_43, 1, x_60);
x_1 = x_43;
x_10 = x_59;
goto _start;
}
else
{
uint8_t x_62; 
lean_free_object(x_43);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_57);
if (x_62 == 0)
{
return x_57;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_57, 0);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_57);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_66 = lean_ctor_get(x_43, 0);
x_67 = lean_ctor_get(x_43, 1);
x_68 = lean_ctor_get(x_43, 2);
x_69 = lean_ctor_get(x_43, 3);
x_70 = lean_ctor_get_uint8(x_43, sizeof(void*)*5);
x_71 = lean_ctor_get(x_43, 4);
lean_inc(x_71);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_43);
x_72 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_loop___lambda__1___boxed), 10, 1);
lean_closure_set(x_72, 0, x_42);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_66);
x_73 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_Preprocessor_introNext___spec__2___rarg(x_66, x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_49);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_PersistentArray_push___rarg(x_67, x_74);
x_77 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_77, 0, x_66);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_77, 2, x_68);
lean_ctor_set(x_77, 3, x_69);
lean_ctor_set(x_77, 4, x_71);
lean_ctor_set_uint8(x_77, sizeof(void*)*5, x_70);
x_1 = x_77;
x_10 = x_75;
goto _start;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_79 = lean_ctor_get(x_73, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_73, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_81 = x_73;
} else {
 lean_dec_ref(x_73);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_43);
lean_dec(x_42);
x_83 = lean_ctor_get(x_47, 1);
lean_inc(x_83);
lean_dec(x_47);
x_84 = lean_ctor_get(x_48, 0);
lean_inc(x_84);
lean_dec(x_48);
x_1 = x_84;
x_10 = x_83;
goto _start;
}
}
else
{
uint8_t x_86; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_47);
if (x_86 == 0)
{
return x_47;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_47, 0);
x_88 = lean_ctor_get(x_47, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_47);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_43);
lean_dec(x_42);
x_90 = lean_ctor_get(x_44, 1);
lean_inc(x_90);
lean_dec(x_44);
x_91 = lean_ctor_get(x_45, 0);
lean_inc(x_91);
lean_dec(x_45);
x_92 = l_List_forM___at_Lean_Meta_Grind_Preprocessor_loop___spec__1(x_91, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_90);
return x_92;
}
}
else
{
uint8_t x_93; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_93 = !lean_is_exclusive(x_44);
if (x_93 == 0)
{
return x_44;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_44, 0);
x_95 = lean_ctor_get(x_44, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_44);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
case 2:
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_1);
x_97 = lean_ctor_get(x_11, 1);
lean_inc(x_97);
lean_dec(x_11);
x_98 = lean_ctor_get(x_12, 0);
lean_inc(x_98);
lean_dec(x_12);
x_1 = x_98;
x_10 = x_97;
goto _start;
}
default: 
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_1);
x_100 = lean_ctor_get(x_11, 1);
lean_inc(x_100);
lean_dec(x_11);
x_101 = lean_ctor_get(x_12, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_12, 1);
lean_inc(x_102);
lean_dec(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_102);
x_103 = l_Lean_Meta_Grind_Preprocessor_applyCases_x3f(x_102, x_101, x_6, x_7, x_8, x_9, x_100);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_1 = x_102;
x_10 = x_105;
goto _start;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_102);
x_107 = lean_ctor_get(x_103, 1);
lean_inc(x_107);
lean_dec(x_103);
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
lean_dec(x_104);
x_109 = l_List_forM___at_Lean_Meta_Grind_Preprocessor_loop___spec__1(x_108, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_107);
return x_109;
}
}
else
{
uint8_t x_110; 
lean_dec(x_102);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_110 = !lean_is_exclusive(x_103);
if (x_110 == 0)
{
return x_103;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_103, 0);
x_112 = lean_ctor_get(x_103, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_103);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_11);
if (x_114 == 0)
{
return x_11;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_11, 0);
x_116 = lean_ctor_get(x_11, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_11);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_loop___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Preprocessor_loop___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_preprocess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Meta_Grind_mkGoal(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_3);
x_14 = l_Lean_Meta_Grind_Preprocessor_loop(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_3, x_15);
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at_Lean_Meta_Grind_main___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_List_map___at_Lean_Meta_Grind_main___spec__1(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_List_map___at_Lean_Meta_Grind_main___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_unfoldReducible), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MVarId_betaReduce___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__3;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ShareCommon_objectFactory;
x_2 = l_ShareCommon_mkStateImpl(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_main___closed__3;
x_2 = l_Lean_Meta_Grind_main___closed__4;
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_MVarId_ensureProp(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_1);
x_10 = l_Lean_MVarId_ensureNoMVar(x_1, x_3, x_4, x_5, x_6, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_MVarId_clearAuxDecls(x_1, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l_Lean_MVarId_revertAll(x_13, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_16);
x_18 = l_Lean_MVarId_ensureNoMVar(x_16, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_20 = l_Lean_MVarId_abstractNestedProofs(x_16, x_2, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_Grind_main___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_24 = l_Lean_MVarId_transformTarget(x_21, x_23, x_3, x_4, x_5, x_6, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_Grind_main___closed__2;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_28 = l_Lean_MVarId_transformTarget(x_25, x_27, x_3, x_4, x_5, x_6, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_preprocess), 10, 1);
lean_closure_set(x_31, 0, x_29);
x_32 = l_Lean_Meta_Grind_main___closed__5;
x_33 = lean_st_mk_ref(x_32, x_30);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_34);
x_36 = l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg(x_31, x_2, x_34, x_3, x_4, x_5, x_6, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_st_ref_get(x_34, x_38);
lean_dec(x_34);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_dec(x_37);
x_43 = l_Lean_PersistentArray_toList___rarg(x_42);
lean_dec(x_42);
x_44 = l_List_map___at_Lean_Meta_Grind_main___spec__1(x_43);
lean_ctor_set(x_39, 0, x_44);
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_dec(x_37);
x_47 = l_Lean_PersistentArray_toList___rarg(x_46);
lean_dec(x_46);
x_48 = l_List_map___at_Lean_Meta_Grind_main___spec__1(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_34);
x_50 = !lean_is_exclusive(x_36);
if (x_50 == 0)
{
return x_36;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_36, 0);
x_52 = lean_ctor_get(x_36, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_36);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_28);
if (x_54 == 0)
{
return x_28;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_28, 0);
x_56 = lean_ctor_get(x_28, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_28);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_24);
if (x_58 == 0)
{
return x_24;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_24, 0);
x_60 = lean_ctor_get(x_24, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_24);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_20);
if (x_62 == 0)
{
return x_20;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_20, 0);
x_64 = lean_ctor_get(x_20, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_20);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_18);
if (x_66 == 0)
{
return x_18;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_18, 0);
x_68 = lean_ctor_get(x_18, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_18);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_15);
if (x_70 == 0)
{
return x_15;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_15, 0);
x_72 = lean_ctor_get(x_15, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_15);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_12);
if (x_74 == 0)
{
return x_12;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_12, 0);
x_76 = lean_ctor_get(x_12, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_12);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_10);
if (x_78 == 0)
{
return x_10;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_10, 0);
x_80 = lean_ctor_get(x_10, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_10);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_8);
if (x_82 == 0)
{
return x_8;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_8, 0);
x_84 = lean_ctor_get(x_8, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_8);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Canonicalizer(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_RevertAll(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Injection(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Core(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Preprocessor(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Canonicalizer(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Attr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_RevertAll(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Cases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Injection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Core(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__1 = _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__1);
l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__2 = _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__2);
l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__3 = _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__3);
l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__4 = _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__4);
l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__5 = _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__5);
l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__6 = _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__6);
l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__7 = _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__7);
l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__8 = _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__8);
l_Lean_Meta_Grind_Preprocessor_instInhabitedContext = _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_instInhabitedContext);
l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__1 = _init_l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__1);
l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__2 = _init_l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__2);
l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__3 = _init_l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__3);
l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__4 = _init_l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__4);
l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__5 = _init_l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__5);
l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__6 = _init_l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__6);
l_Lean_Meta_Grind_Preprocessor_State_simpStats___default = _init_l_Lean_Meta_Grind_Preprocessor_State_simpStats___default();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_State_simpStats___default);
l_Lean_Meta_Grind_Preprocessor_State_goals___default = _init_l_Lean_Meta_Grind_Preprocessor_State_goals___default();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_State_goals___default);
l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__1 = _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__1);
l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__2 = _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__2();
l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__3 = _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__3);
l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__4 = _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__4);
l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__5 = _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__5);
l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__6 = _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__6);
l_Lean_Meta_Grind_Preprocessor_instInhabitedState = _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_instInhabitedState);
l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__1 = _init_l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__1);
l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__2 = _init_l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__2);
l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__3 = _init_l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__3);
l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__4 = _init_l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__4);
l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__5 = _init_l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__5();
l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__6 = _init_l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_PreM_run___rarg___closed__6);
l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__1 = _init_l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__1);
l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__2 = _init_l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__2);
l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__3 = _init_l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__3);
l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__4 = _init_l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__4);
l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__5 = _init_l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__5);
l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__6 = _init_l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_introNext___lambda__5___closed__6);
l_Lean_Meta_Grind_main___closed__1 = _init_l_Lean_Meta_Grind_main___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_main___closed__1);
l_Lean_Meta_Grind_main___closed__2 = _init_l_Lean_Meta_Grind_main___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_main___closed__2);
l_Lean_Meta_Grind_main___closed__3 = _init_l_Lean_Meta_Grind_main___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_main___closed__3);
l_Lean_Meta_Grind_main___closed__4 = _init_l_Lean_Meta_Grind_main___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_main___closed__4);
l_Lean_Meta_Grind_main___closed__5 = _init_l_Lean_Meta_Grind_main___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_main___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
