// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Preprocessor
// Imports: Lean.Meta.Canonicalizer Lean.Meta.Tactic.Util Lean.Meta.Tactic.Intro Lean.Meta.Tactic.Simp.Main Lean.Meta.Tactic.Grind.Attr Lean.Meta.Tactic.Grind.RevertAll Lean.Meta.Tactic.Grind.EnsureNoMVar Lean.Meta.Tactic.Grind.Types
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
static lean_object* l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__2;
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__1___closed__1;
static lean_object* l_Lean_Meta_Grind_Preprocessor_main_loop___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_State_canon___default;
static lean_object* l_Lean_Meta_Grind_Preprocessor_State_goals___default___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_mkInitialState(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_State_goals___default;
static uint32_t l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__5;
static lean_object* l_Lean_Meta_Grind_Preprocessor_State_goals___default___closed__2;
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__10;
uint32_t l_UInt32_ofNatTruncate(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_main_loop___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_simpHyp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLet(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_simpHyp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_pushTodo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__5;
static uint32_t l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_Result_goals___default;
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__3;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_revertAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_pushTodo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedResult;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__7;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_Grind_Preprocessor_introNext___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_getNextGoal_x3f___boxed(lean_object*);
static size_t l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__2;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_Grind_Preprocessor_introNext___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__1;
static lean_object* l_Lean_Meta_Grind_Preprocessor_State_canon___default___closed__1;
lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_getNextGoal_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_main_loop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__6;
static lean_object* l_Lean_Meta_Grind_Preprocessor_main_loop___closed__3;
static lean_object* l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__3;
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_M_run(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedResult___closed__1;
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__6;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_pushResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__3;
lean_object* l_Lean_FVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_State_simpStats___default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_Result_canon___default;
static lean_object* l_Lean_Meta_Grind_Preprocessor_mkInitialState___closed__2;
lean_object* l_Lean_Meta_instBEqOrigin___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_main___closed__1;
extern lean_object* l_Lean_Meta_Grind_grindNormSimprocExt;
extern lean_object* l_Lean_inheritedTraceOptions;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedContext;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_State_todo___default;
static lean_object* l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Meta_Grind_Preprocessor_introNext___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_ensureNoMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_main_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_getNextGoal_x3f___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__4;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_grindNormExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_pushResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__5;
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_main_loop___closed__1;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_State_goals___default___closed__3;
lean_object* l_Lean_Meta_Grind_mkInputClause(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instHashableOrigin___boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__9;
extern lean_object* l_Lean_Meta_Simp_defaultMaxSteps;
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__8;
lean_object* l_Lean_Meta_simpLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_main_loop___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_M_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Meta_Grind_Preprocessor_introNext___spec__2(lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedState;
lean_object* l_Lean_Meta_Grind_mkGoal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_getNextGoal_x3f(lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__1;
static lean_object* l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__3;
static lean_object* l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__5;
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
static double l_Lean_addTrace___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__2___closed__1;
static lean_object* l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Preprocessor_mkInitialState___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_main_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 18);
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
return x_4;
}
}
static uint32_t _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__2() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__6;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__8() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__4;
x_3 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__7;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; uint32_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__1;
x_3 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__2;
x_4 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__3;
x_5 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__8;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_5);
lean_ctor_set(x_7, 3, x_1);
lean_ctor_set(x_7, 4, x_6);
lean_ctor_set_uint32(x_7, sizeof(void*)*5, x_3);
lean_ctor_set_uint32(x_7, sizeof(void*)*5 + 4, x_3);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__9;
x_2 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__3;
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
x_1 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__10;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_State_canon___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__4;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_State_canon___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Preprocessor_State_canon___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_State_todo___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_State_goals___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_State_goals___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Preprocessor_State_goals___default___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_State_goals___default___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Meta_Grind_Preprocessor_State_goals___default___closed__2;
x_3 = l_Lean_Meta_Grind_Preprocessor_State_goals___default___closed__1;
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
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_State_goals___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Preprocessor_State_goals___default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instBEqOrigin___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instHashableOrigin___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__6;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__3;
x_2 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__7;
x_3 = l_Lean_Meta_Grind_Preprocessor_State_goals___default___closed__3;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__3;
x_2 = l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__4;
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
x_1 = l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__3;
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
x_2 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__3;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__3;
x_2 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__7;
x_3 = l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__3;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__3;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Preprocessor_State_canon___default___closed__1;
x_3 = l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__3;
x_4 = l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__5;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
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
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_Result_canon___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Preprocessor_State_canon___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_Result_goals___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Preprocessor_State_goals___default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedResult___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Preprocessor_State_canon___default___closed__1;
x_2 = l_Lean_Meta_Grind_Preprocessor_instInhabitedState___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedResult() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Preprocessor_instInhabitedResult___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_mkInitialState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__3;
x_2 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__7;
x_3 = l_Lean_Meta_Grind_Preprocessor_State_goals___default___closed__3;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_mkInitialState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Preprocessor_State_simpStats___default___closed__3;
x_2 = l_Lean_Meta_Grind_Preprocessor_mkInitialState___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_mkInitialState(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_Meta_Grind_mkGoal(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_Lean_Meta_Grind_Preprocessor_State_canon___default___closed__1;
x_6 = l_Lean_Meta_Grind_Preprocessor_State_goals___default___closed__3;
x_7 = l_Lean_Meta_Grind_Preprocessor_mkInitialState___closed__2;
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_6);
lean_ctor_set(x_8, 3, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_grindNormExt;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_grindNormSimprocExt;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Simp_defaultMaxSteps;
x_2 = lean_unsigned_to_nat(2u);
x_3 = 0;
x_4 = 1;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 2, 18);
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
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 10, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 11, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 12, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 13, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 14, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 15, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 16, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 17, x_4);
return x_6;
}
}
static uint32_t _init_l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__5() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_UInt32_ofNatTruncate(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_M_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_8 = l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__1;
x_9 = l_Lean_Meta_SimpExtension_getTheorems(x_8, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__2;
x_13 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs(x_12, x_5, x_6, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__3;
x_17 = lean_array_push(x_16, x_14);
x_18 = l_Lean_Meta_getSimpCongrTheorems___rarg(x_6, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint32_t x_24; lean_object* x_25; uint32_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_array_push(x_16, x_10);
x_23 = lean_box(0);
x_24 = 0;
x_25 = l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__4;
x_26 = l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__5;
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_22);
lean_ctor_set(x_28, 2, x_20);
lean_ctor_set(x_28, 3, x_23);
lean_ctor_set(x_28, 4, x_27);
lean_ctor_set_uint32(x_28, sizeof(void*)*5, x_26);
lean_ctor_set_uint32(x_28, sizeof(void*)*5 + 4, x_24);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 0, x_28);
x_29 = l_Lean_Meta_Grind_Preprocessor_mkInitialState(x_2);
x_30 = lean_st_mk_ref(x_29, x_21);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_31);
x_33 = lean_apply_7(x_1, x_18, x_31, x_3, x_4, x_5, x_6, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_st_ref_get(x_31, x_35);
lean_dec(x_31);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_34);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_31);
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
return x_33;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_33, 0);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_33);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint32_t x_49; lean_object* x_50; uint32_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_45 = lean_ctor_get(x_18, 0);
x_46 = lean_ctor_get(x_18, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_18);
x_47 = lean_array_push(x_16, x_10);
x_48 = lean_box(0);
x_49 = 0;
x_50 = l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__4;
x_51 = l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__5;
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_alloc_ctor(0, 5, 8);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_47);
lean_ctor_set(x_53, 2, x_45);
lean_ctor_set(x_53, 3, x_48);
lean_ctor_set(x_53, 4, x_52);
lean_ctor_set_uint32(x_53, sizeof(void*)*5, x_51);
lean_ctor_set_uint32(x_53, sizeof(void*)*5 + 4, x_49);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_17);
x_55 = l_Lean_Meta_Grind_Preprocessor_mkInitialState(x_2);
x_56 = lean_st_mk_ref(x_55, x_46);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_57);
x_59 = lean_apply_7(x_1, x_54, x_57, x_3, x_4, x_5, x_6, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_st_ref_get(x_57, x_61);
lean_dec(x_57);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_57);
x_66 = lean_ctor_get(x_59, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_59, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_68 = x_59;
} else {
 lean_dec_ref(x_59);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_M_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_M_run___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_simpHyp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 3);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_box(0);
x_17 = 1;
x_18 = l_Lean_Meta_simpLocalDecl(x_1, x_2, x_14, x_15, x_16, x_17, x_13, x_5, x_6, x_7, x_8, x_12);
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
x_23 = lean_st_ref_take(x_4, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_24, 3);
lean_dec(x_27);
lean_ctor_set(x_24, 3, x_22);
x_28 = lean_st_ref_set(x_4, x_24, x_25);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
x_35 = lean_ctor_get(x_24, 2);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_22);
x_37 = lean_st_ref_set(x_4, x_36, x_25);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_21);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_18);
if (x_41 == 0)
{
return x_18;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_18, 0);
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_18);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_simpHyp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_Preprocessor_simpHyp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_getNextGoal_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_st_ref_get(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_st_ref_take(x_1, x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_20, 1);
lean_dec(x_23);
lean_ctor_set(x_20, 1, x_18);
x_24 = lean_st_ref_set(x_1, x_20, x_21);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_17);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 2);
x_33 = lean_ctor_get(x_20, 3);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_18);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_33);
x_35 = lean_st_ref_set(x_1, x_34, x_21);
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
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_17);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_getNextGoal_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_getNextGoal_x3f___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_getNextGoal_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_Preprocessor_getNextGoal_x3f___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_getNextGoal_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Preprocessor_getNextGoal_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_Grind_Preprocessor_introNext___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_apply_8(x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_Grind_Preprocessor_introNext___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_Preprocessor_introNext___spec__1___rarg), 9, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Meta_Grind_Preprocessor_introNext___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_2(x_2, x_3, x_4);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Meta_Grind_Preprocessor_introNext___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at_Lean_Meta_Grind_Preprocessor_introNext___spec__2___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_FVarId_getType(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l_Lean_Meta_isProp(x_4, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
x_21 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_dec(x_12);
x_24 = l_Lean_Meta_Grind_Preprocessor_simpHyp_x3f(x_1, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_box(1);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_box(1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_24, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_ctor_set(x_32, 1, x_2);
lean_ctor_set(x_32, 0, x_37);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_32);
lean_ctor_set(x_24, 0, x_38);
return x_24;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_32, 0);
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_32);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_2);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_24, 0, x_42);
return x_24;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = lean_ctor_get(x_24, 1);
lean_inc(x_43);
lean_dec(x_24);
x_44 = lean_ctor_get(x_32, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_32, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_46 = x_32;
} else {
 lean_dec_ref(x_32);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_2);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_24);
if (x_50 == 0)
{
return x_24;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_24, 0);
x_52 = lean_ctor_get(x_24, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_24);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_12);
if (x_54 == 0)
{
return x_12;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_12, 0);
x_56 = lean_ctor_get(x_12, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_12);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_12 = l_Lean_MVarId_getType(x_10, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_Expr_isArrow(x_14);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = l_Lean_Expr_isLet(x_14);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l_Lean_Expr_isForall(x_14);
lean_dec(x_14);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = lean_box(0);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
uint8_t x_20; lean_object* x_21; 
lean_free_object(x_12);
x_20 = 1;
x_21 = l_Lean_Meta_intro1Core(x_10, x_20, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 1);
lean_ctor_set(x_1, 0, x_25);
lean_ctor_set_tag(x_23, 3);
lean_ctor_set(x_23, 1, x_1);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_1, 0, x_27);
x_28 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_1);
lean_ctor_set(x_21, 0, x_28);
return x_21;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_33 = x_29;
} else {
 lean_dec_ref(x_29);
 x_33 = lean_box(0);
}
lean_ctor_set(x_1, 0, x_32);
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(3, 2, 0);
} else {
 x_34 = x_33;
 lean_ctor_set_tag(x_34, 3);
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_1);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_free_object(x_1);
lean_dec(x_11);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_21);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
uint8_t x_40; lean_object* x_41; 
lean_free_object(x_12);
lean_dec(x_14);
x_40 = 1;
x_41 = l_Lean_Meta_intro1Core(x_10, x_40, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 1);
lean_ctor_set(x_1, 0, x_45);
lean_ctor_set_tag(x_43, 3);
lean_ctor_set(x_43, 1, x_1);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_43, 0);
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_43);
lean_ctor_set(x_1, 0, x_47);
x_48 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_1);
lean_ctor_set(x_41, 0, x_48);
return x_41;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_41, 0);
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_41);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_53 = x_49;
} else {
 lean_dec_ref(x_49);
 x_53 = lean_box(0);
}
lean_ctor_set(x_1, 0, x_52);
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(3, 2, 0);
} else {
 x_54 = x_53;
 lean_ctor_set_tag(x_54, 3);
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_1);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_free_object(x_1);
lean_dec(x_11);
x_56 = !lean_is_exclusive(x_41);
if (x_56 == 0)
{
return x_41;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_41, 0);
x_58 = lean_ctor_get(x_41, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_41);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
else
{
uint8_t x_60; lean_object* x_61; 
lean_free_object(x_12);
lean_dec(x_14);
lean_free_object(x_1);
x_60 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_61 = l_Lean_Meta_intro1Core(x_10, x_60, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
lean_inc(x_64);
x_66 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_introNext___lambda__1___boxed), 8, 1);
lean_closure_set(x_66, 0, x_64);
lean_inc(x_65);
x_67 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_introNext___lambda__2___boxed), 11, 3);
lean_closure_set(x_67, 0, x_65);
lean_closure_set(x_67, 1, x_11);
lean_closure_set(x_67, 2, x_64);
x_68 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_Preprocessor_introNext___spec__1___rarg), 9, 2);
lean_closure_set(x_68, 0, x_66);
lean_closure_set(x_68, 1, x_67);
x_69 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_Preprocessor_introNext___spec__2___rarg(x_65, x_68, x_2, x_3, x_4, x_5, x_6, x_7, x_63);
return x_69;
}
else
{
uint8_t x_70; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_61);
if (x_70 == 0)
{
return x_61;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_61, 0);
x_72 = lean_ctor_get(x_61, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_61);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_12, 0);
x_75 = lean_ctor_get(x_12, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_12);
x_76 = l_Lean_Expr_isArrow(x_74);
if (x_76 == 0)
{
uint8_t x_77; 
lean_dec(x_3);
lean_dec(x_2);
x_77 = l_Lean_Expr_isLet(x_74);
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = l_Lean_Expr_isForall(x_74);
lean_dec(x_74);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_75);
return x_80;
}
else
{
uint8_t x_81; lean_object* x_82; 
x_81 = 1;
x_82 = l_Lean_Meta_intro1Core(x_10, x_81, x_4, x_5, x_6, x_7, x_75);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_83, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_88 = x_83;
} else {
 lean_dec_ref(x_83);
 x_88 = lean_box(0);
}
lean_ctor_set(x_1, 0, x_87);
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(3, 2, 0);
} else {
 x_89 = x_88;
 lean_ctor_set_tag(x_89, 3);
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_1);
if (lean_is_scalar(x_85)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_85;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_84);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_free_object(x_1);
lean_dec(x_11);
x_91 = lean_ctor_get(x_82, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_82, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_93 = x_82;
} else {
 lean_dec_ref(x_82);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
else
{
uint8_t x_95; lean_object* x_96; 
lean_dec(x_74);
x_95 = 1;
x_96 = l_Lean_Meta_intro1Core(x_10, x_95, x_4, x_5, x_6, x_7, x_75);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_99 = x_96;
} else {
 lean_dec_ref(x_96);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_97, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_97, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_102 = x_97;
} else {
 lean_dec_ref(x_97);
 x_102 = lean_box(0);
}
lean_ctor_set(x_1, 0, x_101);
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(3, 2, 0);
} else {
 x_103 = x_102;
 lean_ctor_set_tag(x_103, 3);
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_1);
if (lean_is_scalar(x_99)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_99;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_98);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_free_object(x_1);
lean_dec(x_11);
x_105 = lean_ctor_get(x_96, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_96, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_107 = x_96;
} else {
 lean_dec_ref(x_96);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
else
{
uint8_t x_109; lean_object* x_110; 
lean_dec(x_74);
lean_free_object(x_1);
x_109 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_110 = l_Lean_Meta_intro1Core(x_10, x_109, x_4, x_5, x_6, x_7, x_75);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_dec(x_111);
lean_inc(x_113);
x_115 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_introNext___lambda__1___boxed), 8, 1);
lean_closure_set(x_115, 0, x_113);
lean_inc(x_114);
x_116 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_introNext___lambda__2___boxed), 11, 3);
lean_closure_set(x_116, 0, x_114);
lean_closure_set(x_116, 1, x_11);
lean_closure_set(x_116, 2, x_113);
x_117 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_Preprocessor_introNext___spec__1___rarg), 9, 2);
lean_closure_set(x_117, 0, x_115);
lean_closure_set(x_117, 1, x_116);
x_118 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_Preprocessor_introNext___spec__2___rarg(x_114, x_117, x_2, x_3, x_4, x_5, x_6, x_7, x_112);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_119 = lean_ctor_get(x_110, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_110, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_121 = x_110;
} else {
 lean_dec_ref(x_110);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_12);
if (x_123 == 0)
{
return x_12;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_12, 0);
x_125 = lean_ctor_get(x_12, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_12);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_1, 0);
x_128 = lean_ctor_get(x_1, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_1);
lean_inc(x_127);
x_129 = l_Lean_MVarId_getType(x_127, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_132 = x_129;
} else {
 lean_dec_ref(x_129);
 x_132 = lean_box(0);
}
x_133 = l_Lean_Expr_isArrow(x_130);
if (x_133 == 0)
{
uint8_t x_134; 
lean_dec(x_3);
lean_dec(x_2);
x_134 = l_Lean_Expr_isLet(x_130);
if (x_134 == 0)
{
uint8_t x_135; 
x_135 = l_Lean_Expr_isForall(x_130);
lean_dec(x_130);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_136 = lean_box(0);
if (lean_is_scalar(x_132)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_132;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_131);
return x_137;
}
else
{
uint8_t x_138; lean_object* x_139; 
lean_dec(x_132);
x_138 = 1;
x_139 = l_Lean_Meta_intro1Core(x_127, x_138, x_4, x_5, x_6, x_7, x_131);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_142 = x_139;
} else {
 lean_dec_ref(x_139);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_140, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_140, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_145 = x_140;
} else {
 lean_dec_ref(x_140);
 x_145 = lean_box(0);
}
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_128);
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(3, 2, 0);
} else {
 x_147 = x_145;
 lean_ctor_set_tag(x_147, 3);
}
lean_ctor_set(x_147, 0, x_143);
lean_ctor_set(x_147, 1, x_146);
if (lean_is_scalar(x_142)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_142;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_141);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_128);
x_149 = lean_ctor_get(x_139, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_139, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_151 = x_139;
} else {
 lean_dec_ref(x_139);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
}
else
{
uint8_t x_153; lean_object* x_154; 
lean_dec(x_132);
lean_dec(x_130);
x_153 = 1;
x_154 = l_Lean_Meta_intro1Core(x_127, x_153, x_4, x_5, x_6, x_7, x_131);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_157 = x_154;
} else {
 lean_dec_ref(x_154);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_155, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_155, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_160 = x_155;
} else {
 lean_dec_ref(x_155);
 x_160 = lean_box(0);
}
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_128);
if (lean_is_scalar(x_160)) {
 x_162 = lean_alloc_ctor(3, 2, 0);
} else {
 x_162 = x_160;
 lean_ctor_set_tag(x_162, 3);
}
lean_ctor_set(x_162, 0, x_158);
lean_ctor_set(x_162, 1, x_161);
if (lean_is_scalar(x_157)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_157;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_156);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_128);
x_164 = lean_ctor_get(x_154, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_154, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_166 = x_154;
} else {
 lean_dec_ref(x_154);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
}
else
{
uint8_t x_168; lean_object* x_169; 
lean_dec(x_132);
lean_dec(x_130);
x_168 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_169 = l_Lean_Meta_intro1Core(x_127, x_168, x_4, x_5, x_6, x_7, x_131);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
lean_dec(x_170);
lean_inc(x_172);
x_174 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_introNext___lambda__1___boxed), 8, 1);
lean_closure_set(x_174, 0, x_172);
lean_inc(x_173);
x_175 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_introNext___lambda__2___boxed), 11, 3);
lean_closure_set(x_175, 0, x_173);
lean_closure_set(x_175, 1, x_128);
lean_closure_set(x_175, 2, x_172);
x_176 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_Preprocessor_introNext___spec__1___rarg), 9, 2);
lean_closure_set(x_176, 0, x_174);
lean_closure_set(x_176, 1, x_175);
x_177 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_Preprocessor_introNext___spec__2___rarg(x_173, x_176, x_2, x_3, x_4, x_5, x_6, x_7, x_171);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_128);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_178 = lean_ctor_get(x_169, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_169, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_180 = x_169;
} else {
 lean_dec_ref(x_169);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_182 = lean_ctor_get(x_129, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_129, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_184 = x_129;
} else {
 lean_dec_ref(x_129);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_Preprocessor_introNext___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_introNext___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Preprocessor_introNext___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_pushTodo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_ctor_get(x_11, 1);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 1, x_14);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_11, 1, x_9);
x_15 = lean_st_ref_set(x_3, x_11, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_9, 1);
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 2);
x_26 = lean_ctor_get(x_11, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 1, x_24);
lean_ctor_set(x_9, 0, x_1);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_9);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_26);
x_28 = lean_st_ref_set(x_3, x_27, x_22);
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
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_33 = lean_ctor_get(x_9, 0);
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_9);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_33, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_33, 3);
lean_inc(x_38);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 lean_ctor_release(x_33, 3);
 x_39 = x_33;
} else {
 lean_dec_ref(x_33);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_36);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 4, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_37);
lean_ctor_set(x_41, 3, x_38);
x_42 = lean_st_ref_set(x_3, x_41, x_34);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
x_45 = lean_box(0);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_pushTodo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_Preprocessor_pushTodo(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_pushResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 2);
x_14 = l_Lean_PersistentArray_push___rarg(x_13, x_1);
lean_ctor_set(x_10, 2, x_14);
x_15 = lean_st_ref_set(x_3, x_10, x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 2);
x_25 = lean_ctor_get(x_10, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_26 = l_Lean_PersistentArray_push___rarg(x_24, x_1);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set(x_27, 3, x_25);
x_28 = lean_st_ref_set(x_3, x_27, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_pushResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_Preprocessor_pushResult(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__1___closed__1;
x_10 = lean_st_ref_get(x_9, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_6, 2);
x_14 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_12, x_13, x_1);
lean_dec(x_12);
x_15 = lean_box(x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_ctor_get(x_6, 2);
x_19 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_16, x_18, x_1);
lean_dec(x_16);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
}
static double _init_l_Lean_addTrace___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__2___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = l_Float_ofScientific(x_1, x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_8, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; double x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_18 = lean_ctor_get(x_14, 1);
x_19 = lean_ctor_get(x_16, 3);
x_20 = l_Lean_addTrace___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__2___closed__1;
x_21 = 0;
x_22 = l_Lean_addTrace___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__2___closed__2;
x_23 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set_float(x_23, sizeof(void*)*2, x_20);
lean_ctor_set_float(x_23, sizeof(void*)*2 + 8, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*2 + 16, x_21);
x_24 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__3;
x_25 = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_12);
lean_ctor_set(x_25, 2, x_24);
lean_inc(x_10);
lean_ctor_set(x_14, 1, x_25);
lean_ctor_set(x_14, 0, x_10);
x_26 = l_Lean_PersistentArray_push___rarg(x_19, x_14);
lean_ctor_set(x_16, 3, x_26);
x_27 = lean_st_ref_set(x_8, x_16, x_18);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; double x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_34 = lean_ctor_get(x_14, 1);
x_35 = lean_ctor_get(x_16, 0);
x_36 = lean_ctor_get(x_16, 1);
x_37 = lean_ctor_get(x_16, 2);
x_38 = lean_ctor_get(x_16, 3);
x_39 = lean_ctor_get(x_16, 4);
x_40 = lean_ctor_get(x_16, 5);
x_41 = lean_ctor_get(x_16, 6);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_16);
x_42 = l_Lean_addTrace___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__2___closed__1;
x_43 = 0;
x_44 = l_Lean_addTrace___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__2___closed__2;
x_45 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set_float(x_45, sizeof(void*)*2, x_42);
lean_ctor_set_float(x_45, sizeof(void*)*2 + 8, x_42);
lean_ctor_set_uint8(x_45, sizeof(void*)*2 + 16, x_43);
x_46 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__3;
x_47 = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_12);
lean_ctor_set(x_47, 2, x_46);
lean_inc(x_10);
lean_ctor_set(x_14, 1, x_47);
lean_ctor_set(x_14, 0, x_10);
x_48 = l_Lean_PersistentArray_push___rarg(x_38, x_14);
x_49 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_49, 0, x_35);
lean_ctor_set(x_49, 1, x_36);
lean_ctor_set(x_49, 2, x_37);
lean_ctor_set(x_49, 3, x_48);
lean_ctor_set(x_49, 4, x_39);
lean_ctor_set(x_49, 5, x_40);
lean_ctor_set(x_49, 6, x_41);
x_50 = lean_st_ref_set(x_8, x_49, x_34);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
x_53 = lean_box(0);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; double x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_55 = lean_ctor_get(x_14, 0);
x_56 = lean_ctor_get(x_14, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_14);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_55, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_55, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 4);
lean_inc(x_61);
x_62 = lean_ctor_get(x_55, 5);
lean_inc(x_62);
x_63 = lean_ctor_get(x_55, 6);
lean_inc(x_63);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 lean_ctor_release(x_55, 4);
 lean_ctor_release(x_55, 5);
 lean_ctor_release(x_55, 6);
 x_64 = x_55;
} else {
 lean_dec_ref(x_55);
 x_64 = lean_box(0);
}
x_65 = l_Lean_addTrace___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__2___closed__1;
x_66 = 0;
x_67 = l_Lean_addTrace___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__2___closed__2;
x_68 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_68, 0, x_1);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set_float(x_68, sizeof(void*)*2, x_65);
lean_ctor_set_float(x_68, sizeof(void*)*2 + 8, x_65);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 16, x_66);
x_69 = l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__3;
x_70 = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_12);
lean_ctor_set(x_70, 2, x_69);
lean_inc(x_10);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_10);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_PersistentArray_push___rarg(x_60, x_71);
if (lean_is_scalar(x_64)) {
 x_73 = lean_alloc_ctor(0, 7, 0);
} else {
 x_73 = x_64;
}
lean_ctor_set(x_73, 0, x_57);
lean_ctor_set(x_73, 1, x_58);
lean_ctor_set(x_73, 2, x_59);
lean_ctor_set(x_73, 3, x_72);
lean_ctor_set(x_73, 4, x_61);
lean_ctor_set(x_73, 5, x_62);
lean_ctor_set(x_73, 6, x_63);
x_74 = lean_st_ref_set(x_8, x_73, x_56);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
x_77 = lean_box(0);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_main_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_mkInputClause(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_main_loop___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l_Lean_Meta_Grind_Preprocessor_introNext(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_Grind_Preprocessor_pushResult(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
case 1:
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = l_Lean_Meta_Grind_Preprocessor_main_loop(x_3, x_4, x_5, x_6, x_7, x_8, x_20);
return x_21;
}
case 2:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_1);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
lean_dec(x_11);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_main_loop___lambda__1___boxed), 8, 1);
lean_closure_set(x_28, 0, x_24);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_26);
x_29 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_Preprocessor_introNext___spec__2___rarg(x_26, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_PersistentArray_push___rarg(x_27, x_30);
lean_ctor_set(x_22, 1, x_32);
x_33 = l_Lean_Meta_Grind_Preprocessor_pushTodo(x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_31);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_Meta_Grind_Preprocessor_main_loop(x_3, x_4, x_5, x_6, x_7, x_8, x_34);
return x_35;
}
else
{
uint8_t x_36; 
lean_free_object(x_22);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
return x_29;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_29, 0);
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_29);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_22, 0);
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_22);
x_42 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_main_loop___lambda__1___boxed), 8, 1);
lean_closure_set(x_42, 0, x_24);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_40);
x_43 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_Preprocessor_introNext___spec__2___rarg(x_40, x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_PersistentArray_push___rarg(x_41, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Meta_Grind_Preprocessor_pushTodo(x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_45);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_Meta_Grind_Preprocessor_main_loop(x_3, x_4, x_5, x_6, x_7, x_8, x_49);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_51 = lean_ctor_get(x_43, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_53 = x_43;
} else {
 lean_dec_ref(x_43);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
default: 
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_1);
x_55 = lean_ctor_get(x_10, 1);
lean_inc(x_55);
lean_dec(x_10);
x_56 = lean_ctor_get(x_11, 1);
lean_inc(x_56);
lean_dec(x_11);
x_57 = l_Lean_Meta_Grind_Preprocessor_pushTodo(x_56, x_3, x_4, x_5, x_6, x_7, x_8, x_55);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Lean_Meta_Grind_Preprocessor_main_loop(x_3, x_4, x_5, x_6, x_7, x_8, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_10);
if (x_60 == 0)
{
return x_10;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_10, 0);
x_62 = lean_ctor_get(x_10, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_10);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_main_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_main_loop___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("debug", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_main_loop___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Preprocessor_main_loop___closed__1;
x_2 = l_Lean_Meta_Grind_Preprocessor_main_loop___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_main_loop___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_main_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Meta_Grind_Preprocessor_getNextGoal_x3f___rarg(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = l_Lean_Meta_Grind_Preprocessor_main_loop___closed__3;
x_20 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__1(x_19, x_1, x_2, x_3, x_4, x_5, x_6, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_9);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = l_Lean_Meta_Grind_Preprocessor_main_loop___lambda__2(x_18, x_24, x_1, x_2, x_3, x_4, x_5, x_6, x_23);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_20, 1);
x_28 = lean_ctor_get(x_20, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_18, 0);
lean_inc(x_29);
lean_ctor_set(x_9, 0, x_29);
x_30 = l_Lean_Meta_Grind_Preprocessor_main_loop___closed__4;
lean_ctor_set_tag(x_20, 6);
lean_ctor_set(x_20, 1, x_9);
lean_ctor_set(x_20, 0, x_30);
x_31 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_31, 0, x_20);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_addTrace___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__2(x_19, x_31, x_1, x_2, x_3, x_4, x_5, x_6, x_27);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Meta_Grind_Preprocessor_main_loop___lambda__2(x_18, x_33, x_1, x_2, x_3, x_4, x_5, x_6, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_dec(x_20);
x_37 = lean_ctor_get(x_18, 0);
lean_inc(x_37);
lean_ctor_set(x_9, 0, x_37);
x_38 = l_Lean_Meta_Grind_Preprocessor_main_loop___closed__4;
x_39 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_9);
x_40 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Lean_addTrace___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__2(x_19, x_40, x_1, x_2, x_3, x_4, x_5, x_6, x_36);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Meta_Grind_Preprocessor_main_loop___lambda__2(x_18, x_42, x_1, x_2, x_3, x_4, x_5, x_6, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_9, 0);
lean_inc(x_45);
lean_dec(x_9);
x_46 = l_Lean_Meta_Grind_Preprocessor_main_loop___closed__3;
x_47 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__1(x_46, x_1, x_2, x_3, x_4, x_5, x_6, x_16);
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
x_52 = l_Lean_Meta_Grind_Preprocessor_main_loop___lambda__2(x_45, x_51, x_1, x_2, x_3, x_4, x_5, x_6, x_50);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_54 = x_47;
} else {
 lean_dec_ref(x_47);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_45, 0);
lean_inc(x_55);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = l_Lean_Meta_Grind_Preprocessor_main_loop___closed__4;
if (lean_is_scalar(x_54)) {
 x_58 = lean_alloc_ctor(6, 2, 0);
} else {
 x_58 = x_54;
 lean_ctor_set_tag(x_58, 6);
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_Lean_addTrace___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__2(x_46, x_59, x_1, x_2, x_3, x_4, x_5, x_6, x_53);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Meta_Grind_Preprocessor_main_loop___lambda__2(x_45, x_61, x_1, x_2, x_3, x_4, x_5, x_6, x_62);
return x_63;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_main_loop___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_Preprocessor_main_loop___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_2);
x_8 = l_Lean_Meta_Grind_Preprocessor_main_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_2, x_9);
lean_dec(x_2);
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
else
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Preprocessor_main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Preprocessor_main___lambda__1), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Preprocessor_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_MVarId_ensureNoMVar(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_MVarId_revertAll(x_1, x_2, x_3, x_4, x_5, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_10);
x_12 = l_Lean_MVarId_ensureNoMVar(x_10, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Meta_Grind_Preprocessor_main___closed__1;
x_15 = l_Lean_Meta_Grind_Preprocessor_M_run___rarg(x_14, x_10, x_2, x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 2);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 2);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
uint8_t x_35; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_9);
if (x_35 == 0)
{
return x_9;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_9, 0);
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_9);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_7);
if (x_39 == 0)
{
return x_7;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_7, 0);
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_7);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
lean_object* initialize_Lean_Meta_Canonicalizer(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_RevertAll(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_EnsureNoMVar(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Preprocessor(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
res = initialize_Lean_Meta_Tactic_Grind_EnsureNoMVar(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__1 = _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__1);
l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__2 = _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__2();
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
l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__9 = _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__9);
l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__10 = _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_instInhabitedContext___closed__10);
l_Lean_Meta_Grind_Preprocessor_instInhabitedContext = _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedContext();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_instInhabitedContext);
l_Lean_Meta_Grind_Preprocessor_State_canon___default___closed__1 = _init_l_Lean_Meta_Grind_Preprocessor_State_canon___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_State_canon___default___closed__1);
l_Lean_Meta_Grind_Preprocessor_State_canon___default = _init_l_Lean_Meta_Grind_Preprocessor_State_canon___default();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_State_canon___default);
l_Lean_Meta_Grind_Preprocessor_State_todo___default = _init_l_Lean_Meta_Grind_Preprocessor_State_todo___default();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_State_todo___default);
l_Lean_Meta_Grind_Preprocessor_State_goals___default___closed__1 = _init_l_Lean_Meta_Grind_Preprocessor_State_goals___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_State_goals___default___closed__1);
l_Lean_Meta_Grind_Preprocessor_State_goals___default___closed__2 = _init_l_Lean_Meta_Grind_Preprocessor_State_goals___default___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_State_goals___default___closed__2);
l_Lean_Meta_Grind_Preprocessor_State_goals___default___closed__3 = _init_l_Lean_Meta_Grind_Preprocessor_State_goals___default___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_State_goals___default___closed__3);
l_Lean_Meta_Grind_Preprocessor_State_goals___default = _init_l_Lean_Meta_Grind_Preprocessor_State_goals___default();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_State_goals___default);
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
l_Lean_Meta_Grind_Preprocessor_State_simpStats___default = _init_l_Lean_Meta_Grind_Preprocessor_State_simpStats___default();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_State_simpStats___default);
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
l_Lean_Meta_Grind_Preprocessor_Result_canon___default = _init_l_Lean_Meta_Grind_Preprocessor_Result_canon___default();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_Result_canon___default);
l_Lean_Meta_Grind_Preprocessor_Result_goals___default = _init_l_Lean_Meta_Grind_Preprocessor_Result_goals___default();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_Result_goals___default);
l_Lean_Meta_Grind_Preprocessor_instInhabitedResult___closed__1 = _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedResult___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_instInhabitedResult___closed__1);
l_Lean_Meta_Grind_Preprocessor_instInhabitedResult = _init_l_Lean_Meta_Grind_Preprocessor_instInhabitedResult();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_instInhabitedResult);
l_Lean_Meta_Grind_Preprocessor_mkInitialState___closed__1 = _init_l_Lean_Meta_Grind_Preprocessor_mkInitialState___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_mkInitialState___closed__1);
l_Lean_Meta_Grind_Preprocessor_mkInitialState___closed__2 = _init_l_Lean_Meta_Grind_Preprocessor_mkInitialState___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_mkInitialState___closed__2);
l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__1 = _init_l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__1);
l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__2 = _init_l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__2);
l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__3 = _init_l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__3);
l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__4 = _init_l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__4);
l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__5 = _init_l_Lean_Meta_Grind_Preprocessor_M_run___rarg___closed__5();
l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__1___closed__1 = _init_l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__1___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__1___closed__1);
l_Lean_addTrace___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__2___closed__1 = _init_l_Lean_addTrace___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__2___closed__1();
l_Lean_addTrace___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__2___closed__2 = _init_l_Lean_addTrace___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__2___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Meta_Grind_Preprocessor_main_loop___spec__2___closed__2);
l_Lean_Meta_Grind_Preprocessor_main_loop___closed__1 = _init_l_Lean_Meta_Grind_Preprocessor_main_loop___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_main_loop___closed__1);
l_Lean_Meta_Grind_Preprocessor_main_loop___closed__2 = _init_l_Lean_Meta_Grind_Preprocessor_main_loop___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_main_loop___closed__2);
l_Lean_Meta_Grind_Preprocessor_main_loop___closed__3 = _init_l_Lean_Meta_Grind_Preprocessor_main_loop___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_main_loop___closed__3);
l_Lean_Meta_Grind_Preprocessor_main_loop___closed__4 = _init_l_Lean_Meta_Grind_Preprocessor_main_loop___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_main_loop___closed__4);
l_Lean_Meta_Grind_Preprocessor_main___closed__1 = _init_l_Lean_Meta_Grind_Preprocessor_main___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Preprocessor_main___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
