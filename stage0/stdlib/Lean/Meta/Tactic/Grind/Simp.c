// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Simp
// Imports: Init.Grind.Lemmas Lean.Meta.Tactic.Simp.Main Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Assert Lean.Meta.Tactic.Grind.Util Lean.Meta.Tactic.Grind.MatchDiscrOnly Lean.Meta.Tactic.Grind.MarkNestedSubsingletons
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
lean_object* l_Lean_Meta_Grind_replacePreMatchCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__6;
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_preprocess_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__2;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__4;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__9;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_preprocess_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mainCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__12;
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__7;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_Meta_Grind_simpCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__1;
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__1;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__6;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_preprocess___closed__2;
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_dsimpMainCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_dsimpCore___closed__0;
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__10;
double lean_float_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_preprocess___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__5;
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_Meta_Grind_simpCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_abstractNestedProofs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_preprocess_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__11;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__0;
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__5;
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__13;
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__3;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__8;
static lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markNestedSubsingletons(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__4;
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__2;
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__2;
lean_object* l_Lean_Meta_Simp_Result_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_shareCommon___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpCore___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_Meta_Grind_simpCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_preprocess_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpCore___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_normalizeLevels(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_foldProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__0;
static lean_object* l_Lean_Meta_Grind_preprocess___closed__1;
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_Meta_Grind_simpCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_preprocess___closed__3;
static lean_object* l_Lean_Meta_Grind_preprocess___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_Meta_Grind_simpCore_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_apply_7(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_14 = l_Lean_profileitIOUnsafe___redArg(x_1, x_2, x_13, x_4, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_Meta_Grind_simpCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_profileitM___at___Lean_Meta_Grind_simpCore_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Meta_Grind_simpCore___lam__0___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpCore___lam__0___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpCore___lam__0___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_simpCore___lam__0___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpCore___lam__0___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpCore___lam__0___closed__6;
x_2 = l_Lean_Meta_Grind_simpCore___lam__0___closed__4;
x_3 = 1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_Grind_simpCore___lam__0___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpCore___lam__0___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__11() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_simpCore___lam__0___closed__9;
x_4 = l_Lean_Meta_Grind_simpCore___lam__0___closed__10;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_simpCore___lam__0___closed__11;
x_2 = l_Lean_Meta_Grind_simpCore___lam__0___closed__6;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_simpCore___lam__0___closed__12;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_simpCore___lam__0___closed__8;
x_4 = l_Lean_Meta_Grind_simpCore___lam__0___closed__4;
x_5 = l_Lean_Meta_Grind_simpCore___lam__0___closed__7;
x_6 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_3);
lean_ctor_set(x_6, 4, x_2);
lean_ctor_set(x_6, 5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_11, 2);
x_15 = l_Lean_Meta_Grind_simpCore___lam__0___closed__13;
lean_ctor_set(x_11, 2, x_15);
x_16 = lean_st_ref_set(x_4, x_11, x_12);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_19);
lean_dec_ref(x_3);
x_20 = l_Lean_Meta_Simp_mainCore(x_1, x_18, x_14, x_19, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_st_ref_take(x_4, x_22);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_26, 2);
lean_dec(x_29);
lean_ctor_set(x_26, 2, x_24);
x_30 = lean_st_ref_set(x_4, x_26, x_27);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_ctor_get(x_26, 1);
x_37 = lean_ctor_get(x_26, 3);
x_38 = lean_ctor_get(x_26, 4);
x_39 = lean_ctor_get(x_26, 5);
x_40 = lean_ctor_get(x_26, 6);
x_41 = lean_ctor_get(x_26, 7);
x_42 = lean_ctor_get(x_26, 8);
x_43 = lean_ctor_get(x_26, 9);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_26);
x_44 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 2, x_24);
lean_ctor_set(x_44, 3, x_37);
lean_ctor_set(x_44, 4, x_38);
lean_ctor_set(x_44, 5, x_39);
lean_ctor_set(x_44, 6, x_40);
lean_ctor_set(x_44, 7, x_41);
lean_ctor_set(x_44, 8, x_42);
lean_ctor_set(x_44, 9, x_43);
x_45 = lean_st_ref_set(x_4, x_44, x_27);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_23);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_20);
if (x_49 == 0)
{
return x_20;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_20, 0);
x_51 = lean_ctor_get(x_20, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_20);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_53 = lean_ctor_get(x_11, 0);
x_54 = lean_ctor_get(x_11, 1);
x_55 = lean_ctor_get(x_11, 2);
x_56 = lean_ctor_get(x_11, 3);
x_57 = lean_ctor_get(x_11, 4);
x_58 = lean_ctor_get(x_11, 5);
x_59 = lean_ctor_get(x_11, 6);
x_60 = lean_ctor_get(x_11, 7);
x_61 = lean_ctor_get(x_11, 8);
x_62 = lean_ctor_get(x_11, 9);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_11);
x_63 = l_Lean_Meta_Grind_simpCore___lam__0___closed__13;
x_64 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_64, 0, x_53);
lean_ctor_set(x_64, 1, x_54);
lean_ctor_set(x_64, 2, x_63);
lean_ctor_set(x_64, 3, x_56);
lean_ctor_set(x_64, 4, x_57);
lean_ctor_set(x_64, 5, x_58);
lean_ctor_set(x_64, 6, x_59);
lean_ctor_set(x_64, 7, x_60);
lean_ctor_set(x_64, 8, x_61);
lean_ctor_set(x_64, 9, x_62);
x_65 = lean_st_ref_set(x_4, x_64, x_12);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec_ref(x_65);
x_67 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_68);
lean_dec_ref(x_3);
x_69 = l_Lean_Meta_Simp_mainCore(x_1, x_67, x_55, x_68, x_5, x_6, x_7, x_8, x_66);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_st_ref_take(x_4, x_71);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec_ref(x_74);
x_77 = lean_ctor_get(x_75, 0);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_75, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_75, 4);
lean_inc(x_80);
x_81 = lean_ctor_get(x_75, 5);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_75, 6);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_75, 7);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_75, 8);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_75, 9);
lean_inc_ref(x_85);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 lean_ctor_release(x_75, 4);
 lean_ctor_release(x_75, 5);
 lean_ctor_release(x_75, 6);
 lean_ctor_release(x_75, 7);
 lean_ctor_release(x_75, 8);
 lean_ctor_release(x_75, 9);
 x_86 = x_75;
} else {
 lean_dec_ref(x_75);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 10, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_77);
lean_ctor_set(x_87, 1, x_78);
lean_ctor_set(x_87, 2, x_73);
lean_ctor_set(x_87, 3, x_79);
lean_ctor_set(x_87, 4, x_80);
lean_ctor_set(x_87, 5, x_81);
lean_ctor_set(x_87, 6, x_82);
lean_ctor_set(x_87, 7, x_83);
lean_ctor_set(x_87, 8, x_84);
lean_ctor_set(x_87, 9, x_85);
x_88 = lean_st_ref_set(x_4, x_87, x_76);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_72);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_69, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_69, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_94 = x_69;
} else {
 lean_dec_ref(x_69);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind simp", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpCore___lam__0___boxed), 9, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Meta_Grind_simpCore___closed__0;
x_13 = lean_box(0);
x_14 = l_Lean_profileitM___at___Lean_Meta_Grind_simpCore_spec__0___redArg(x_12, x_10, x_11, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_Meta_Grind_simpCore_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_profileitM___at___Lean_Meta_Grind_simpCore_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_Meta_Grind_simpCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_profileitM___at___Lean_Meta_Grind_simpCore_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_simpCore___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_11, 2);
x_15 = l_Lean_Meta_Grind_simpCore___lam__0___closed__13;
lean_ctor_set(x_11, 2, x_15);
x_16 = lean_st_ref_set(x_4, x_11, x_12);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_19);
lean_dec_ref(x_3);
x_20 = l_Lean_Meta_Simp_dsimpMainCore(x_1, x_18, x_14, x_19, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_st_ref_take(x_4, x_22);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_26, 2);
lean_dec(x_29);
lean_ctor_set(x_26, 2, x_24);
x_30 = lean_st_ref_set(x_4, x_26, x_27);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_ctor_get(x_26, 1);
x_37 = lean_ctor_get(x_26, 3);
x_38 = lean_ctor_get(x_26, 4);
x_39 = lean_ctor_get(x_26, 5);
x_40 = lean_ctor_get(x_26, 6);
x_41 = lean_ctor_get(x_26, 7);
x_42 = lean_ctor_get(x_26, 8);
x_43 = lean_ctor_get(x_26, 9);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_26);
x_44 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 2, x_24);
lean_ctor_set(x_44, 3, x_37);
lean_ctor_set(x_44, 4, x_38);
lean_ctor_set(x_44, 5, x_39);
lean_ctor_set(x_44, 6, x_40);
lean_ctor_set(x_44, 7, x_41);
lean_ctor_set(x_44, 8, x_42);
lean_ctor_set(x_44, 9, x_43);
x_45 = lean_st_ref_set(x_4, x_44, x_27);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_23);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_20);
if (x_49 == 0)
{
return x_20;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_20, 0);
x_51 = lean_ctor_get(x_20, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_20);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_53 = lean_ctor_get(x_11, 0);
x_54 = lean_ctor_get(x_11, 1);
x_55 = lean_ctor_get(x_11, 2);
x_56 = lean_ctor_get(x_11, 3);
x_57 = lean_ctor_get(x_11, 4);
x_58 = lean_ctor_get(x_11, 5);
x_59 = lean_ctor_get(x_11, 6);
x_60 = lean_ctor_get(x_11, 7);
x_61 = lean_ctor_get(x_11, 8);
x_62 = lean_ctor_get(x_11, 9);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_11);
x_63 = l_Lean_Meta_Grind_simpCore___lam__0___closed__13;
x_64 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_64, 0, x_53);
lean_ctor_set(x_64, 1, x_54);
lean_ctor_set(x_64, 2, x_63);
lean_ctor_set(x_64, 3, x_56);
lean_ctor_set(x_64, 4, x_57);
lean_ctor_set(x_64, 5, x_58);
lean_ctor_set(x_64, 6, x_59);
lean_ctor_set(x_64, 7, x_60);
lean_ctor_set(x_64, 8, x_61);
lean_ctor_set(x_64, 9, x_62);
x_65 = lean_st_ref_set(x_4, x_64, x_12);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec_ref(x_65);
x_67 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_68);
lean_dec_ref(x_3);
x_69 = l_Lean_Meta_Simp_dsimpMainCore(x_1, x_67, x_55, x_68, x_5, x_6, x_7, x_8, x_66);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_st_ref_take(x_4, x_71);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec_ref(x_74);
x_77 = lean_ctor_get(x_75, 0);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_75, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_75, 4);
lean_inc(x_80);
x_81 = lean_ctor_get(x_75, 5);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_75, 6);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_75, 7);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_75, 8);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_75, 9);
lean_inc_ref(x_85);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 lean_ctor_release(x_75, 4);
 lean_ctor_release(x_75, 5);
 lean_ctor_release(x_75, 6);
 lean_ctor_release(x_75, 7);
 lean_ctor_release(x_75, 8);
 lean_ctor_release(x_75, 9);
 x_86 = x_75;
} else {
 lean_dec_ref(x_75);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 10, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_77);
lean_ctor_set(x_87, 1, x_78);
lean_ctor_set(x_87, 2, x_73);
lean_ctor_set(x_87, 3, x_79);
lean_ctor_set(x_87, 4, x_80);
lean_ctor_set(x_87, 5, x_81);
lean_ctor_set(x_87, 6, x_82);
lean_ctor_set(x_87, 7, x_83);
lean_ctor_set(x_87, 8, x_84);
lean_ctor_set(x_87, 9, x_85);
x_88 = lean_st_ref_set(x_4, x_87, x_76);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_72);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_69, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_69, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_94 = x_69;
} else {
 lean_dec_ref(x_69);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_dsimpCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind dsimp", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_dsimpCore___lam__0___boxed), 9, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Meta_Grind_dsimpCore___closed__0;
x_13 = lean_box(0);
x_14 = l_Lean_profileitM___at___Lean_Meta_Grind_simpCore_spec__0___redArg(x_12, x_10, x_11, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_dsimpCore___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_6 = lean_st_ref_get(x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
lean_dec(x_7);
x_10 = l_Lean_instantiateMVarsCore(x_9, x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_st_ref_take(x_2, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
lean_ctor_set(x_14, 0, x_12);
x_18 = lean_st_ref_set(x_2, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_11);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_14, 1);
x_24 = lean_ctor_get(x_14, 2);
x_25 = lean_ctor_get(x_14, 3);
x_26 = lean_ctor_get(x_14, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
lean_ctor_set(x_27, 4, x_26);
x_28 = lean_st_ref_set(x_2, x_27, x_15);
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
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_11);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0___redArg(x_1, x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_preprocess_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 13);
x_6 = l_Lean_checkTraceOption(x_5, x_4, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_preprocess_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_preprocess_spec__1___redArg(x_1, x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_4, 2);
lean_inc(x_17);
lean_inc_ref(x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set(x_18, 3, x_17);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_18);
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_4, 2);
lean_inc(x_23);
lean_inc_ref(x_22);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_3, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_2, 2);
x_35 = lean_ctor_get(x_4, 2);
lean_inc(x_35);
lean_inc_ref(x_34);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_1);
if (lean_is_scalar(x_32)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_32;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
return x_38;
}
}
}
static double _init_l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2_spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_st_ref_take(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 4);
lean_inc_ref(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_13, 4);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; double x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__0;
x_23 = 0;
x_24 = l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__1;
x_25 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_float(x_25, sizeof(void*)*2, x_22);
lean_ctor_set_float(x_25, sizeof(void*)*2 + 8, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 16, x_23);
x_26 = l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__2;
x_27 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_10);
lean_ctor_set(x_27, 2, x_26);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_27);
lean_ctor_set(x_12, 0, x_8);
x_28 = l_Lean_PersistentArray_push___redArg(x_21, x_12);
lean_ctor_set(x_14, 0, x_28);
x_29 = lean_st_ref_set(x_6, x_13, x_16);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint64_t x_36; lean_object* x_37; double x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_37 = lean_ctor_get(x_14, 0);
lean_inc(x_37);
lean_dec(x_14);
x_38 = l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__0;
x_39 = 0;
x_40 = l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__1;
x_41 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set_float(x_41, sizeof(void*)*2, x_38);
lean_ctor_set_float(x_41, sizeof(void*)*2 + 8, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 16, x_39);
x_42 = l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__2;
x_43 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_10);
lean_ctor_set(x_43, 2, x_42);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_43);
lean_ctor_set(x_12, 0, x_8);
x_44 = l_Lean_PersistentArray_push___redArg(x_37, x_12);
x_45 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint64(x_45, sizeof(void*)*1, x_36);
lean_ctor_set(x_13, 4, x_45);
x_46 = lean_st_ref_set(x_6, x_13, x_16);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint64_t x_59; lean_object* x_60; lean_object* x_61; double x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_51 = lean_ctor_get(x_13, 0);
x_52 = lean_ctor_get(x_13, 1);
x_53 = lean_ctor_get(x_13, 2);
x_54 = lean_ctor_get(x_13, 3);
x_55 = lean_ctor_get(x_13, 5);
x_56 = lean_ctor_get(x_13, 6);
x_57 = lean_ctor_get(x_13, 7);
x_58 = lean_ctor_get(x_13, 8);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_13);
x_59 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_60 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_60);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_61 = x_14;
} else {
 lean_dec_ref(x_14);
 x_61 = lean_box(0);
}
x_62 = l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__0;
x_63 = 0;
x_64 = l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__1;
x_65 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set_float(x_65, sizeof(void*)*2, x_62);
lean_ctor_set_float(x_65, sizeof(void*)*2 + 8, x_62);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 16, x_63);
x_66 = l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__2;
x_67 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_10);
lean_ctor_set(x_67, 2, x_66);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_67);
lean_ctor_set(x_12, 0, x_8);
x_68 = l_Lean_PersistentArray_push___redArg(x_60, x_12);
if (lean_is_scalar(x_61)) {
 x_69 = lean_alloc_ctor(0, 1, 8);
} else {
 x_69 = x_61;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set_uint64(x_69, sizeof(void*)*1, x_59);
x_70 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_70, 0, x_51);
lean_ctor_set(x_70, 1, x_52);
lean_ctor_set(x_70, 2, x_53);
lean_ctor_set(x_70, 3, x_54);
lean_ctor_set(x_70, 4, x_69);
lean_ctor_set(x_70, 5, x_55);
lean_ctor_set(x_70, 6, x_56);
lean_ctor_set(x_70, 7, x_57);
lean_ctor_set(x_70, 8, x_58);
x_71 = lean_st_ref_set(x_6, x_70, x_16);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
x_74 = lean_box(0);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; lean_object* x_88; double x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_76 = lean_ctor_get(x_12, 1);
lean_inc(x_76);
lean_dec(x_12);
x_77 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_13, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_13, 2);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_13, 3);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_13, 5);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_13, 6);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_13, 7);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_13, 8);
lean_inc_ref(x_84);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 lean_ctor_release(x_13, 6);
 lean_ctor_release(x_13, 7);
 lean_ctor_release(x_13, 8);
 x_85 = x_13;
} else {
 lean_dec_ref(x_13);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_87 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_87);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_88 = x_14;
} else {
 lean_dec_ref(x_14);
 x_88 = lean_box(0);
}
x_89 = l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__0;
x_90 = 0;
x_91 = l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__1;
x_92 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set_float(x_92, sizeof(void*)*2, x_89);
lean_ctor_set_float(x_92, sizeof(void*)*2 + 8, x_89);
lean_ctor_set_uint8(x_92, sizeof(void*)*2 + 16, x_90);
x_93 = l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__2;
x_94 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_10);
lean_ctor_set(x_94, 2, x_93);
lean_inc(x_8);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_8);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_PersistentArray_push___redArg(x_87, x_95);
if (lean_is_scalar(x_88)) {
 x_97 = lean_alloc_ctor(0, 1, 8);
} else {
 x_97 = x_88;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set_uint64(x_97, sizeof(void*)*1, x_86);
if (lean_is_scalar(x_85)) {
 x_98 = lean_alloc_ctor(0, 9, 0);
} else {
 x_98 = x_85;
}
lean_ctor_set(x_98, 0, x_77);
lean_ctor_set(x_98, 1, x_78);
lean_ctor_set(x_98, 2, x_79);
lean_ctor_set(x_98, 3, x_80);
lean_ctor_set(x_98, 4, x_97);
lean_ctor_set(x_98, 5, x_81);
lean_ctor_set(x_98, 6, x_82);
lean_ctor_set(x_98, 7, x_83);
lean_ctor_set(x_98, 8, x_84);
x_99 = lean_st_ref_set(x_6, x_98, x_76);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
x_102 = lean_box(0);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_preprocess___closed__1;
x_2 = l_Lean_Meta_Grind_preprocess___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n===>\n", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_preprocess___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0___redArg(x_1, x_7, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_12);
x_14 = l_Lean_Meta_Grind_simpCore(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_17);
x_18 = l_Lean_Meta_Grind_unfoldReducible(x_17, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_21 = l_Lean_Meta_Grind_abstractNestedProofs___redArg(x_19, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_24 = l_Lean_Meta_Grind_markNestedSubsingletons(x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
lean_inc(x_9);
lean_inc_ref(x_8);
x_27 = l_Lean_Meta_Grind_eraseIrrelevantMData(x_25, x_8, x_9, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_30 = l_Lean_Meta_Grind_foldProjs(x_28, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
lean_inc(x_9);
lean_inc_ref(x_8);
x_33 = l_Lean_Meta_Grind_normalizeLevels(x_31, x_8, x_9, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_36 = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(x_34, x_6, x_7, x_8, x_9, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_37);
x_39 = l_Lean_Meta_Simp_Result_mkEqTrans(x_15, x_37, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_42);
lean_dec(x_37);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_43 = l_Lean_Meta_Grind_replacePreMatchCond(x_42, x_6, x_7, x_8, x_9, x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_44);
x_46 = l_Lean_Meta_Simp_Result_mkEqTrans(x_40, x_44, x_6, x_7, x_8, x_9, x_45);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
x_50 = lean_ctor_get(x_44, 0);
lean_inc_ref(x_50);
lean_dec(x_44);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_51 = lean_grind_canon(x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
x_54 = l_Lean_Meta_Grind_shareCommon___redArg(x_52, x_5, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
x_67 = l_Lean_Meta_Grind_preprocess___closed__2;
x_68 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_preprocess_spec__1___redArg(x_67, x_8, x_56);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; 
lean_free_object(x_46);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec_ref(x_68);
x_58 = x_71;
goto block_66;
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_68);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_68, 1);
x_74 = lean_ctor_get(x_68, 0);
lean_dec(x_74);
x_75 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_73);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec_ref(x_75);
x_77 = l_Lean_MessageData_ofExpr(x_12);
x_78 = l_Lean_Meta_Grind_preprocess___closed__4;
lean_ctor_set_tag(x_68, 7);
lean_ctor_set(x_68, 1, x_78);
lean_ctor_set(x_68, 0, x_77);
lean_inc(x_55);
x_79 = l_Lean_MessageData_ofExpr(x_55);
lean_ctor_set_tag(x_46, 7);
lean_ctor_set(x_46, 1, x_79);
lean_ctor_set(x_46, 0, x_68);
x_80 = l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg(x_67, x_46, x_6, x_7, x_8, x_9, x_76);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec_ref(x_80);
x_58 = x_81;
goto block_66;
}
else
{
uint8_t x_82; 
lean_free_object(x_68);
lean_dec(x_57);
lean_dec(x_55);
lean_free_object(x_46);
lean_dec(x_48);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_82 = !lean_is_exclusive(x_75);
if (x_82 == 0)
{
return x_75;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_75, 0);
x_84 = lean_ctor_get(x_75, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_75);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_68, 1);
lean_inc(x_86);
lean_dec(x_68);
x_87 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_86);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec_ref(x_87);
x_89 = l_Lean_MessageData_ofExpr(x_12);
x_90 = l_Lean_Meta_Grind_preprocess___closed__4;
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
lean_inc(x_55);
x_92 = l_Lean_MessageData_ofExpr(x_55);
lean_ctor_set_tag(x_46, 7);
lean_ctor_set(x_46, 1, x_92);
lean_ctor_set(x_46, 0, x_91);
x_93 = l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg(x_67, x_46, x_6, x_7, x_8, x_9, x_88);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec_ref(x_93);
x_58 = x_94;
goto block_66;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_57);
lean_dec(x_55);
lean_free_object(x_46);
lean_dec(x_48);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_95 = lean_ctor_get(x_87, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_87, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_97 = x_87;
} else {
 lean_dec_ref(x_87);
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
block_66:
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_48);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_48, 0);
lean_dec(x_60);
lean_ctor_set(x_48, 0, x_55);
if (lean_is_scalar(x_57)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_57;
}
lean_ctor_set(x_61, 0, x_48);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
else
{
lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_48, 1);
x_63 = lean_ctor_get_uint8(x_48, sizeof(void*)*2);
lean_inc(x_62);
lean_dec(x_48);
x_64 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_64, 0, x_55);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_63);
if (lean_is_scalar(x_57)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_57;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_58);
return x_65;
}
}
}
else
{
uint8_t x_99; 
lean_free_object(x_46);
lean_dec(x_48);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_99 = !lean_is_exclusive(x_54);
if (x_99 == 0)
{
return x_54;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_54, 0);
x_101 = lean_ctor_get(x_54, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_54);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_free_object(x_46);
lean_dec(x_48);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_103 = !lean_is_exclusive(x_51);
if (x_103 == 0)
{
return x_51;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_51, 0);
x_105 = lean_ctor_get(x_51, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_51);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_46, 0);
x_108 = lean_ctor_get(x_46, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_46);
x_109 = lean_ctor_get(x_44, 0);
lean_inc_ref(x_109);
lean_dec(x_44);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_110 = lean_grind_canon(x_109, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_108);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec_ref(x_110);
x_113 = l_Lean_Meta_Grind_shareCommon___redArg(x_111, x_5, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_116 = x_113;
} else {
 lean_dec_ref(x_113);
 x_116 = lean_box(0);
}
x_124 = l_Lean_Meta_Grind_preprocess___closed__2;
x_125 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_preprocess_spec__1___redArg(x_124, x_8, x_115);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_unbox(x_126);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec_ref(x_125);
x_117 = x_128;
goto block_123;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_125, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_130 = x_125;
} else {
 lean_dec_ref(x_125);
 x_130 = lean_box(0);
}
x_131 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_129);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec_ref(x_131);
x_133 = l_Lean_MessageData_ofExpr(x_12);
x_134 = l_Lean_Meta_Grind_preprocess___closed__4;
if (lean_is_scalar(x_130)) {
 x_135 = lean_alloc_ctor(7, 2, 0);
} else {
 x_135 = x_130;
 lean_ctor_set_tag(x_135, 7);
}
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
lean_inc(x_114);
x_136 = l_Lean_MessageData_ofExpr(x_114);
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg(x_124, x_137, x_6, x_7, x_8, x_9, x_132);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec_ref(x_138);
x_117 = x_139;
goto block_123;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_130);
lean_dec(x_116);
lean_dec(x_114);
lean_dec(x_107);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_140 = lean_ctor_get(x_131, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_131, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_142 = x_131;
} else {
 lean_dec_ref(x_131);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
block_123:
{
lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_118 = lean_ctor_get(x_107, 1);
lean_inc(x_118);
x_119 = lean_ctor_get_uint8(x_107, sizeof(void*)*2);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_120 = x_107;
} else {
 lean_dec_ref(x_107);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(0, 2, 1);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_114);
lean_ctor_set(x_121, 1, x_118);
lean_ctor_set_uint8(x_121, sizeof(void*)*2, x_119);
if (lean_is_scalar(x_116)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_116;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_117);
return x_122;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_107);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_144 = lean_ctor_get(x_113, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_113, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_146 = x_113;
} else {
 lean_dec_ref(x_113);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_107);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_148 = lean_ctor_get(x_110, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_110, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_150 = x_110;
} else {
 lean_dec_ref(x_110);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
}
else
{
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_46;
}
}
else
{
lean_dec(x_40);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_43;
}
}
else
{
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_39;
}
}
else
{
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_36;
}
}
else
{
uint8_t x_152; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_152 = !lean_is_exclusive(x_33);
if (x_152 == 0)
{
return x_33;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_33, 0);
x_154 = lean_ctor_get(x_33, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_33);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_156 = !lean_is_exclusive(x_30);
if (x_156 == 0)
{
return x_30;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_30, 0);
x_158 = lean_ctor_get(x_30, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_30);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_160 = !lean_is_exclusive(x_27);
if (x_160 == 0)
{
return x_27;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_27, 0);
x_162 = lean_ctor_get(x_27, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_27);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
else
{
uint8_t x_164; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_164 = !lean_is_exclusive(x_24);
if (x_164 == 0)
{
return x_24;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_24, 0);
x_166 = lean_ctor_get(x_24, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_24);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
else
{
uint8_t x_168; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_168 = !lean_is_exclusive(x_21);
if (x_168 == 0)
{
return x_21;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_21, 0);
x_170 = lean_ctor_get(x_21, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_21);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
uint8_t x_172; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_172 = !lean_is_exclusive(x_18);
if (x_172 == 0)
{
return x_18;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_18, 0);
x_174 = lean_ctor_get(x_18, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_18);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_preprocess_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_preprocess_spec__1___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_preprocess_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_preprocess_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pushNewFact", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_pushNewFact_x27___closed__1;
x_2 = l_Lean_Meta_Grind_pushNewFact_x27___closed__0;
x_3 = l_Lean_Meta_Grind_preprocess___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ==> ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_pushNewFact_x27___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mp", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_pushNewFact_x27___closed__6;
x_2 = l_Lean_Meta_Grind_pushNewFact_x27___closed__5;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_pushNewFact_x27___closed__8;
x_2 = l_Lean_Meta_Grind_pushNewFact_x27___closed__7;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_4);
lean_inc_ref(x_1);
x_13 = l_Lean_Meta_Grind_preprocess(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_61; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 0)
{
x_61 = x_2;
goto block_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_17, 0);
lean_inc(x_85);
lean_dec_ref(x_17);
x_86 = l_Lean_Meta_Grind_pushNewFact_x27___closed__9;
lean_inc_ref(x_16);
lean_inc_ref(x_1);
x_87 = l_Lean_mkApp4(x_86, x_1, x_16, x_85, x_2);
x_61 = x_87;
goto block_84;
}
block_60:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_st_ref_take(x_19, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_22, 7);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set(x_26, 2, x_3);
x_27 = lean_array_push(x_25, x_26);
lean_ctor_set(x_22, 7, x_27);
x_28 = lean_st_ref_set(x_19, x_22, x_23);
lean_dec(x_19);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = lean_ctor_get(x_22, 1);
x_37 = lean_ctor_get(x_22, 2);
x_38 = lean_ctor_get(x_22, 3);
x_39 = lean_ctor_get(x_22, 4);
x_40 = lean_ctor_get(x_22, 5);
x_41 = lean_ctor_get(x_22, 6);
x_42 = lean_ctor_get(x_22, 7);
x_43 = lean_ctor_get_uint8(x_22, sizeof(void*)*16);
x_44 = lean_ctor_get(x_22, 8);
x_45 = lean_ctor_get(x_22, 9);
x_46 = lean_ctor_get(x_22, 10);
x_47 = lean_ctor_get(x_22, 11);
x_48 = lean_ctor_get(x_22, 12);
x_49 = lean_ctor_get(x_22, 13);
x_50 = lean_ctor_get(x_22, 14);
x_51 = lean_ctor_get(x_22, 15);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_22);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_16);
lean_ctor_set(x_52, 1, x_18);
lean_ctor_set(x_52, 2, x_3);
x_53 = lean_array_push(x_42, x_52);
x_54 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_54, 0, x_35);
lean_ctor_set(x_54, 1, x_36);
lean_ctor_set(x_54, 2, x_37);
lean_ctor_set(x_54, 3, x_38);
lean_ctor_set(x_54, 4, x_39);
lean_ctor_set(x_54, 5, x_40);
lean_ctor_set(x_54, 6, x_41);
lean_ctor_set(x_54, 7, x_53);
lean_ctor_set(x_54, 8, x_44);
lean_ctor_set(x_54, 9, x_45);
lean_ctor_set(x_54, 10, x_46);
lean_ctor_set(x_54, 11, x_47);
lean_ctor_set(x_54, 12, x_48);
lean_ctor_set(x_54, 13, x_49);
lean_ctor_set(x_54, 14, x_50);
lean_ctor_set(x_54, 15, x_51);
lean_ctor_set_uint8(x_54, sizeof(void*)*16, x_43);
x_55 = lean_st_ref_set(x_19, x_54, x_23);
lean_dec(x_19);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = lean_box(0);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
block_84:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = l_Lean_Meta_Grind_pushNewFact_x27___closed__2;
x_63 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_preprocess_spec__1___redArg(x_62, x_10, x_15);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec_ref(x_63);
x_18 = x_61;
x_19 = x_4;
x_20 = x_66;
goto block_60;
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_63);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = lean_ctor_get(x_63, 1);
x_69 = lean_ctor_get(x_63, 0);
lean_dec(x_69);
x_70 = l_Lean_MessageData_ofExpr(x_1);
x_71 = l_Lean_Meta_Grind_pushNewFact_x27___closed__4;
lean_ctor_set_tag(x_63, 7);
lean_ctor_set(x_63, 1, x_71);
lean_ctor_set(x_63, 0, x_70);
lean_inc_ref(x_16);
x_72 = l_Lean_MessageData_ofExpr(x_16);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_63);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg(x_62, x_73, x_8, x_9, x_10, x_11, x_68);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec_ref(x_74);
x_18 = x_61;
x_19 = x_4;
x_20 = x_75;
goto block_60;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_76 = lean_ctor_get(x_63, 1);
lean_inc(x_76);
lean_dec(x_63);
x_77 = l_Lean_MessageData_ofExpr(x_1);
x_78 = l_Lean_Meta_Grind_pushNewFact_x27___closed__4;
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
lean_inc_ref(x_16);
x_80 = l_Lean_MessageData_ofExpr(x_16);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg(x_62, x_81, x_8, x_9, x_10, x_11, x_76);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec_ref(x_82);
x_18 = x_61;
x_19 = x_4;
x_20 = x_83;
goto block_60;
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_88 = !lean_is_exclusive(x_13);
if (x_88 == 0)
{
return x_13;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_13, 0);
x_90 = lean_ctor_get(x_13, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_13);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_1);
x_12 = lean_infer_type(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l_Lean_Meta_Grind_pushNewFact_x27___closed__2;
x_16 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_preprocess_spec__1___redArg(x_15, x_9, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = l_Lean_Meta_Grind_pushNewFact_x27(x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec_ref(x_16);
lean_inc(x_13);
x_22 = l_Lean_MessageData_ofExpr(x_13);
x_23 = l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg(x_15, x_22, x_7, x_8, x_9, x_10, x_21);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = l_Lean_Meta_Grind_pushNewFact_x27(x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessLight(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_11 = l_Lean_Meta_Grind_unfoldReducible(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_14 = l_Lean_Meta_Grind_markNestedSubsingletons(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
lean_inc(x_9);
lean_inc_ref(x_8);
x_17 = l_Lean_Meta_Grind_eraseIrrelevantMData(x_15, x_8, x_9, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_20 = l_Lean_Meta_Grind_foldProjs(x_18, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
lean_inc(x_9);
lean_inc_ref(x_8);
x_23 = l_Lean_Meta_Grind_normalizeLevels(x_21, x_8, x_9, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
lean_inc(x_5);
x_26 = lean_grind_canon(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l_Lean_Meta_Grind_shareCommon___redArg(x_27, x_5, x_28);
lean_dec(x_5);
return x_29;
}
else
{
lean_dec(x_5);
return x_26;
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_23;
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_20;
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
}
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_simpCore___lam__0___closed__0 = _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__0___closed__0);
l_Lean_Meta_Grind_simpCore___lam__0___closed__1 = _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__0___closed__1);
l_Lean_Meta_Grind_simpCore___lam__0___closed__2 = _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__0___closed__2);
l_Lean_Meta_Grind_simpCore___lam__0___closed__3 = _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__0___closed__3);
l_Lean_Meta_Grind_simpCore___lam__0___closed__4 = _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__0___closed__4);
l_Lean_Meta_Grind_simpCore___lam__0___closed__5 = _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__0___closed__5);
l_Lean_Meta_Grind_simpCore___lam__0___closed__6 = _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__0___closed__6);
l_Lean_Meta_Grind_simpCore___lam__0___closed__7 = _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__0___closed__7);
l_Lean_Meta_Grind_simpCore___lam__0___closed__8 = _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__0___closed__8);
l_Lean_Meta_Grind_simpCore___lam__0___closed__9 = _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__0___closed__9);
l_Lean_Meta_Grind_simpCore___lam__0___closed__10 = _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__0___closed__10);
l_Lean_Meta_Grind_simpCore___lam__0___closed__11 = _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__0___closed__11);
l_Lean_Meta_Grind_simpCore___lam__0___closed__12 = _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__0___closed__12);
l_Lean_Meta_Grind_simpCore___lam__0___closed__13 = _init_l_Lean_Meta_Grind_simpCore___lam__0___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__0___closed__13);
l_Lean_Meta_Grind_simpCore___closed__0 = _init_l_Lean_Meta_Grind_simpCore___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___closed__0);
l_Lean_Meta_Grind_dsimpCore___closed__0 = _init_l_Lean_Meta_Grind_dsimpCore___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_dsimpCore___closed__0);
l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__0 = _init_l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__0();
l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__1 = _init_l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__1);
l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__2 = _init_l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Meta_Grind_preprocess_spec__2___redArg___closed__2);
l_Lean_Meta_Grind_preprocess___closed__0 = _init_l_Lean_Meta_Grind_preprocess___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__0);
l_Lean_Meta_Grind_preprocess___closed__1 = _init_l_Lean_Meta_Grind_preprocess___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__1);
l_Lean_Meta_Grind_preprocess___closed__2 = _init_l_Lean_Meta_Grind_preprocess___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__2);
l_Lean_Meta_Grind_preprocess___closed__3 = _init_l_Lean_Meta_Grind_preprocess___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__3);
l_Lean_Meta_Grind_preprocess___closed__4 = _init_l_Lean_Meta_Grind_preprocess___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__4);
l_Lean_Meta_Grind_pushNewFact_x27___closed__0 = _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_pushNewFact_x27___closed__0);
l_Lean_Meta_Grind_pushNewFact_x27___closed__1 = _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_pushNewFact_x27___closed__1);
l_Lean_Meta_Grind_pushNewFact_x27___closed__2 = _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_pushNewFact_x27___closed__2);
l_Lean_Meta_Grind_pushNewFact_x27___closed__3 = _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_pushNewFact_x27___closed__3);
l_Lean_Meta_Grind_pushNewFact_x27___closed__4 = _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_pushNewFact_x27___closed__4);
l_Lean_Meta_Grind_pushNewFact_x27___closed__5 = _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_pushNewFact_x27___closed__5);
l_Lean_Meta_Grind_pushNewFact_x27___closed__6 = _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_pushNewFact_x27___closed__6);
l_Lean_Meta_Grind_pushNewFact_x27___closed__7 = _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_pushNewFact_x27___closed__7);
l_Lean_Meta_Grind_pushNewFact_x27___closed__8 = _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_pushNewFact_x27___closed__8);
l_Lean_Meta_Grind_pushNewFact_x27___closed__9 = _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_pushNewFact_x27___closed__9);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
