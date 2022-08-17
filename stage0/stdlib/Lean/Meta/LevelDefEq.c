// Lean compiler output
// Module: Lean.Meta.LevelDefEq
// Imports: Init Lean.Util.CollectMVars Lean.Meta.Basic Lean.Meta.InferType Lean.Meta.DecLevel
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
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__9;
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lambda__1___closed__1;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__6;
lean_object* l_Lean_assignLevelMVar___at_Lean_Meta_normalizeLevel___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_15_(uint8_t, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8;
lean_object* l_Lean_withTraceNode___at_Lean_Meta_processPostponed___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3;
lean_object* l_Lean_Level_getOffsetAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_isLevelDefEqAuxImpl___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5;
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Meta_isLevelDefEqAuxImpl___spec__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lambda__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax___boxed(lean_object*, lean_object*);
lean_object* lean_is_level_def_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___spec__1___closed__1;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__10;
uint8_t l_Lean_Level_isParam(lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__6;
LEAN_EXPORT uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1;
LEAN_EXPORT lean_object* lean_is_level_def_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwIsDefEqStuck___rarg(lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMetaM;
lean_object* l_Lean_LMVarId_isReadOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit___boxed(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_isLevelDefEqAuxImpl___spec__3___closed__1;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__7;
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3;
lean_object* l_Lean_exceptBoolEmoji___rarg(lean_object*);
extern uint8_t l_instInhabitedBool;
lean_object* l_Lean_LMVarId_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize(lean_object*);
uint8_t l_Bool_toLBool(uint8_t);
static lean_object* l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__3;
uint8_t l_Lean_Level_isMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_isLevelMVarAssignable___spec__1(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
lean_object* l_Lean_Level_getLevelOffset(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Meta_isLevelDefEqAuxImpl___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__4;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1;
static lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
uint8_t l_Lean_Level_occurs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at_Lean_Meta_isLevelDefEqAuxImpl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_LevelDefEq___hyg_1333_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Meta_isLevelDefEqAuxImpl___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__1;
lean_object* l_Lean_Meta_decLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isMax(lean_object*);
static lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lambda__1___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(x_1, x_3);
if (x_5 == 0)
{
x_2 = x_4;
goto _start;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = lean_level_eq(x_2, x_1);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Level_occurs(x_1, x_2);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(x_1, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(x_1, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(x_1, x_4, x_3);
x_2 = x_5;
x_3 = x_6;
goto _start;
}
case 5:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_name_eq(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_mkLevelMax_x27(x_3, x_2);
return x_10;
}
else
{
lean_dec(x_2);
return x_3;
}
}
default: 
{
lean_object* x_11; 
x_11 = l_Lean_mkLevelMax_x27(x_3, x_2);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___boxed), 5, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___spec__1___closed__1;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("assertion violation: ", 21);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("v.isMax\n  ", 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1;
x_2 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Meta.LevelDefEq", 20);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Meta.LevelDefEq.0.Lean.Meta.solveSelfMax", 54);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4;
x_2 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5;
x_3 = lean_unsigned_to_nat(34u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Level_isMax(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__6;
x_10 = l_panic___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___spec__1(x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(x_1, x_2, x_12);
x_15 = l_Lean_assignLevelMVar___at_Lean_Meta_normalizeLevel___spec__2(x_1, x_14, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_take(x_7, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_14, 3);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_3);
lean_ctor_set(x_19, 2, x_4);
lean_ctor_set(x_19, 3, x_18);
x_20 = l_Std_PersistentArray_push___rarg(x_17, x_19);
lean_ctor_set(x_14, 3, x_20);
x_21 = lean_st_ref_set(x_7, x_14, x_15);
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
x_30 = lean_ctor_get(x_14, 2);
x_31 = lean_ctor_get(x_14, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_32 = lean_ctor_get(x_1, 3);
lean_inc(x_32);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_3);
lean_ctor_set(x_33, 2, x_4);
lean_ctor_set(x_33, 3, x_32);
x_34 = l_Std_PersistentArray_push___rarg(x_31, x_33);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_29);
lean_ctor_set(x_35, 2, x_30);
lean_ctor_set(x_35, 3, x_34);
x_36 = lean_st_ref_set(x_7, x_35, x_15);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = lean_box(0);
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
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("isLevelDefEq", 12);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2;
x_2 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("stuck", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_2 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" =?= ", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_5, 5);
lean_inc(x_8);
x_9 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__6;
x_10 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_9, x_3, x_4, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_box(0);
x_15 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___lambda__1(x_3, x_8, x_1, x_2, x_14, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
lean_inc(x_1);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_1);
x_18 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__10;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_inc(x_2);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_2);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
x_25 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_9, x_24, x_3, x_4, x_5, x_6, x_16);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___lambda__1(x_3, x_8, x_1, x_2, x_26, x_3, x_4, x_5, x_6, x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_26);
lean_dec(x_3);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_LMVarId_getLevel(x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_LMVarId_getLevel(x_2, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_nat_dec_lt(x_14, x_10);
lean_dec(x_10);
lean_dec(x_14);
x_16 = lean_box(x_15);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_nat_dec_lt(x_17, x_10);
lean_dec(x_10);
lean_dec(x_17);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_10);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
return x_9;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
lean_dec(x_1);
x_30 = 0;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_7);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_Lean_levelZero;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = lean_is_level_def_eq(x_13, x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_unbox(x_15);
lean_dec(x_15);
x_20 = l_Bool_toLBool(x_19);
x_21 = lean_box(x_20);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_unbox(x_15);
lean_dec(x_15);
x_24 = l_Bool_toLBool(x_23);
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_15);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_dec(x_14);
x_28 = lean_is_level_def_eq(x_13, x_12, x_3, x_4, x_5, x_6, x_27);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
x_32 = l_Bool_toLBool(x_31);
x_33 = lean_box(x_32);
lean_ctor_set(x_28, 0, x_33);
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
x_36 = lean_unbox(x_34);
lean_dec(x_34);
x_37 = l_Bool_toLBool(x_36);
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_28);
if (x_40 == 0)
{
return x_28;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_28, 0);
x_42 = lean_ctor_get(x_28, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_28);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_14);
if (x_44 == 0)
{
return x_14;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_14, 0);
x_46 = lean_ctor_get(x_14, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_14);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
case 3:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_2, 1);
lean_inc(x_48);
lean_dec(x_2);
x_49 = l_Lean_levelZero;
x_50 = lean_is_level_def_eq(x_49, x_48, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
x_54 = l_Bool_toLBool(x_53);
x_55 = lean_box(x_54);
lean_ctor_set(x_50, 0, x_55);
return x_50;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_50);
x_58 = lean_unbox(x_56);
lean_dec(x_56);
x_59 = l_Bool_toLBool(x_58);
x_60 = lean_box(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_50);
if (x_62 == 0)
{
return x_50;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_50, 0);
x_64 = lean_ctor_get(x_50, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_50);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
default: 
{
uint8_t x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_66 = 2;
x_67 = lean_box(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_7);
return x_68;
}
}
}
case 1:
{
if (lean_obj_tag(x_2) == 5)
{
uint8_t x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = 2;
x_70 = lean_box(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_7);
return x_71;
}
else
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_1, 0);
lean_inc(x_72);
lean_dec(x_1);
x_73 = l_Lean_Level_isParam(x_2);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = l_Lean_Level_isMVar(x_72);
if (x_74 == 0)
{
lean_object* x_75; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_75 = l_Lean_Meta_decLevel_x3f(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_77; 
lean_dec(x_72);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_75);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_75, 0);
lean_dec(x_78);
x_79 = 2;
x_80 = lean_box(x_79);
lean_ctor_set(x_75, 0, x_80);
return x_75;
}
else
{
lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
lean_dec(x_75);
x_82 = 2;
x_83 = lean_box(x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_75, 1);
lean_inc(x_85);
lean_dec(x_75);
x_86 = lean_ctor_get(x_76, 0);
lean_inc(x_86);
lean_dec(x_76);
x_87 = lean_is_level_def_eq(x_72, x_86, x_3, x_4, x_5, x_6, x_85);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; uint8_t x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
x_91 = l_Bool_toLBool(x_90);
x_92 = lean_box(x_91);
lean_ctor_set(x_87, 0, x_92);
return x_87;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_87, 0);
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_87);
x_95 = lean_unbox(x_93);
lean_dec(x_93);
x_96 = l_Bool_toLBool(x_95);
x_97 = lean_box(x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_94);
return x_98;
}
}
else
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_87);
if (x_99 == 0)
{
return x_87;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_87, 0);
x_101 = lean_ctor_get(x_87, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_87);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_72);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_103 = !lean_is_exclusive(x_75);
if (x_103 == 0)
{
return x_75;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_75, 0);
x_105 = lean_ctor_get(x_75, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_75);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
x_107 = l_Lean_Level_occurs(x_72, x_2);
if (x_107 == 0)
{
lean_object* x_108; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_108 = l_Lean_Meta_decLevel_x3f(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
lean_dec(x_72);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_110 = !lean_is_exclusive(x_108);
if (x_110 == 0)
{
lean_object* x_111; uint8_t x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_108, 0);
lean_dec(x_111);
x_112 = 2;
x_113 = lean_box(x_112);
lean_ctor_set(x_108, 0, x_113);
return x_108;
}
else
{
lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_108, 1);
lean_inc(x_114);
lean_dec(x_108);
x_115 = 2;
x_116 = lean_box(x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_114);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_108, 1);
lean_inc(x_118);
lean_dec(x_108);
x_119 = lean_ctor_get(x_109, 0);
lean_inc(x_119);
lean_dec(x_109);
x_120 = lean_is_level_def_eq(x_72, x_119, x_3, x_4, x_5, x_6, x_118);
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; uint8_t x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_120, 0);
x_123 = lean_unbox(x_122);
lean_dec(x_122);
x_124 = l_Bool_toLBool(x_123);
x_125 = lean_box(x_124);
lean_ctor_set(x_120, 0, x_125);
return x_120;
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; 
x_126 = lean_ctor_get(x_120, 0);
x_127 = lean_ctor_get(x_120, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_120);
x_128 = lean_unbox(x_126);
lean_dec(x_126);
x_129 = l_Bool_toLBool(x_128);
x_130 = lean_box(x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_127);
return x_131;
}
}
else
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_120);
if (x_132 == 0)
{
return x_120;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_120, 0);
x_134 = lean_ctor_get(x_120, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_120);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_72);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_136 = !lean_is_exclusive(x_108);
if (x_136 == 0)
{
return x_108;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_108, 0);
x_138 = lean_ctor_get(x_108, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_108);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
uint8_t x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_72);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_140 = 2;
x_141 = lean_box(x_140);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_7);
return x_142;
}
}
}
else
{
uint8_t x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_72);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_143 = 0;
x_144 = lean_box(x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_7);
return x_145;
}
}
}
case 5:
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_1, 0);
lean_inc(x_146);
lean_inc(x_146);
x_147 = l_Lean_LMVarId_isReadOnly(x_146, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; uint8_t x_149; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_unbox(x_148);
lean_dec(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_dec(x_147);
x_151 = l_Lean_Meta_getConfig(x_3, x_4, x_5, x_6, x_150);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
lean_inc(x_2);
x_154 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(x_2, x_146, x_3, x_4, x_5, x_6, x_153);
if (lean_obj_tag(x_154) == 0)
{
uint8_t x_155; 
x_155 = lean_ctor_get_uint8(x_152, 11);
lean_dec(x_152);
if (x_155 == 0)
{
uint8_t x_156; 
x_156 = !lean_is_exclusive(x_154);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_157 = lean_ctor_get(x_154, 1);
x_158 = lean_ctor_get(x_154, 0);
lean_dec(x_158);
x_159 = l_Lean_Level_occurs(x_1, x_2);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_free_object(x_154);
x_160 = l_Lean_Level_mvarId_x21(x_1);
x_161 = l_Lean_assignLevelMVar___at_Lean_Meta_normalizeLevel___spec__2(x_160, x_2, x_3, x_4, x_5, x_6, x_157);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_162 = !lean_is_exclusive(x_161);
if (x_162 == 0)
{
lean_object* x_163; uint8_t x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_161, 0);
lean_dec(x_163);
x_164 = 1;
x_165 = lean_box(x_164);
lean_ctor_set(x_161, 0, x_165);
return x_161;
}
else
{
lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; 
x_166 = lean_ctor_get(x_161, 1);
lean_inc(x_166);
lean_dec(x_161);
x_167 = 1;
x_168 = lean_box(x_167);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_166);
return x_169;
}
}
else
{
uint8_t x_170; 
x_170 = l_Lean_Level_isMax(x_2);
if (x_170 == 0)
{
uint8_t x_171; lean_object* x_172; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_171 = 2;
x_172 = lean_box(x_171);
lean_ctor_set(x_154, 0, x_172);
return x_154;
}
else
{
uint8_t x_173; 
x_173 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(x_1, x_2);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; 
lean_free_object(x_154);
x_174 = l_Lean_Level_mvarId_x21(x_1);
x_175 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(x_174, x_2, x_3, x_4, x_5, x_6, x_157);
if (lean_obj_tag(x_175) == 0)
{
uint8_t x_176; 
x_176 = !lean_is_exclusive(x_175);
if (x_176 == 0)
{
lean_object* x_177; uint8_t x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_175, 0);
lean_dec(x_177);
x_178 = 1;
x_179 = lean_box(x_178);
lean_ctor_set(x_175, 0, x_179);
return x_175;
}
else
{
lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; 
x_180 = lean_ctor_get(x_175, 1);
lean_inc(x_180);
lean_dec(x_175);
x_181 = 1;
x_182 = lean_box(x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_180);
return x_183;
}
}
else
{
uint8_t x_184; 
x_184 = !lean_is_exclusive(x_175);
if (x_184 == 0)
{
return x_175;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_175, 0);
x_186 = lean_ctor_get(x_175, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_175);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
uint8_t x_188; lean_object* x_189; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_188 = 2;
x_189 = lean_box(x_188);
lean_ctor_set(x_154, 0, x_189);
return x_154;
}
}
}
}
else
{
lean_object* x_190; uint8_t x_191; 
x_190 = lean_ctor_get(x_154, 1);
lean_inc(x_190);
lean_dec(x_154);
x_191 = l_Lean_Level_occurs(x_1, x_2);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; 
x_192 = l_Lean_Level_mvarId_x21(x_1);
x_193 = l_Lean_assignLevelMVar___at_Lean_Meta_normalizeLevel___spec__2(x_192, x_2, x_3, x_4, x_5, x_6, x_190);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_195 = x_193;
} else {
 lean_dec_ref(x_193);
 x_195 = lean_box(0);
}
x_196 = 1;
x_197 = lean_box(x_196);
if (lean_is_scalar(x_195)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_195;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_194);
return x_198;
}
else
{
uint8_t x_199; 
x_199 = l_Lean_Level_isMax(x_2);
if (x_199 == 0)
{
uint8_t x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_200 = 2;
x_201 = lean_box(x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_190);
return x_202;
}
else
{
uint8_t x_203; 
x_203 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(x_1, x_2);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; 
x_204 = l_Lean_Level_mvarId_x21(x_1);
x_205 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(x_204, x_2, x_3, x_4, x_5, x_6, x_190);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; 
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_207 = x_205;
} else {
 lean_dec_ref(x_205);
 x_207 = lean_box(0);
}
x_208 = 1;
x_209 = lean_box(x_208);
if (lean_is_scalar(x_207)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_207;
}
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_206);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_211 = lean_ctor_get(x_205, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_205, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_213 = x_205;
} else {
 lean_dec_ref(x_205);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
return x_214;
}
}
else
{
uint8_t x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_215 = 2;
x_216 = lean_box(x_215);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_190);
return x_217;
}
}
}
}
}
else
{
lean_object* x_218; uint8_t x_219; 
x_218 = lean_ctor_get(x_154, 0);
lean_inc(x_218);
x_219 = lean_unbox(x_218);
lean_dec(x_218);
if (x_219 == 0)
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_154);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_221 = lean_ctor_get(x_154, 1);
x_222 = lean_ctor_get(x_154, 0);
lean_dec(x_222);
x_223 = l_Lean_Level_occurs(x_1, x_2);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; uint8_t x_226; 
lean_free_object(x_154);
x_224 = l_Lean_Level_mvarId_x21(x_1);
x_225 = l_Lean_assignLevelMVar___at_Lean_Meta_normalizeLevel___spec__2(x_224, x_2, x_3, x_4, x_5, x_6, x_221);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_226 = !lean_is_exclusive(x_225);
if (x_226 == 0)
{
lean_object* x_227; uint8_t x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_225, 0);
lean_dec(x_227);
x_228 = 1;
x_229 = lean_box(x_228);
lean_ctor_set(x_225, 0, x_229);
return x_225;
}
else
{
lean_object* x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; 
x_230 = lean_ctor_get(x_225, 1);
lean_inc(x_230);
lean_dec(x_225);
x_231 = 1;
x_232 = lean_box(x_231);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_230);
return x_233;
}
}
else
{
uint8_t x_234; 
x_234 = l_Lean_Level_isMax(x_2);
if (x_234 == 0)
{
uint8_t x_235; lean_object* x_236; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_235 = 2;
x_236 = lean_box(x_235);
lean_ctor_set(x_154, 0, x_236);
return x_154;
}
else
{
uint8_t x_237; 
x_237 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(x_1, x_2);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; 
lean_free_object(x_154);
x_238 = l_Lean_Level_mvarId_x21(x_1);
x_239 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(x_238, x_2, x_3, x_4, x_5, x_6, x_221);
if (lean_obj_tag(x_239) == 0)
{
uint8_t x_240; 
x_240 = !lean_is_exclusive(x_239);
if (x_240 == 0)
{
lean_object* x_241; uint8_t x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_239, 0);
lean_dec(x_241);
x_242 = 1;
x_243 = lean_box(x_242);
lean_ctor_set(x_239, 0, x_243);
return x_239;
}
else
{
lean_object* x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; 
x_244 = lean_ctor_get(x_239, 1);
lean_inc(x_244);
lean_dec(x_239);
x_245 = 1;
x_246 = lean_box(x_245);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_244);
return x_247;
}
}
else
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_239);
if (x_248 == 0)
{
return x_239;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_239, 0);
x_250 = lean_ctor_get(x_239, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_239);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
}
}
else
{
uint8_t x_252; lean_object* x_253; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_252 = 2;
x_253 = lean_box(x_252);
lean_ctor_set(x_154, 0, x_253);
return x_154;
}
}
}
}
else
{
lean_object* x_254; uint8_t x_255; 
x_254 = lean_ctor_get(x_154, 1);
lean_inc(x_254);
lean_dec(x_154);
x_255 = l_Lean_Level_occurs(x_1, x_2);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; lean_object* x_261; lean_object* x_262; 
x_256 = l_Lean_Level_mvarId_x21(x_1);
x_257 = l_Lean_assignLevelMVar___at_Lean_Meta_normalizeLevel___spec__2(x_256, x_2, x_3, x_4, x_5, x_6, x_254);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_258 = lean_ctor_get(x_257, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_259 = x_257;
} else {
 lean_dec_ref(x_257);
 x_259 = lean_box(0);
}
x_260 = 1;
x_261 = lean_box(x_260);
if (lean_is_scalar(x_259)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_259;
}
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_258);
return x_262;
}
else
{
uint8_t x_263; 
x_263 = l_Lean_Level_isMax(x_2);
if (x_263 == 0)
{
uint8_t x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_264 = 2;
x_265 = lean_box(x_264);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_254);
return x_266;
}
else
{
uint8_t x_267; 
x_267 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(x_1, x_2);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; 
x_268 = l_Lean_Level_mvarId_x21(x_1);
x_269 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(x_268, x_2, x_3, x_4, x_5, x_6, x_254);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; uint8_t x_272; lean_object* x_273; lean_object* x_274; 
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_271 = x_269;
} else {
 lean_dec_ref(x_269);
 x_271 = lean_box(0);
}
x_272 = 1;
x_273 = lean_box(x_272);
if (lean_is_scalar(x_271)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_271;
}
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_270);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_275 = lean_ctor_get(x_269, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_269, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_277 = x_269;
} else {
 lean_dec_ref(x_269);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
}
else
{
uint8_t x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_279 = 2;
x_280 = lean_box(x_279);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_254);
return x_281;
}
}
}
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_282 = lean_ctor_get(x_154, 1);
lean_inc(x_282);
lean_dec(x_154);
x_283 = l_Lean_Level_mvarId_x21(x_2);
x_284 = l_Lean_assignLevelMVar___at_Lean_Meta_normalizeLevel___spec__2(x_283, x_1, x_3, x_4, x_5, x_6, x_282);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_285 = !lean_is_exclusive(x_284);
if (x_285 == 0)
{
lean_object* x_286; uint8_t x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_284, 0);
lean_dec(x_286);
x_287 = 1;
x_288 = lean_box(x_287);
lean_ctor_set(x_284, 0, x_288);
return x_284;
}
else
{
lean_object* x_289; uint8_t x_290; lean_object* x_291; lean_object* x_292; 
x_289 = lean_ctor_get(x_284, 1);
lean_inc(x_289);
lean_dec(x_284);
x_290 = 1;
x_291 = lean_box(x_290);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_289);
return x_292;
}
}
}
}
else
{
uint8_t x_293; 
lean_dec(x_152);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_293 = !lean_is_exclusive(x_154);
if (x_293 == 0)
{
return x_154;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_154, 0);
x_295 = lean_ctor_get(x_154, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_154);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
return x_296;
}
}
}
else
{
uint8_t x_297; 
lean_dec(x_146);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_297 = !lean_is_exclusive(x_147);
if (x_297 == 0)
{
lean_object* x_298; uint8_t x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_147, 0);
lean_dec(x_298);
x_299 = 2;
x_300 = lean_box(x_299);
lean_ctor_set(x_147, 0, x_300);
return x_147;
}
else
{
lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; 
x_301 = lean_ctor_get(x_147, 1);
lean_inc(x_301);
lean_dec(x_147);
x_302 = 2;
x_303 = lean_box(x_302);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_301);
return x_304;
}
}
}
else
{
uint8_t x_305; 
lean_dec(x_146);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_305 = !lean_is_exclusive(x_147);
if (x_305 == 0)
{
return x_147;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_147, 0);
x_307 = lean_ctor_get(x_147, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_147);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
}
}
default: 
{
uint8_t x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_309 = 2;
x_310 = lean_box(x_309);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_7);
return x_311;
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Meta_isLevelDefEqAuxImpl___spec__3___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = l_instInhabitedBool;
x_3 = lean_box(x_2);
x_4 = l_instInhabited___rarg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_isLevelDefEqAuxImpl___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_Lean_Meta_isLevelDefEqAuxImpl___spec__3___closed__1;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.MetavarContext", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.isLevelMVarAssignable", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown universe metavariable", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__1;
x_2 = l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__2;
x_3 = lean_unsigned_to_nat(365u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
x_15 = l_Std_PersistentHashMap_find_x3f___at_Lean_isLevelMVarAssignable___spec__1(x_14, x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_free_object(x_9);
x_16 = l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__4;
x_17 = l_panic___at_Lean_Meta_isLevelDefEqAuxImpl___spec__3(x_16, x_2, x_3, x_4, x_5, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_nat_dec_eq(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
x_21 = lean_box(x_20);
lean_ctor_set(x_9, 0, x_21);
return x_9;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
x_26 = l_Std_PersistentHashMap_find_x3f___at_Lean_isLevelMVarAssignable___spec__1(x_25, x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
x_27 = l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__4;
x_28 = l_panic___at_Lean_Meta_isLevelDefEqAuxImpl___spec__3(x_27, x_2, x_3, x_4, x_5, x_23);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_nat_dec_eq(x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_23);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at_Lean_Meta_isLevelDefEqAuxImpl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Level_hasMVar(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
case 2:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lean_Level_hasMVar(x_12);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = l_Lean_Level_hasMVar(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
else
{
x_1 = x_13;
goto _start;
}
}
else
{
lean_object* x_19; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_hasAssignableLevelMVar___at_Lean_Meta_isLevelDefEqAuxImpl___spec__1(x_12, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_20);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_ctor_get(x_19, 0);
lean_dec(x_24);
x_25 = l_Lean_Level_hasMVar(x_13);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_box(x_25);
lean_ctor_set(x_19, 0, x_26);
return x_19;
}
else
{
lean_free_object(x_19);
x_1 = x_13;
x_6 = x_23;
goto _start;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = l_Lean_Level_hasMVar(x_13);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
else
{
x_1 = x_13;
x_6 = x_28;
goto _start;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_19, 0);
lean_dec(x_34);
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_dec(x_19);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_19);
if (x_37 == 0)
{
return x_19;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_19, 0);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_19);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
case 3:
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
lean_dec(x_1);
x_43 = l_Lean_Level_hasMVar(x_41);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_41);
x_44 = l_Lean_Level_hasMVar(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = lean_box(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_6);
return x_46;
}
else
{
x_1 = x_42;
goto _start;
}
}
else
{
lean_object* x_48; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_48 = l_Lean_hasAssignableLevelMVar___at_Lean_Meta_isLevelDefEqAuxImpl___spec__1(x_41, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
if (x_50 == 0)
{
uint8_t x_51; 
lean_dec(x_49);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_48, 1);
x_53 = lean_ctor_get(x_48, 0);
lean_dec(x_53);
x_54 = l_Lean_Level_hasMVar(x_42);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = lean_box(x_54);
lean_ctor_set(x_48, 0, x_55);
return x_48;
}
else
{
lean_free_object(x_48);
x_1 = x_42;
x_6 = x_52;
goto _start;
}
}
else
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
lean_dec(x_48);
x_58 = l_Lean_Level_hasMVar(x_42);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = lean_box(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
else
{
x_1 = x_42;
x_6 = x_57;
goto _start;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_48);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_48, 0);
lean_dec(x_63);
return x_48;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_48, 1);
lean_inc(x_64);
lean_dec(x_48);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_49);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_48);
if (x_66 == 0)
{
return x_48;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_48, 0);
x_68 = lean_ctor_get(x_48, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_48);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
case 5:
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_1, 0);
lean_inc(x_70);
lean_dec(x_1);
x_71 = l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2(x_70, x_2, x_3, x_4, x_5, x_6);
return x_71;
}
default: 
{
uint8_t x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = 0;
x_73 = lean_box(x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_6);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Meta_isLevelDefEqAuxImpl___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Meta_isLevelDefEqAuxImpl___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Meta_isLevelDefEqAuxImpl___spec__4___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_isLevelDefEqAuxImpl___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_9 = l_Lean_exceptBoolEmoji___rarg(x_3);
x_10 = l_Lean_stringToMessageData(x_9);
lean_dec(x_9);
x_11 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Meta_isLevelDefEqAuxImpl___lambda__1___closed__2;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__10;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_2);
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_11);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_8);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_throwIsDefEqStuck___rarg(x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_isLevelDefEqAuxImpl___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAuxImpl___lambda__2___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_inc(x_1);
x_9 = l_Lean_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Level_normalize(x_10);
lean_inc(x_2);
x_13 = l_Lean_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1(x_2, x_4, x_5, x_6, x_7, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Level_normalize(x_14);
x_17 = lean_level_eq(x_1, x_12);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_is_level_def_eq(x_12, x_16, x_4, x_5, x_6, x_7, x_15);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_level_eq(x_2, x_16);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_is_level_def_eq(x_12, x_16, x_4, x_5, x_6, x_7, x_15);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_1, x_2, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = 2;
x_26 = lean_unbox(x_23);
x_27 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_15_(x_26, x_25);
if (x_27 == 0)
{
uint8_t x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = 1;
x_29 = lean_unbox(x_23);
lean_dec(x_23);
x_30 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_15_(x_29, x_28);
x_31 = lean_box(x_30);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
else
{
lean_object* x_32; 
lean_free_object(x_21);
lean_dec(x_23);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_2);
x_32 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_1, x_4, x_5, x_6, x_7, x_24);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_36 = lean_unbox(x_33);
x_37 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_15_(x_36, x_25);
if (x_37 == 0)
{
uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = 1;
x_39 = lean_unbox(x_33);
lean_dec(x_33);
x_40 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_15_(x_39, x_38);
x_41 = lean_box(x_40);
if (lean_is_scalar(x_35)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_35;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_34);
return x_42;
}
else
{
uint8_t x_43; lean_object* x_44; lean_object* x_90; 
lean_dec(x_33);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_90 = l_Lean_hasAssignableLevelMVar___at_Lean_Meta_isLevelDefEqAuxImpl___spec__1(x_1, x_4, x_5, x_6, x_7, x_34);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_unbox(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_91);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_94 = l_Lean_hasAssignableLevelMVar___at_Lean_Meta_isLevelDefEqAuxImpl___spec__1(x_2, x_4, x_5, x_6, x_7, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_unbox(x_95);
lean_dec(x_95);
x_43 = x_97;
x_44 = x_96;
goto block_89;
}
else
{
uint8_t x_98; 
lean_dec(x_35);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_94);
if (x_98 == 0)
{
return x_94;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_94, 0);
x_100 = lean_ctor_get(x_94, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_94);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_90, 1);
lean_inc(x_102);
lean_dec(x_90);
x_103 = lean_unbox(x_91);
lean_dec(x_91);
x_43 = x_103;
x_44 = x_102;
goto block_89;
}
}
else
{
uint8_t x_104; 
lean_dec(x_35);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_90);
if (x_104 == 0)
{
return x_90;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_90, 0);
x_106 = lean_ctor_get(x_90, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_90);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
block_89:
{
if (x_43 == 0)
{
lean_object* x_45; lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_4, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_68, 4);
lean_dec(x_68);
if (x_69 == 0)
{
uint8_t x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = 0;
x_71 = lean_box(x_70);
if (lean_is_scalar(x_35)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_35;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_44);
return x_72;
}
else
{
uint8_t x_73; 
x_73 = l_Lean_Level_isMVar(x_1);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = l_Lean_Level_isMVar(x_2);
if (x_74 == 0)
{
uint8_t x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = 0;
x_76 = lean_box(x_75);
if (lean_is_scalar(x_35)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_35;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_44);
return x_77;
}
else
{
lean_object* x_78; 
lean_dec(x_35);
x_78 = lean_box(0);
x_45 = x_78;
goto block_67;
}
}
else
{
lean_object* x_79; 
lean_dec(x_35);
x_79 = lean_box(0);
x_45 = x_79;
goto block_67;
}
}
block_67:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_45);
x_46 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_47 = l_Lean_Name_str___override(x_3, x_46);
lean_inc(x_47);
x_48 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_47, x_4, x_5, x_6, x_7, x_44);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Meta_isLevelDefEqAuxImpl___lambda__3___closed__1;
x_52 = lean_unbox(x_49);
lean_dec(x_49);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_47);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_box(0);
x_54 = lean_apply_6(x_51, x_53, x_4, x_5, x_6, x_7, x_50);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_1);
x_56 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__10;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_2);
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_56);
x_63 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_47, x_62, x_4, x_5, x_6, x_7, x_50);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_apply_6(x_51, x_64, x_4, x_5, x_6, x_7, x_65);
return x_66;
}
}
}
else
{
lean_object* x_80; uint8_t x_81; 
lean_dec(x_35);
lean_dec(x_3);
x_80 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_4, x_5, x_6, x_7, x_44);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_80, 0);
lean_dec(x_82);
x_83 = 1;
x_84 = lean_box(x_83);
lean_ctor_set(x_80, 0, x_84);
return x_80;
}
else
{
lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_80, 1);
lean_inc(x_85);
lean_dec(x_80);
x_86 = 1;
x_87 = lean_box(x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
}
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_32);
if (x_108 == 0)
{
return x_32;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_32, 0);
x_110 = lean_ctor_get(x_32, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_32);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; 
x_112 = lean_ctor_get(x_21, 0);
x_113 = lean_ctor_get(x_21, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_21);
x_114 = 2;
x_115 = lean_unbox(x_112);
x_116 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_15_(x_115, x_114);
if (x_116 == 0)
{
uint8_t x_117; uint8_t x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_117 = 1;
x_118 = lean_unbox(x_112);
lean_dec(x_112);
x_119 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_15_(x_118, x_117);
x_120 = lean_box(x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_113);
return x_121;
}
else
{
lean_object* x_122; 
lean_dec(x_112);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_2);
x_122 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_1, x_4, x_5, x_6, x_7, x_113);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_127; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
x_126 = lean_unbox(x_123);
x_127 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_15_(x_126, x_114);
if (x_127 == 0)
{
uint8_t x_128; uint8_t x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = 1;
x_129 = lean_unbox(x_123);
lean_dec(x_123);
x_130 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_15_(x_129, x_128);
x_131 = lean_box(x_130);
if (lean_is_scalar(x_125)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_125;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_124);
return x_132;
}
else
{
uint8_t x_133; lean_object* x_134; lean_object* x_177; 
lean_dec(x_123);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_177 = l_Lean_hasAssignableLevelMVar___at_Lean_Meta_isLevelDefEqAuxImpl___spec__1(x_1, x_4, x_5, x_6, x_7, x_124);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; uint8_t x_179; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_unbox(x_178);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_178);
x_180 = lean_ctor_get(x_177, 1);
lean_inc(x_180);
lean_dec(x_177);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_181 = l_Lean_hasAssignableLevelMVar___at_Lean_Meta_isLevelDefEqAuxImpl___spec__1(x_2, x_4, x_5, x_6, x_7, x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_unbox(x_182);
lean_dec(x_182);
x_133 = x_184;
x_134 = x_183;
goto block_176;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_125);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_185 = lean_ctor_get(x_181, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_181, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_187 = x_181;
} else {
 lean_dec_ref(x_181);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
else
{
lean_object* x_189; uint8_t x_190; 
x_189 = lean_ctor_get(x_177, 1);
lean_inc(x_189);
lean_dec(x_177);
x_190 = lean_unbox(x_178);
lean_dec(x_178);
x_133 = x_190;
x_134 = x_189;
goto block_176;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_125);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_191 = lean_ctor_get(x_177, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_177, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_193 = x_177;
} else {
 lean_dec_ref(x_177);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
block_176:
{
if (x_133 == 0)
{
lean_object* x_135; lean_object* x_158; uint8_t x_159; 
x_158 = lean_ctor_get(x_4, 0);
lean_inc(x_158);
x_159 = lean_ctor_get_uint8(x_158, 4);
lean_dec(x_158);
if (x_159 == 0)
{
uint8_t x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_160 = 0;
x_161 = lean_box(x_160);
if (lean_is_scalar(x_125)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_125;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_134);
return x_162;
}
else
{
uint8_t x_163; 
x_163 = l_Lean_Level_isMVar(x_1);
if (x_163 == 0)
{
uint8_t x_164; 
x_164 = l_Lean_Level_isMVar(x_2);
if (x_164 == 0)
{
uint8_t x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_165 = 0;
x_166 = lean_box(x_165);
if (lean_is_scalar(x_125)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_125;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_134);
return x_167;
}
else
{
lean_object* x_168; 
lean_dec(x_125);
x_168 = lean_box(0);
x_135 = x_168;
goto block_157;
}
}
else
{
lean_object* x_169; 
lean_dec(x_125);
x_169 = lean_box(0);
x_135 = x_169;
goto block_157;
}
}
block_157:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
lean_dec(x_135);
x_136 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5;
x_137 = l_Lean_Name_str___override(x_3, x_136);
lean_inc(x_137);
x_138 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_137, x_4, x_5, x_6, x_7, x_134);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = l_Lean_Meta_isLevelDefEqAuxImpl___lambda__3___closed__1;
x_142 = lean_unbox(x_139);
lean_dec(x_139);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_137);
lean_dec(x_2);
lean_dec(x_1);
x_143 = lean_box(0);
x_144 = lean_apply_6(x_141, x_143, x_4, x_5, x_6, x_7, x_140);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_145 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_145, 0, x_1);
x_146 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8;
x_147 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
x_148 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__10;
x_149 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_150, 0, x_2);
x_151 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_146);
x_153 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_137, x_152, x_4, x_5, x_6, x_7, x_140);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_apply_6(x_141, x_154, x_4, x_5, x_6, x_7, x_155);
return x_156;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_125);
lean_dec(x_3);
x_170 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_4, x_5, x_6, x_7, x_134);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_172 = x_170;
} else {
 lean_dec_ref(x_170);
 x_172 = lean_box(0);
}
x_173 = 1;
x_174 = lean_box(x_173);
if (lean_is_scalar(x_172)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_172;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_171);
return x_175;
}
}
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_195 = lean_ctor_get(x_122, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_122, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_197 = x_122;
} else {
 lean_dec_ref(x_122);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_199 = !lean_is_exclusive(x_21);
if (x_199 == 0)
{
return x_21;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_21, 0);
x_201 = lean_ctor_get(x_21, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_21);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_is_level_def_eq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_is_level_def_eq(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_2);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAuxImpl___lambda__1___boxed), 8, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
x_12 = l_Lean_Level_getLevelOffset(x_1);
x_13 = l_Lean_Level_getLevelOffset(x_2);
x_14 = lean_level_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_15 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAuxImpl___lambda__3), 8, 3);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_15);
x_17 = 1;
x_18 = l_Lean_withTraceNode___at_Lean_Meta_processPostponed___spec__1(x_15, x_11, x_16, x_17, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Level_getOffsetAux(x_1, x_19);
lean_dec(x_1);
x_21 = l_Lean_Level_getOffsetAux(x_2, x_19);
lean_dec(x_2);
x_22 = lean_nat_dec_eq(x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
x_23 = lean_box(x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Meta_isLevelDefEqAuxImpl___spec__4___rarg___boxed), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_26 = 1;
x_27 = l_Lean_withTraceNode___at_Lean_Meta_processPostponed___spec__1(x_25, x_11, x_24, x_26, x_3, x_4, x_5, x_6, x_7);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_inc(x_2);
lean_inc(x_1);
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAuxImpl___lambda__1___boxed), 8, 2);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_2);
x_29 = l_Lean_Level_getLevelOffset(x_1);
x_30 = l_Lean_Level_getLevelOffset(x_2);
x_31 = lean_level_eq(x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_32 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_33 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAuxImpl___lambda__3), 8, 3);
lean_closure_set(x_33, 0, x_1);
lean_closure_set(x_33, 1, x_2);
lean_closure_set(x_33, 2, x_32);
x_34 = 1;
x_35 = l_Lean_withTraceNode___at_Lean_Meta_processPostponed___spec__1(x_32, x_28, x_33, x_34, x_3, x_4, x_5, x_6, x_7);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Lean_Level_getOffsetAux(x_1, x_36);
lean_dec(x_1);
x_38 = l_Lean_Level_getOffsetAux(x_2, x_36);
lean_dec(x_2);
x_39 = lean_nat_dec_eq(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
x_40 = lean_box(x_39);
x_41 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Meta_isLevelDefEqAuxImpl___spec__4___rarg___boxed), 6, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_43 = 1;
x_44 = l_Lean_withTraceNode___at_Lean_Meta_processPostponed___spec__1(x_42, x_28, x_41, x_43, x_3, x_4, x_5, x_6, x_7);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Meta_isLevelDefEqAuxImpl___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_ReaderT_pure___at_Lean_Meta_isLevelDefEqAuxImpl___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_isLevelDefEqAuxImpl___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isLevelDefEqAuxImpl___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_LevelDefEq___hyg_1333_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4;
x_3 = 0;
x_4 = l_Lean_registerTraceClass(x_2, x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__6;
x_7 = 1;
x_8 = l_Lean_registerTraceClass(x_6, x_7, x_5);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_CollectMVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_DecLevel(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_LevelDefEq(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectMVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DecLevel(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_panic___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___spec__1___closed__1 = _init_l_panic___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___spec__1___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___spec__1___closed__1);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__2);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__3);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__4);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__5);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__6 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__6();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__6);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__1);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__2);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__3);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__4);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__5);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__6 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__6();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__6);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__7 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__7();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__7);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__8);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__9 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__9();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__9);
l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__10 = _init_l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__10();
lean_mark_persistent(l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___closed__10);
l_panic___at_Lean_Meta_isLevelDefEqAuxImpl___spec__3___closed__1 = _init_l_panic___at_Lean_Meta_isLevelDefEqAuxImpl___spec__3___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_isLevelDefEqAuxImpl___spec__3___closed__1);
l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__1 = _init_l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__1();
lean_mark_persistent(l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__1);
l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__2 = _init_l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__2();
lean_mark_persistent(l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__2);
l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__3 = _init_l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__3();
lean_mark_persistent(l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__3);
l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__4 = _init_l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__4();
lean_mark_persistent(l_Lean_isLevelMVarAssignable___at_Lean_Meta_isLevelDefEqAuxImpl___spec__2___closed__4);
l_Lean_Meta_isLevelDefEqAuxImpl___lambda__1___closed__1 = _init_l_Lean_Meta_isLevelDefEqAuxImpl___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_isLevelDefEqAuxImpl___lambda__1___closed__1);
l_Lean_Meta_isLevelDefEqAuxImpl___lambda__1___closed__2 = _init_l_Lean_Meta_isLevelDefEqAuxImpl___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_isLevelDefEqAuxImpl___lambda__1___closed__2);
l_Lean_Meta_isLevelDefEqAuxImpl___lambda__3___closed__1 = _init_l_Lean_Meta_isLevelDefEqAuxImpl___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_isLevelDefEqAuxImpl___lambda__3___closed__1);
res = l_Lean_Meta_initFn____x40_Lean_Meta_LevelDefEq___hyg_1333_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
