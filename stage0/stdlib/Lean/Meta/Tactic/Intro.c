// Lean compiler output
// Module: Lean.Meta.Tactic.Intro
// Imports: Init Lean.Meta.Tactic.Util
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
lean_object* l_Lean_Meta_withNewLocalInstances___at_Lean_Meta_introNCore___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534____closed__1;
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop_match__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_intro1Core___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534____closed__2;
lean_object* lean_local_ctx_get_unused_name(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__4;
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Meta_hygienicIntroDefault;
lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_ReaderT_bind___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getHygienicIntro___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getHygienicIntro___rarg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_getHygienicIntro___rarg___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at_Lean_Meta_introNCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getHygienicIntro___rarg___closed__2;
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_Name_inhabited;
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop_match__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at_Lean_Meta_introNCore___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___lambda__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg___closed__2;
lean_object* l_Lean_Meta_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__5;
lean_object* l_Lean_Meta_intro_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp(lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534_(lean_object*);
lean_object* l_Lean_Meta_intro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_match__1___rarg(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__4;
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__2;
lean_object* l_Lean_Meta_introNCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__2;
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop_match__1___rarg(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__1;
lean_object* l_Lean_Meta_intro1P(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__3;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_1__mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkSimpleThunk___closed__1;
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__3;
lean_object* l_Lean_Meta_assignExprMVar___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_match__1(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534____closed__3;
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___at_Lean_Meta_introNCore___spec__2(lean_object*);
lean_object* l_Lean_Meta_intro_match__1(lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__5;
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at_Lean_Meta_introNCore___spec__1___lambda__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getHygienicIntro___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at_Lean_Meta_withNewLocalInstances___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getHygienicIntro(lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop_match__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop_match__3(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_match__1(lean_object*);
lean_object* l_Lean_Meta_intro1Core_match__1(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at_Lean_Meta_introNCore___spec__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at_Lean_Meta_introNCore___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534____closed__4;
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at_Lean_Meta_introNCore___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop_match__1___rarg), 2, 0);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop_match__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop_match__2___rarg), 2, 0);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_1, x_13);
switch (lean_obj_tag(x_6)) {
case 7:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_8);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 2);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
lean_dec(x_6);
x_19 = lean_box_uint64(x_18);
x_20 = lean_apply_9(x_9, x_14, x_2, x_3, x_4, x_5, x_15, x_16, x_17, x_19);
return x_20;
}
case 8:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_10);
lean_dec(x_9);
x_21 = lean_ctor_get(x_6, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_6, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_6, 3);
lean_inc(x_24);
x_25 = lean_ctor_get_uint64(x_6, sizeof(void*)*4);
lean_dec(x_6);
x_26 = lean_box_uint64(x_25);
x_27 = lean_apply_10(x_8, x_14, x_2, x_3, x_4, x_5, x_21, x_22, x_23, x_24, x_26);
return x_27;
}
default: 
{
lean_object* x_28; 
lean_dec(x_9);
lean_dec(x_8);
x_28 = lean_apply_6(x_10, x_14, x_2, x_3, x_4, x_5, x_6);
return x_28;
}
}
}
else
{
lean_object* x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_29 = lean_apply_5(x_7, x_2, x_3, x_4, x_5, x_6);
return x_29;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop_match__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop_match__3___rarg___boxed), 10, 0);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop_match__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop_match__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_match__1___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("introN");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("insufficient number of binders");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = l_Lean_Expr_isForall(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__2;
x_16 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__5;
x_17 = lean_box(0);
x_18 = l_Lean_Meta_throwTacticEx___rarg(x_15, x_1, x_16, x_17, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
x_21 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg(x_1, x_3, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_21;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_Lean_Expr_headBeta(x_1);
lean_inc(x_5);
x_11 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_10, x_4, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__4;
lean_inc(x_12);
lean_inc(x_2);
x_15 = l_Lean_Meta_mkLambdaFVars___rarg(x_14, x_2, x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = lean_apply_5(x_15, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_assignExprMVar___rarg(x_14, x_3, x_17);
x_20 = lean_apply_5(x_19, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = l_Lean_Expr_mvarId_x21(x_12);
lean_dec(x_12);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = l_Lean_Expr_mvarId_x21(x_12);
lean_dec(x_12);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_12);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_20);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_3, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_3, x_16);
lean_dec(x_3);
switch (lean_obj_tag(x_8)) {
case 7:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_8, 2);
lean_inc(x_20);
x_21 = lean_ctor_get_uint64(x_8, sizeof(void*)*3);
lean_dec(x_8);
x_22 = lean_array_get_size(x_5);
x_23 = lean_expr_instantiate_rev_range(x_19, x_6, x_22, x_5);
lean_dec(x_22);
lean_dec(x_19);
x_24 = l_Lean_Expr_headBeta(x_23);
x_25 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__3;
x_26 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg___closed__2;
x_27 = l_Lean_mkFreshId___rarg(x_25, x_26);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_28 = lean_apply_5(x_27, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_31 = lean_apply_8(x_2, x_4, x_18, x_7, x_9, x_10, x_11, x_12, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = (uint8_t)((x_21 << 24) >> 61);
lean_inc(x_29);
x_37 = lean_local_ctx_mk_local_decl(x_4, x_29, x_34, x_24, x_36);
x_38 = l_Lean_mkFVar(x_29);
x_39 = lean_array_push(x_5, x_38);
x_3 = x_17;
x_4 = x_37;
x_5 = x_39;
x_7 = x_35;
x_8 = x_20;
x_13 = x_33;
goto _start;
}
else
{
uint8_t x_41; 
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_31);
if (x_41 == 0)
{
return x_31;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_31, 0);
x_43 = lean_ctor_get(x_31, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_31);
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
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_28);
if (x_45 == 0)
{
return x_28;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_28, 0);
x_47 = lean_ctor_get(x_28, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_28);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
case 8:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_49 = lean_ctor_get(x_8, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_8, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_8, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_8, 3);
lean_inc(x_52);
lean_dec(x_8);
x_53 = lean_array_get_size(x_5);
x_54 = lean_expr_instantiate_rev_range(x_50, x_6, x_53, x_5);
lean_dec(x_50);
x_55 = l_Lean_Expr_headBeta(x_54);
x_56 = lean_expr_instantiate_rev_range(x_51, x_6, x_53, x_5);
lean_dec(x_53);
lean_dec(x_51);
x_57 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__3;
x_58 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___rarg___closed__2;
x_59 = l_Lean_mkFreshId___rarg(x_57, x_58);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_60 = lean_apply_5(x_59, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_63 = lean_apply_8(x_2, x_4, x_49, x_7, x_9, x_10, x_11, x_12, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = 0;
lean_inc(x_61);
x_69 = lean_local_ctx_mk_let_decl(x_4, x_61, x_66, x_55, x_56, x_68);
x_70 = l_Lean_mkFVar(x_61);
x_71 = lean_array_push(x_5, x_70);
x_3 = x_17;
x_4 = x_69;
x_5 = x_71;
x_7 = x_67;
x_8 = x_52;
x_13 = x_65;
goto _start;
}
else
{
uint8_t x_73; 
lean_dec(x_61);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_63);
if (x_73 == 0)
{
return x_63;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_63, 0);
x_75 = lean_ctor_get(x_63, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_63);
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
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_60);
if (x_77 == 0)
{
return x_60;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_60, 0);
x_79 = lean_ctor_get(x_60, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_60);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
default: 
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_81 = lean_array_get_size(x_5);
x_82 = lean_expr_instantiate_rev_range(x_8, x_6, x_81, x_5);
lean_dec(x_8);
x_83 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__4;
x_84 = l_Lean_Meta_whnf___rarg(x_83, x_82);
lean_inc(x_5);
lean_inc(x_4);
x_85 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___boxed), 13, 7);
lean_closure_set(x_85, 0, x_1);
lean_closure_set(x_85, 1, x_17);
lean_closure_set(x_85, 2, x_2);
lean_closure_set(x_85, 3, x_4);
lean_closure_set(x_85, 4, x_5);
lean_closure_set(x_85, 5, x_81);
lean_closure_set(x_85, 6, x_7);
x_86 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__2;
x_87 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_87, 0, x_86);
lean_closure_set(x_87, 1, lean_box(0));
lean_closure_set(x_87, 2, lean_box(0));
lean_closure_set(x_87, 3, x_84);
lean_closure_set(x_87, 4, x_85);
x_88 = !lean_is_exclusive(x_9);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_9, 1);
lean_dec(x_89);
lean_ctor_set(x_9, 1, x_4);
x_90 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__5;
x_91 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__3;
x_92 = l_Lean_Meta_withNewLocalInstances___rarg(x_90, x_91, lean_box(0), x_5, x_6, x_87);
x_93 = lean_apply_5(x_92, x_9, x_10, x_11, x_12, x_13);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_94 = lean_ctor_get(x_9, 0);
x_95 = lean_ctor_get(x_9, 2);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_9);
x_96 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_4);
lean_ctor_set(x_96, 2, x_95);
x_97 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__5;
x_98 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__3;
x_99 = l_Lean_Meta_withNewLocalInstances___rarg(x_97, x_98, lean_box(0), x_5, x_6, x_87);
x_100 = lean_apply_5(x_99, x_96, x_10, x_11, x_12, x_13);
return x_100;
}
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_101 = lean_array_get_size(x_5);
x_102 = lean_expr_instantiate_rev_range(x_8, x_6, x_101, x_5);
lean_dec(x_101);
lean_dec(x_8);
lean_inc(x_1);
x_103 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarTag___boxed), 6, 1);
lean_closure_set(x_103, 0, x_1);
lean_inc(x_5);
x_104 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2), 9, 3);
lean_closure_set(x_104, 0, x_102);
lean_closure_set(x_104, 1, x_5);
lean_closure_set(x_104, 2, x_1);
x_105 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__2;
x_106 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_106, 0, x_105);
lean_closure_set(x_106, 1, lean_box(0));
lean_closure_set(x_106, 2, lean_box(0));
lean_closure_set(x_106, 3, x_103);
lean_closure_set(x_106, 4, x_104);
x_107 = !lean_is_exclusive(x_9);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_ctor_get(x_9, 1);
lean_dec(x_108);
lean_ctor_set(x_9, 1, x_4);
x_109 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__5;
x_110 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__3;
x_111 = l_Lean_Meta_withNewLocalInstances___rarg(x_109, x_110, lean_box(0), x_5, x_6, x_106);
x_112 = lean_apply_5(x_111, x_9, x_10, x_11, x_12, x_13);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_113 = lean_ctor_get(x_9, 0);
x_114 = lean_ctor_get(x_9, 2);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_9);
x_115 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_4);
lean_ctor_set(x_115, 2, x_114);
x_116 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__5;
x_117 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__3;
x_118 = l_Lean_Meta_withNewLocalInstances___rarg(x_116, x_117, lean_box(0), x_5, x_6, x_106);
x_119 = lean_apply_5(x_118, x_115, x_10, x_11, x_12, x_13);
return x_119;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg), 13, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_14;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = x_6;
x_10 = l_Lean_Expr_fvarId_x21(x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = x_10;
x_14 = lean_array_fset(x_8, x_1, x_13);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_Meta_getMVarType(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
x_15 = l_Array_empty___closed__1;
x_16 = lean_unsigned_to_nat(0u);
x_17 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg(x_1, x_2, x_3, x_14, x_15, x_16, x_4, x_12, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = x_21;
x_23 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1(x_16, x_22);
x_24 = x_23;
lean_ctor_set(x_19, 0, x_24);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = x_25;
x_28 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1(x_16, x_27);
x_29 = x_28;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_17, 0, x_30);
return x_17;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_35 = x_31;
} else {
 lean_dec_ref(x_31);
 x_35 = lean_box(0);
}
x_36 = x_33;
x_37 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1(x_16, x_36);
x_38 = x_37;
if (lean_is_scalar(x_35)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_35;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_17);
if (x_41 == 0)
{
return x_17;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_17, 0);
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_17);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_11);
if (x_45 == 0)
{
return x_11;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_11, 0);
x_47 = lean_ctor_get(x_11, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_11);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__2;
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 7, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg___lambda__1___boxed), 10, 4);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_4);
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg), 7, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1, x_13, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg), 9, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
static uint8_t _init_l_Lean_Meta_hygienicIntroDefault() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getHygienicIntro___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hygienicIntro");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getHygienicIntro___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_getHygienicIntro___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_getHygienicIntro___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_Meta_getHygienicIntro___rarg___closed__2;
x_6 = l_Lean_Meta_hygienicIntroDefault;
x_7 = l_Lean_KVMap_getBool(x_4, x_5, x_6);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
lean_object* l_Lean_Meta_getHygienicIntro(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_getHygienicIntro___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Lean_Meta_getHygienicIntro___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getHygienicIntro___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Meta_getHygienicIntro___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_getHygienicIntro(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534____closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_hygienicIntroDefault;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tactic");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("make sure 'intro'-like tactics are hygienic");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534____closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534____closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_getHygienicIntro___rarg___closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534____closed__4;
x_4 = lean_register_option(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
if (x_1 == 0)
{
if (x_2 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_local_ctx_get_unused_name(x_3, x_4);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_3);
x_15 = l___private_Lean_CoreM_1__mkFreshNameImp(x_4, x_8, x_9, x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_3);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_10);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_47; uint8_t x_48; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_47 = l_Lean_mkSimpleThunk___closed__1;
x_48 = lean_name_eq(x_28, x_47);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = 1;
x_30 = x_49;
goto block_46;
}
else
{
uint8_t x_50; 
x_50 = 0;
x_30 = x_50;
goto block_46;
}
block_46:
{
if (x_30 == 0)
{
if (x_1 == 0)
{
if (x_2 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_local_ctx_get_unused_name(x_3, x_4);
lean_inc(x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_10);
return x_33;
}
else
{
lean_object* x_34; uint8_t x_35; 
lean_dec(x_3);
x_34 = l___private_Lean_CoreM_1__mkFreshNameImp(x_4, x_8, x_9, x_10);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_29);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
lean_inc(x_29);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_29);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_3);
lean_inc(x_29);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_29);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_10);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_29);
lean_inc(x_28);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_28);
lean_ctor_set(x_44, 1, x_29);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_10);
return x_45;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___at_Lean_Meta_introNCore___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at_Lean_Meta_withNewLocalInstances___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___at_Lean_Meta_introNCore___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___at_Lean_Meta_introNCore___spec__2___rarg), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at_Lean_Meta_introNCore___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = l_Lean_Expr_isForall(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_16 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__2;
x_17 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__5;
x_18 = lean_box(0);
x_19 = l_Lean_Meta_throwTacticEx___rarg(x_16, x_1, x_17, x_18, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
x_22 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at_Lean_Meta_introNCore___spec__1(x_3, x_4, x_1, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_22;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at_Lean_Meta_introNCore___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_Expr_headBeta(x_1);
lean_inc(x_5);
x_11 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_10, x_4, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_5);
lean_inc(x_12);
lean_inc(x_2);
x_14 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_2, x_12, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__3(x_3, x_15, x_5, x_6, x_7, x_8, x_16);
lean_dec(x_5);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = l_Lean_Expr_mvarId_x21(x_12);
lean_dec(x_12);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = l_Lean_Expr_mvarId_x21(x_12);
lean_dec(x_12);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at_Lean_Meta_introNCore___spec__1(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_4, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_4, x_17);
lean_dec(x_4);
switch (lean_obj_tag(x_9)) {
case 7:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_9, 2);
lean_inc(x_21);
x_22 = lean_ctor_get_uint64(x_9, sizeof(void*)*3);
lean_dec(x_9);
x_23 = lean_array_get_size(x_6);
x_24 = lean_expr_instantiate_rev_range(x_20, x_7, x_23, x_6);
lean_dec(x_23);
lean_dec(x_20);
x_25 = l_Lean_Expr_headBeta(x_24);
x_26 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_13, x_14);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_5);
x_29 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(x_1, x_2, x_5, x_19, x_8, x_10, x_11, x_12, x_13, x_28);
lean_dec(x_8);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = (uint8_t)((x_22 << 24) >> 61);
lean_inc(x_27);
x_35 = lean_local_ctx_mk_local_decl(x_5, x_27, x_32, x_25, x_34);
x_36 = l_Lean_mkFVar(x_27);
x_37 = lean_array_push(x_6, x_36);
x_4 = x_18;
x_5 = x_35;
x_6 = x_37;
x_8 = x_33;
x_9 = x_21;
x_14 = x_31;
goto _start;
}
case 8:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_39 = lean_ctor_get(x_9, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_9, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_9, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_9, 3);
lean_inc(x_42);
lean_dec(x_9);
x_43 = lean_array_get_size(x_6);
x_44 = lean_expr_instantiate_rev_range(x_40, x_7, x_43, x_6);
lean_dec(x_40);
x_45 = l_Lean_Expr_headBeta(x_44);
x_46 = lean_expr_instantiate_rev_range(x_41, x_7, x_43, x_6);
lean_dec(x_43);
lean_dec(x_41);
x_47 = l_Lean_mkFreshId___at_Lean_Meta_mkFreshExprMVarAt___spec__1___rarg(x_13, x_14);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_5);
x_50 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(x_1, x_2, x_5, x_39, x_8, x_10, x_11, x_12, x_13, x_49);
lean_dec(x_8);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = 0;
lean_inc(x_48);
x_56 = lean_local_ctx_mk_let_decl(x_5, x_48, x_53, x_45, x_46, x_55);
x_57 = l_Lean_mkFVar(x_48);
x_58 = lean_array_push(x_6, x_57);
x_4 = x_18;
x_5 = x_56;
x_6 = x_58;
x_8 = x_54;
x_9 = x_42;
x_14 = x_52;
goto _start;
}
default: 
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_60 = lean_array_get_size(x_6);
x_61 = lean_expr_instantiate_rev_range(x_9, x_7, x_60, x_6);
lean_dec(x_9);
x_62 = lean_alloc_closure((void*)(l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2), 6, 1);
lean_closure_set(x_62, 0, x_61);
x_63 = lean_box(x_1);
x_64 = lean_box(x_2);
lean_inc(x_6);
lean_inc(x_5);
x_65 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at_Lean_Meta_introNCore___spec__1___lambda__1___boxed), 14, 8);
lean_closure_set(x_65, 0, x_3);
lean_closure_set(x_65, 1, x_18);
lean_closure_set(x_65, 2, x_63);
lean_closure_set(x_65, 3, x_64);
lean_closure_set(x_65, 4, x_5);
lean_closure_set(x_65, 5, x_6);
lean_closure_set(x_65, 6, x_60);
lean_closure_set(x_65, 7, x_8);
x_66 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg), 7, 2);
lean_closure_set(x_66, 0, x_62);
lean_closure_set(x_66, 1, x_65);
x_67 = !lean_is_exclusive(x_10);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_10, 1);
lean_dec(x_68);
lean_ctor_set(x_10, 1, x_5);
x_69 = l_Lean_Meta_withNewLocalInstances___at_Lean_Meta_introNCore___spec__2___rarg(x_6, x_7, x_66, x_10, x_11, x_12, x_13, x_14);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_10, 0);
x_71 = lean_ctor_get(x_10, 2);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_10);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_5);
lean_ctor_set(x_72, 2, x_71);
x_73 = l_Lean_Meta_withNewLocalInstances___at_Lean_Meta_introNCore___spec__2___rarg(x_6, x_7, x_66, x_72, x_11, x_12, x_13, x_14);
return x_73;
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_8);
lean_dec(x_4);
x_74 = lean_array_get_size(x_6);
x_75 = lean_expr_instantiate_rev_range(x_9, x_7, x_74, x_6);
lean_dec(x_74);
lean_dec(x_9);
lean_inc(x_3);
x_76 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarTag___boxed), 6, 1);
lean_closure_set(x_76, 0, x_3);
lean_inc(x_6);
x_77 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at_Lean_Meta_introNCore___spec__1___lambda__2___boxed), 9, 3);
lean_closure_set(x_77, 0, x_75);
lean_closure_set(x_77, 1, x_6);
lean_closure_set(x_77, 2, x_3);
x_78 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg), 7, 2);
lean_closure_set(x_78, 0, x_76);
lean_closure_set(x_78, 1, x_77);
x_79 = !lean_is_exclusive(x_10);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_10, 1);
lean_dec(x_80);
lean_ctor_set(x_10, 1, x_5);
x_81 = l_Lean_Meta_withNewLocalInstances___at_Lean_Meta_introNCore___spec__2___rarg(x_6, x_7, x_78, x_10, x_11, x_12, x_13, x_14);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_10, 0);
x_83 = lean_ctor_get(x_10, 2);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_10);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_5);
lean_ctor_set(x_84, 2, x_83);
x_85 = l_Lean_Meta_withNewLocalInstances___at_Lean_Meta_introNCore___spec__2___rarg(x_6, x_7, x_78, x_84, x_11, x_12, x_13, x_14);
return x_85;
}
}
}
}
lean_object* l_Lean_Meta_introNCore___lambda__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_1);
x_12 = l_Lean_Meta_getMVarType(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
x_16 = l_Array_empty___closed__1;
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at_Lean_Meta_introNCore___spec__1(x_2, x_3, x_1, x_4, x_15, x_16, x_17, x_5, x_13, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = x_22;
x_24 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1(x_17, x_23);
x_25 = x_24;
lean_ctor_set(x_20, 0, x_25);
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = x_26;
x_29 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1(x_17, x_28);
x_30 = x_29;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set(x_18, 0, x_31);
return x_18;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_36 = x_32;
} else {
 lean_dec_ref(x_32);
 x_36 = lean_box(0);
}
x_37 = x_34;
x_38 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1(x_17, x_37);
x_39 = x_38;
if (lean_is_scalar(x_36)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_36;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_33);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_18);
if (x_42 == 0)
{
return x_18;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_18);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_12);
if (x_46 == 0)
{
return x_12;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_12, 0);
x_48 = lean_ctor_get(x_12, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_12);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
lean_object* l_Lean_Meta_introNCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Meta_getHygienicIntro___rarg(x_7, x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_10);
x_16 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__2;
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 7, 2);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_box(x_4);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_introNCore___lambda__1___boxed), 11, 5);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_18);
lean_closure_set(x_19, 2, x_12);
lean_closure_set(x_19, 3, x_2);
lean_closure_set(x_19, 4, x_3);
x_20 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg), 7, 2);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_19);
x_21 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1, x_20, x_5, x_6, x_7, x_8, x_13);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_22 = l_Array_empty___closed__1;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_1);
lean_ctor_set(x_10, 0, x_23);
return x_10;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_eq(x_2, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__2;
lean_inc(x_1);
x_29 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 7, 2);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_28);
x_30 = lean_box(x_4);
lean_inc(x_1);
x_31 = lean_alloc_closure((void*)(l_Lean_Meta_introNCore___lambda__1___boxed), 11, 5);
lean_closure_set(x_31, 0, x_1);
lean_closure_set(x_31, 1, x_30);
lean_closure_set(x_31, 2, x_24);
lean_closure_set(x_31, 3, x_2);
lean_closure_set(x_31, 4, x_3);
x_32 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg), 7, 2);
lean_closure_set(x_32, 0, x_29);
lean_closure_set(x_32, 1, x_31);
x_33 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1, x_32, x_5, x_6, x_7, x_8, x_25);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_34 = l_Array_empty___closed__1;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_25);
return x_36;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at_Lean_Meta_introNCore___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at_Lean_Meta_introNCore___spec__1___lambda__1(x_1, x_2, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
return x_17;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at_Lean_Meta_introNCore___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at_Lean_Meta_introNCore___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at_Lean_Meta_introNCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at_Lean_Meta_introNCore___spec__1(x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
lean_object* l_Lean_Meta_introNCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Meta_introNCore___lambda__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_14;
}
}
lean_object* l_Lean_Meta_introNCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_introNCore(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Meta_introN(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 0;
x_10 = l_Lean_Meta_introNCore(x_1, x_2, x_3, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_introNP(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = 1;
x_10 = l_Lean_Meta_introNCore(x_1, x_2, x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
lean_object* l_Lean_Meta_intro_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_intro_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_intro_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_intro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = 0;
x_12 = l_Lean_Meta_introNCore(x_1, x_10, x_9, x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_Name_inhabited;
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_get(x_17, x_16, x_18);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = l_Lean_Name_inhabited;
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_get(x_22, x_20, x_23);
lean_dec(x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_12, 0, x_25);
return x_12;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_30 = x_26;
} else {
 lean_dec_ref(x_26);
 x_30 = lean_box(0);
}
x_31 = l_Lean_Name_inhabited;
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_array_get(x_31, x_28, x_32);
lean_dec(x_28);
if (lean_is_scalar(x_30)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_30;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_27);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_12);
if (x_36 == 0)
{
return x_12;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_12, 0);
x_38 = lean_ctor_get(x_12, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_12);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
lean_object* l_Lean_Meta_intro1Core_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_intro1Core_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_intro1Core_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_intro1Core(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Meta_introNCore(x_1, x_9, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_Name_inhabited;
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get(x_15, x_14, x_16);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = l_Lean_Name_inhabited;
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get(x_20, x_18, x_21);
lean_dec(x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_10, 0, x_23);
return x_10;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_28 = x_24;
} else {
 lean_dec_ref(x_24);
 x_28 = lean_box(0);
}
x_29 = l_Lean_Name_inhabited;
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_array_get(x_29, x_26, x_30);
lean_dec(x_26);
if (lean_is_scalar(x_28)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_28;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_10);
if (x_34 == 0)
{
return x_10;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_10, 0);
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_10);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l_Lean_Meta_intro1Core___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_intro1Core(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_Meta_intro1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 0;
x_8 = l_Lean_Meta_intro1Core(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_Meta_intro1P(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
x_8 = l_Lean_Meta_intro1Core(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Tactic_Intro(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__2 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__2);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__3 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__3);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__4 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__4);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__5 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__5);
l_Lean_Meta_hygienicIntroDefault = _init_l_Lean_Meta_hygienicIntroDefault();
l_Lean_Meta_getHygienicIntro___rarg___closed__1 = _init_l_Lean_Meta_getHygienicIntro___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_getHygienicIntro___rarg___closed__1);
l_Lean_Meta_getHygienicIntro___rarg___closed__2 = _init_l_Lean_Meta_getHygienicIntro___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_getHygienicIntro___rarg___closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534____closed__4);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_534_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
