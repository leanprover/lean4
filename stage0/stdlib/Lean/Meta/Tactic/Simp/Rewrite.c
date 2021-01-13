// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Rewrite
// Imports: Init Lean.Meta.SynthInstance Lean.Meta.Tactic.Simp.Types
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
lean_object* l_Lean_Meta_mkPropExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_finalizeProof_match__1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_match__4(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_finalizeProof(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__1(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_preDefault___closed__1;
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_postDefault___closed__1;
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_match__2(lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_getLHS(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__4(lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_match__1(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__5(lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__2___closed__1;
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__2(lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_finalizeProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t lean_expr_lt(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__6;
lean_object* l_Lean_Meta_Simp_postDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__4___rarg(lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_match__3(lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_finalizeProof_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_getRHS___closed__6;
lean_object* l_Lean_Meta_Simp_rewrite_getLHS_match__1(lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f_match__1(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__11;
lean_object* l_Lean_Meta_Simp_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_getLHS_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__3;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_getRHS_match__1(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_getRHS_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite___closed__4;
lean_object* l_Lean_Meta_Simp_rewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__10;
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__7;
extern lean_object* l_Lean_Parser_Tactic_rewrite___closed__1;
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__2;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_getRHS_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_getRHS___closed__3;
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__5___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs___closed__1;
lean_object* l_Lean_Meta_mkEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__15;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite___closed__3;
extern lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__8;
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_synthInstance_x3f___lambda__2___closed__8;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_getRHS___closed__2;
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite___closed__1;
lean_object* l_Lean_Meta_Simp_rewrite___closed__2;
lean_object* l_Lean_Meta_Simp_rewrite_match__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_getRHS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_finalizeProof_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_getRHS___closed__1;
lean_object* l_Lean_Meta_Simp_rewrite___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__3(lean_object*, lean_object*);
lean_object* l_Array_insertionSort_swapLoop___at_Lean_Meta_Simp_rewrite___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_hasAssignableMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__5___closed__2;
lean_object* l_Lean_Meta_Simp_rewrite_getRHS___closed__4;
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__3(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__5___closed__3;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__5___closed__1;
lean_object* l_Lean_Meta_Simp_preDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_simp___closed__1;
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__12;
lean_object* l_Lean_Meta_Simp_rewrite_getLHS_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_match__4___rarg(lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__5;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__1;
lean_object* l_Lean_Meta_DiscrTree_getMatch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertionSort_traverse___at_Lean_Meta_Simp_rewrite___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_changeWith___closed__3;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__3;
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpLemma_getValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_getRHS(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_intro___closed__1;
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__4;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__8;
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__2;
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__2;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__1;
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_getRHS___closed__5;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__4(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__9;
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_findSomeM_x3f___rarg___closed__1;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4;
lean_object* l_Lean_Meta_Simp_rewrite_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_getLHS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_fmt___at_Lean_Meta_instToMessageDataSimpLemma___spec__1(lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_getLHS_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_4, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_5, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_2, x_10);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_3, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Meta_Simp_rewrite_getLHS_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_rewrite_getLHS_match__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_getLHS_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Meta_Simp_rewrite_getLHS_match__1___rarg(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_getRHS_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_4, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_5, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_2, x_10);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_3, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Meta_Simp_rewrite_getRHS_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_rewrite_getRHS_match__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_getRHS_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Meta_Simp_rewrite_getRHS_match__1___rarg(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__4___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__4___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_rewrite_synthesizeArgs_match__5___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_finalizeProof_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_4, x_10);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_5, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Meta_Simp_rewrite_finalizeProof_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_rewrite_finalizeProof_match__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_finalizeProof_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Meta_Simp_rewrite_finalizeProof_match__1___rarg(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_rewrite_tryLemma_x3f_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Meta_Simp_rewrite_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_rewrite_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_rewrite_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Meta_Simp_rewrite_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_rewrite_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_match__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_match__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_rewrite_match__4___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_match__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_rewrite_match__4(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_getLHS(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_box(x_1);
switch (lean_obj_tag(x_8)) {
case 2:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
case 3:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
x_12 = l_Lean_Expr_appFn_x21(x_2);
lean_dec(x_2);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
}
}
}
lean_object* l_Lean_Meta_Simp_rewrite_getLHS___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Meta_Simp_rewrite_getLHS(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_getRHS___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("True");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_getRHS___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewrite_getRHS___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_getRHS___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewrite_getRHS___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_getRHS___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("False");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_getRHS___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewrite_getRHS___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_getRHS___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewrite_getRHS___closed__5;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_getRHS(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_box(x_1);
switch (lean_obj_tag(x_8)) {
case 2:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Meta_Simp_rewrite_getRHS___closed__3;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
case 3:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Meta_Simp_rewrite_getRHS___closed__6;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
x_13 = l_Lean_Expr_appArg_x21(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
}
}
}
lean_object* l_Lean_Meta_Simp_rewrite_getRHS___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Meta_Simp_rewrite_getRHS(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_8, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_15, 3);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_12);
lean_inc(x_10);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Std_PersistentArray_push___rarg(x_21, x_23);
lean_ctor_set(x_16, 0, x_24);
x_25 = lean_st_ref_set(x_8, x_15, x_17);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
x_33 = lean_ctor_get(x_16, 0);
lean_inc(x_33);
lean_dec(x_16);
x_34 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_12);
lean_inc(x_10);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_10);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Std_PersistentArray_push___rarg(x_33, x_35);
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_32);
lean_ctor_set(x_15, 3, x_37);
x_38 = lean_st_ref_set(x_8, x_15, x_17);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_43 = lean_ctor_get(x_15, 0);
x_44 = lean_ctor_get(x_15, 1);
x_45 = lean_ctor_get(x_15, 2);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_15);
x_46 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
x_47 = lean_ctor_get(x_16, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_48 = x_16;
} else {
 lean_dec_ref(x_16);
 x_48 = lean_box(0);
}
x_49 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_12);
lean_inc(x_10);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_10);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Std_PersistentArray_push___rarg(x_47, x_50);
if (lean_is_scalar(x_48)) {
 x_52 = lean_alloc_ctor(0, 1, 1);
} else {
 x_52 = x_48;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_46);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_43);
lean_ctor_set(x_53, 1, x_44);
lean_ctor_set(x_53, 2, x_45);
lean_ctor_set(x_53, 3, x_52);
x_54 = lean_st_ref_set(x_8, x_53, x_17);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_Lean_checkTraceOption(x_9, x_1);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__2;
x_2 = l_Lean_Parser_Tactic_intro___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__1;
x_2 = l_Lean_Parser_Tactic_simp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("discharge");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__2;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", failed to discharge hypotheses");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", failed to assign proof");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", failed to synthesize instance");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", failed to assign instance");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_33; 
x_33 = x_6 < x_5;
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_14);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_35 = lean_array_uget(x_4, x_6);
x_36 = lean_ctor_get(x_7, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_37 = x_7;
} else {
 lean_dec_ref(x_7);
 x_37 = lean_box(0);
}
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_36, 2);
lean_inc(x_40);
x_41 = lean_nat_dec_lt(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_35);
lean_inc(x_3);
if (lean_is_scalar(x_37)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_37;
}
lean_ctor_set(x_42, 0, x_3);
lean_ctor_set(x_42, 1, x_36);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_14);
x_15 = x_44;
goto block_32;
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_36);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_36, 2);
lean_dec(x_46);
x_47 = lean_ctor_get(x_36, 1);
lean_dec(x_47);
x_48 = lean_ctor_get(x_36, 0);
lean_dec(x_48);
x_49 = lean_array_fget(x_38, x_39);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_39, x_51);
lean_dec(x_39);
lean_ctor_set(x_36, 1, x_52);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_35);
x_53 = l_Lean_Meta_inferType(x_35, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; uint8_t x_170; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
x_170 = l_Lean_BinderInfo_isInstImplicit(x_50);
if (x_170 == 0)
{
lean_object* x_171; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_35);
x_171 = l_Lean_Meta_instantiateMVars(x_35, x_10, x_11, x_12, x_13, x_55);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_54);
x_174 = l_Lean_Meta_isProp(x_54, x_10, x_11, x_12, x_13, x_173);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_unbox(x_175);
if (x_176 == 0)
{
lean_object* x_177; uint8_t x_178; 
lean_dec(x_172);
x_177 = lean_ctor_get(x_174, 1);
lean_inc(x_177);
lean_dec(x_174);
x_178 = lean_unbox(x_175);
lean_dec(x_175);
x_57 = x_178;
x_58 = x_177;
goto block_169;
}
else
{
lean_object* x_179; uint8_t x_180; 
lean_dec(x_175);
x_179 = lean_ctor_get(x_174, 1);
lean_inc(x_179);
lean_dec(x_174);
x_180 = l_Lean_Expr_isMVar(x_172);
lean_dec(x_172);
x_57 = x_180;
x_58 = x_179;
goto block_169;
}
}
else
{
uint8_t x_181; 
lean_dec(x_172);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_36);
lean_dec(x_37);
lean_dec(x_35);
x_181 = !lean_is_exclusive(x_174);
if (x_181 == 0)
{
x_15 = x_174;
goto block_32;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_174, 0);
x_183 = lean_ctor_get(x_174, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_174);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
x_15 = x_184;
goto block_32;
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_36);
lean_dec(x_37);
lean_dec(x_35);
x_185 = !lean_is_exclusive(x_171);
if (x_185 == 0)
{
x_15 = x_171;
goto block_32;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_171, 0);
x_187 = lean_ctor_get(x_171, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_171);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
x_15 = x_188;
goto block_32;
}
}
}
else
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_56);
lean_dec(x_37);
x_189 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_54);
x_190 = l_Lean_Meta_trySynthInstance(x_54, x_189, x_10, x_11, x_12, x_13, x_55);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
switch (lean_obj_tag(x_191)) {
case 0:
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
lean_dec(x_35);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_193 = x_190;
} else {
 lean_dec_ref(x_190);
 x_193 = lean_box(0);
}
x_222 = lean_st_ref_get(x_13, x_192);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_223, 3);
lean_inc(x_224);
lean_dec(x_223);
x_225 = lean_ctor_get_uint8(x_224, sizeof(void*)*1);
lean_dec(x_224);
if (x_225 == 0)
{
lean_object* x_226; uint8_t x_227; 
x_226 = lean_ctor_get(x_222, 1);
lean_inc(x_226);
lean_dec(x_222);
x_227 = 0;
x_194 = x_227;
x_195 = x_226;
goto block_221;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_228 = lean_ctor_get(x_222, 1);
lean_inc(x_228);
lean_dec(x_222);
x_229 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4;
x_230 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__2(x_229, x_8, x_9, x_10, x_11, x_12, x_13, x_228);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_unbox(x_231);
lean_dec(x_231);
x_194 = x_233;
x_195 = x_232;
goto block_221;
}
block_221:
{
if (x_194 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_54);
x_196 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_36);
x_198 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_198, 0, x_197);
if (lean_is_scalar(x_193)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_193;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_195);
x_15 = x_199;
goto block_32;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
lean_dec(x_193);
lean_inc(x_2);
x_200 = l_Std_fmt___at_Lean_Meta_instToMessageDataSimpLemma___spec__1(x_2);
x_201 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_201, 0, x_200);
x_202 = l_Lean_KernelException_toMessageData___closed__15;
x_203 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_201);
x_204 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__10;
x_205 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
x_206 = l_Lean_indentExpr(x_54);
x_207 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
x_208 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_202);
x_209 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4;
x_210 = l_Lean_addTrace___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__1(x_209, x_208, x_8, x_9, x_10, x_11, x_12, x_13, x_195);
x_211 = !lean_is_exclusive(x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_212 = lean_ctor_get(x_210, 0);
lean_dec(x_212);
x_213 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_36);
x_215 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_210, 0, x_215);
x_15 = x_210;
goto block_32;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_216 = lean_ctor_get(x_210, 1);
lean_inc(x_216);
lean_dec(x_210);
x_217 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_36);
x_219 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_219, 0, x_218);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_216);
x_15 = x_220;
goto block_32;
}
}
}
}
case 1:
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_190, 1);
lean_inc(x_234);
lean_dec(x_190);
x_235 = lean_ctor_get(x_191, 0);
lean_inc(x_235);
lean_dec(x_191);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_236 = l_Lean_Meta_isExprDefEq(x_35, x_235, x_10, x_11, x_12, x_13, x_234);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; uint8_t x_238; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_unbox(x_237);
lean_dec(x_237);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_239 = lean_ctor_get(x_236, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_240 = x_236;
} else {
 lean_dec_ref(x_236);
 x_240 = lean_box(0);
}
x_269 = lean_st_ref_get(x_13, x_239);
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_270, 3);
lean_inc(x_271);
lean_dec(x_270);
x_272 = lean_ctor_get_uint8(x_271, sizeof(void*)*1);
lean_dec(x_271);
if (x_272 == 0)
{
lean_object* x_273; uint8_t x_274; 
x_273 = lean_ctor_get(x_269, 1);
lean_inc(x_273);
lean_dec(x_269);
x_274 = 0;
x_241 = x_274;
x_242 = x_273;
goto block_268;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_275 = lean_ctor_get(x_269, 1);
lean_inc(x_275);
lean_dec(x_269);
x_276 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4;
x_277 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__2(x_276, x_8, x_9, x_10, x_11, x_12, x_13, x_275);
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec(x_277);
x_280 = lean_unbox(x_278);
lean_dec(x_278);
x_241 = x_280;
x_242 = x_279;
goto block_268;
}
block_268:
{
if (x_241 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_54);
x_243 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_36);
x_245 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_245, 0, x_244);
if (lean_is_scalar(x_240)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_240;
}
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_242);
x_15 = x_246;
goto block_32;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
lean_dec(x_240);
lean_inc(x_2);
x_247 = l_Std_fmt___at_Lean_Meta_instToMessageDataSimpLemma___spec__1(x_2);
x_248 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_248, 0, x_247);
x_249 = l_Lean_KernelException_toMessageData___closed__15;
x_250 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_248);
x_251 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__12;
x_252 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
x_253 = l_Lean_indentExpr(x_54);
x_254 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
x_255 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_249);
x_256 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4;
x_257 = l_Lean_addTrace___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__1(x_256, x_255, x_8, x_9, x_10, x_11, x_12, x_13, x_242);
x_258 = !lean_is_exclusive(x_257);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_259 = lean_ctor_get(x_257, 0);
lean_dec(x_259);
x_260 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_36);
x_262 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_257, 0, x_262);
x_15 = x_257;
goto block_32;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_263 = lean_ctor_get(x_257, 1);
lean_inc(x_263);
lean_dec(x_257);
x_264 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_36);
x_266 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_266, 0, x_265);
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_263);
x_15 = x_267;
goto block_32;
}
}
}
}
else
{
uint8_t x_281; 
lean_dec(x_54);
x_281 = !lean_is_exclusive(x_236);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_236, 0);
lean_dec(x_282);
lean_inc(x_3);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_3);
lean_ctor_set(x_283, 1, x_36);
x_284 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_236, 0, x_284);
x_15 = x_236;
goto block_32;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_285 = lean_ctor_get(x_236, 1);
lean_inc(x_285);
lean_dec(x_236);
lean_inc(x_3);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_3);
lean_ctor_set(x_286, 1, x_36);
x_287 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_287, 0, x_286);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_285);
x_15 = x_288;
goto block_32;
}
}
}
else
{
uint8_t x_289; 
lean_dec(x_54);
lean_dec(x_36);
x_289 = !lean_is_exclusive(x_236);
if (x_289 == 0)
{
x_15 = x_236;
goto block_32;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_236, 0);
x_291 = lean_ctor_get(x_236, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_236);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
x_15 = x_292;
goto block_32;
}
}
}
default: 
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; lean_object* x_296; lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; 
lean_dec(x_35);
x_293 = lean_ctor_get(x_190, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_294 = x_190;
} else {
 lean_dec_ref(x_190);
 x_294 = lean_box(0);
}
x_323 = lean_st_ref_get(x_13, x_293);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_324, 3);
lean_inc(x_325);
lean_dec(x_324);
x_326 = lean_ctor_get_uint8(x_325, sizeof(void*)*1);
lean_dec(x_325);
if (x_326 == 0)
{
lean_object* x_327; uint8_t x_328; 
x_327 = lean_ctor_get(x_323, 1);
lean_inc(x_327);
lean_dec(x_323);
x_328 = 0;
x_295 = x_328;
x_296 = x_327;
goto block_322;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; 
x_329 = lean_ctor_get(x_323, 1);
lean_inc(x_329);
lean_dec(x_323);
x_330 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4;
x_331 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__2(x_330, x_8, x_9, x_10, x_11, x_12, x_13, x_329);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
lean_dec(x_331);
x_334 = lean_unbox(x_332);
lean_dec(x_332);
x_295 = x_334;
x_296 = x_333;
goto block_322;
}
block_322:
{
if (x_295 == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_54);
x_297 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_36);
x_299 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_299, 0, x_298);
if (lean_is_scalar(x_294)) {
 x_300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_300 = x_294;
}
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_296);
x_15 = x_300;
goto block_32;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
lean_dec(x_294);
lean_inc(x_2);
x_301 = l_Std_fmt___at_Lean_Meta_instToMessageDataSimpLemma___spec__1(x_2);
x_302 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_302, 0, x_301);
x_303 = l_Lean_KernelException_toMessageData___closed__15;
x_304 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_302);
x_305 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__10;
x_306 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
x_307 = l_Lean_indentExpr(x_54);
x_308 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
x_309 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_303);
x_310 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4;
x_311 = l_Lean_addTrace___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__1(x_310, x_309, x_8, x_9, x_10, x_11, x_12, x_13, x_296);
x_312 = !lean_is_exclusive(x_311);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_313 = lean_ctor_get(x_311, 0);
lean_dec(x_313);
x_314 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_36);
x_316 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_311, 0, x_316);
x_15 = x_311;
goto block_32;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_317 = lean_ctor_get(x_311, 1);
lean_inc(x_317);
lean_dec(x_311);
x_318 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_36);
x_320 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_320, 0, x_319);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_317);
x_15 = x_321;
goto block_32;
}
}
}
}
}
}
else
{
uint8_t x_335; 
lean_dec(x_54);
lean_dec(x_36);
lean_dec(x_35);
x_335 = !lean_is_exclusive(x_190);
if (x_335 == 0)
{
x_15 = x_190;
goto block_32;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_336 = lean_ctor_get(x_190, 0);
x_337 = lean_ctor_get(x_190, 1);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_190);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set(x_338, 1, x_337);
x_15 = x_338;
goto block_32;
}
}
}
block_169:
{
if (x_57 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_54);
lean_dec(x_35);
lean_inc(x_3);
if (lean_is_scalar(x_37)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_37;
}
lean_ctor_set(x_59, 0, x_3);
lean_ctor_set(x_59, 1, x_36);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
if (lean_is_scalar(x_56)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_56;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
x_15 = x_61;
goto block_32;
}
else
{
lean_object* x_62; 
lean_dec(x_56);
lean_inc(x_1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_54);
x_62 = lean_apply_8(x_1, x_54, x_8, x_9, x_10, x_11, x_12, x_13, x_58);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_35);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_94 = lean_st_ref_get(x_13, x_64);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_95, 3);
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_ctor_get_uint8(x_96, sizeof(void*)*1);
lean_dec(x_96);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
lean_dec(x_94);
x_99 = 0;
x_66 = x_99;
x_67 = x_98;
goto block_93;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_100 = lean_ctor_get(x_94, 1);
lean_inc(x_100);
lean_dec(x_94);
x_101 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4;
x_102 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__2(x_101, x_8, x_9, x_10, x_11, x_12, x_13, x_100);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_unbox(x_103);
lean_dec(x_103);
x_66 = x_105;
x_67 = x_104;
goto block_93;
}
block_93:
{
if (x_66 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_54);
x_68 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
if (lean_is_scalar(x_37)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_37;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_36);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
if (lean_is_scalar(x_65)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_65;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_67);
x_15 = x_71;
goto block_32;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_dec(x_65);
lean_inc(x_2);
x_72 = l_Std_fmt___at_Lean_Meta_instToMessageDataSimpLemma___spec__1(x_2);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = l_Lean_KernelException_toMessageData___closed__15;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__6;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_indentExpr(x_54);
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_74);
x_81 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4;
x_82 = l_Lean_addTrace___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__1(x_81, x_80, x_8, x_9, x_10, x_11, x_12, x_13, x_67);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_82, 0);
lean_dec(x_84);
x_85 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
if (lean_is_scalar(x_37)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_37;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_36);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_82, 0, x_87);
x_15 = x_82;
goto block_32;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
lean_dec(x_82);
x_89 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
if (lean_is_scalar(x_37)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_37;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_36);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_88);
x_15 = x_92;
goto block_32;
}
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_62, 1);
lean_inc(x_106);
lean_dec(x_62);
x_107 = lean_ctor_get(x_63, 0);
lean_inc(x_107);
lean_dec(x_63);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_108 = l_Lean_Meta_isExprDefEq(x_35, x_107, x_10, x_11, x_12, x_13, x_106);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_unbox(x_109);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_112 = x_108;
} else {
 lean_dec_ref(x_108);
 x_112 = lean_box(0);
}
x_141 = lean_st_ref_get(x_13, x_111);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_142, 3);
lean_inc(x_143);
lean_dec(x_142);
x_144 = lean_ctor_get_uint8(x_143, sizeof(void*)*1);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; uint8_t x_146; 
x_145 = lean_ctor_get(x_141, 1);
lean_inc(x_145);
lean_dec(x_141);
x_146 = 0;
x_113 = x_146;
x_114 = x_145;
goto block_140;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_147 = lean_ctor_get(x_141, 1);
lean_inc(x_147);
lean_dec(x_141);
x_148 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4;
x_149 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__2(x_148, x_8, x_9, x_10, x_11, x_12, x_13, x_147);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_unbox(x_150);
lean_dec(x_150);
x_113 = x_152;
x_114 = x_151;
goto block_140;
}
block_140:
{
if (x_113 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_54);
x_115 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
if (lean_is_scalar(x_37)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_37;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_36);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
if (lean_is_scalar(x_112)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_112;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_114);
x_15 = x_118;
goto block_32;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
lean_dec(x_112);
lean_inc(x_2);
x_119 = l_Std_fmt___at_Lean_Meta_instToMessageDataSimpLemma___spec__1(x_2);
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = l_Lean_KernelException_toMessageData___closed__15;
x_122 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
x_123 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__8;
x_124 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_indentExpr(x_54);
x_126 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_121);
x_128 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4;
x_129 = l_Lean_addTrace___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__1(x_128, x_127, x_8, x_9, x_10, x_11, x_12, x_13, x_114);
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_129, 0);
lean_dec(x_131);
x_132 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
if (lean_is_scalar(x_37)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_37;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_36);
x_134 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_129, 0, x_134);
x_15 = x_129;
goto block_32;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_135 = lean_ctor_get(x_129, 1);
lean_inc(x_135);
lean_dec(x_129);
x_136 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
if (lean_is_scalar(x_37)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_37;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_36);
x_138 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_138, 0, x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_135);
x_15 = x_139;
goto block_32;
}
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_54);
x_153 = !lean_is_exclusive(x_108);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_108, 0);
lean_dec(x_154);
lean_inc(x_3);
if (lean_is_scalar(x_37)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_37;
}
lean_ctor_set(x_155, 0, x_3);
lean_ctor_set(x_155, 1, x_36);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_108, 0, x_156);
x_15 = x_108;
goto block_32;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_108, 1);
lean_inc(x_157);
lean_dec(x_108);
lean_inc(x_3);
if (lean_is_scalar(x_37)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_37;
}
lean_ctor_set(x_158, 0, x_3);
lean_ctor_set(x_158, 1, x_36);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_157);
x_15 = x_160;
goto block_32;
}
}
}
else
{
uint8_t x_161; 
lean_dec(x_54);
lean_dec(x_36);
lean_dec(x_37);
x_161 = !lean_is_exclusive(x_108);
if (x_161 == 0)
{
x_15 = x_108;
goto block_32;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_108, 0);
x_163 = lean_ctor_get(x_108, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_108);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_15 = x_164;
goto block_32;
}
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_54);
lean_dec(x_36);
lean_dec(x_37);
lean_dec(x_35);
x_165 = !lean_is_exclusive(x_62);
if (x_165 == 0)
{
x_15 = x_62;
goto block_32;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_62, 0);
x_167 = lean_ctor_get(x_62, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_62);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_15 = x_168;
goto block_32;
}
}
}
}
}
else
{
uint8_t x_339; 
lean_dec(x_36);
lean_dec(x_37);
lean_dec(x_35);
x_339 = !lean_is_exclusive(x_53);
if (x_339 == 0)
{
x_15 = x_53;
goto block_32;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_53, 0);
x_341 = lean_ctor_get(x_53, 1);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_53);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
x_15 = x_342;
goto block_32;
}
}
}
else
{
lean_object* x_343; uint8_t x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_36);
x_343 = lean_array_fget(x_38, x_39);
x_344 = lean_unbox(x_343);
lean_dec(x_343);
x_345 = lean_unsigned_to_nat(1u);
x_346 = lean_nat_add(x_39, x_345);
lean_dec(x_39);
x_347 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_347, 0, x_38);
lean_ctor_set(x_347, 1, x_346);
lean_ctor_set(x_347, 2, x_40);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_35);
x_348 = l_Lean_Meta_inferType(x_35, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; lean_object* x_353; uint8_t x_454; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_351 = x_348;
} else {
 lean_dec_ref(x_348);
 x_351 = lean_box(0);
}
x_454 = l_Lean_BinderInfo_isInstImplicit(x_344);
if (x_454 == 0)
{
lean_object* x_455; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_35);
x_455 = l_Lean_Meta_instantiateMVars(x_35, x_10, x_11, x_12, x_13, x_350);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_455, 1);
lean_inc(x_457);
lean_dec(x_455);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_349);
x_458 = l_Lean_Meta_isProp(x_349, x_10, x_11, x_12, x_13, x_457);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; uint8_t x_460; 
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
x_460 = lean_unbox(x_459);
if (x_460 == 0)
{
lean_object* x_461; uint8_t x_462; 
lean_dec(x_456);
x_461 = lean_ctor_get(x_458, 1);
lean_inc(x_461);
lean_dec(x_458);
x_462 = lean_unbox(x_459);
lean_dec(x_459);
x_352 = x_462;
x_353 = x_461;
goto block_453;
}
else
{
lean_object* x_463; uint8_t x_464; 
lean_dec(x_459);
x_463 = lean_ctor_get(x_458, 1);
lean_inc(x_463);
lean_dec(x_458);
x_464 = l_Lean_Expr_isMVar(x_456);
lean_dec(x_456);
x_352 = x_464;
x_353 = x_463;
goto block_453;
}
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
lean_dec(x_456);
lean_dec(x_351);
lean_dec(x_349);
lean_dec(x_347);
lean_dec(x_37);
lean_dec(x_35);
x_465 = lean_ctor_get(x_458, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_458, 1);
lean_inc(x_466);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 x_467 = x_458;
} else {
 lean_dec_ref(x_458);
 x_467 = lean_box(0);
}
if (lean_is_scalar(x_467)) {
 x_468 = lean_alloc_ctor(1, 2, 0);
} else {
 x_468 = x_467;
}
lean_ctor_set(x_468, 0, x_465);
lean_ctor_set(x_468, 1, x_466);
x_15 = x_468;
goto block_32;
}
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
lean_dec(x_351);
lean_dec(x_349);
lean_dec(x_347);
lean_dec(x_37);
lean_dec(x_35);
x_469 = lean_ctor_get(x_455, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_455, 1);
lean_inc(x_470);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 lean_ctor_release(x_455, 1);
 x_471 = x_455;
} else {
 lean_dec_ref(x_455);
 x_471 = lean_box(0);
}
if (lean_is_scalar(x_471)) {
 x_472 = lean_alloc_ctor(1, 2, 0);
} else {
 x_472 = x_471;
}
lean_ctor_set(x_472, 0, x_469);
lean_ctor_set(x_472, 1, x_470);
x_15 = x_472;
goto block_32;
}
}
else
{
lean_object* x_473; lean_object* x_474; 
lean_dec(x_351);
lean_dec(x_37);
x_473 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_349);
x_474 = l_Lean_Meta_trySynthInstance(x_349, x_473, x_10, x_11, x_12, x_13, x_350);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; 
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
switch (lean_obj_tag(x_475)) {
case 0:
{
lean_object* x_476; lean_object* x_477; uint8_t x_478; lean_object* x_479; lean_object* x_502; lean_object* x_503; lean_object* x_504; uint8_t x_505; 
lean_dec(x_35);
x_476 = lean_ctor_get(x_474, 1);
lean_inc(x_476);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 lean_ctor_release(x_474, 1);
 x_477 = x_474;
} else {
 lean_dec_ref(x_474);
 x_477 = lean_box(0);
}
x_502 = lean_st_ref_get(x_13, x_476);
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_503, 3);
lean_inc(x_504);
lean_dec(x_503);
x_505 = lean_ctor_get_uint8(x_504, sizeof(void*)*1);
lean_dec(x_504);
if (x_505 == 0)
{
lean_object* x_506; uint8_t x_507; 
x_506 = lean_ctor_get(x_502, 1);
lean_inc(x_506);
lean_dec(x_502);
x_507 = 0;
x_478 = x_507;
x_479 = x_506;
goto block_501;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; uint8_t x_513; 
x_508 = lean_ctor_get(x_502, 1);
lean_inc(x_508);
lean_dec(x_502);
x_509 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4;
x_510 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__2(x_509, x_8, x_9, x_10, x_11, x_12, x_13, x_508);
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_510, 1);
lean_inc(x_512);
lean_dec(x_510);
x_513 = lean_unbox(x_511);
lean_dec(x_511);
x_478 = x_513;
x_479 = x_512;
goto block_501;
}
block_501:
{
if (x_478 == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
lean_dec(x_349);
x_480 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
x_481 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_481, 0, x_480);
lean_ctor_set(x_481, 1, x_347);
x_482 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_482, 0, x_481);
if (lean_is_scalar(x_477)) {
 x_483 = lean_alloc_ctor(0, 2, 0);
} else {
 x_483 = x_477;
}
lean_ctor_set(x_483, 0, x_482);
lean_ctor_set(x_483, 1, x_479);
x_15 = x_483;
goto block_32;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_477);
lean_inc(x_2);
x_484 = l_Std_fmt___at_Lean_Meta_instToMessageDataSimpLemma___spec__1(x_2);
x_485 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_485, 0, x_484);
x_486 = l_Lean_KernelException_toMessageData___closed__15;
x_487 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_485);
x_488 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__10;
x_489 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_489, 0, x_487);
lean_ctor_set(x_489, 1, x_488);
x_490 = l_Lean_indentExpr(x_349);
x_491 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_491, 0, x_489);
lean_ctor_set(x_491, 1, x_490);
x_492 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_492, 0, x_491);
lean_ctor_set(x_492, 1, x_486);
x_493 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4;
x_494 = l_Lean_addTrace___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__1(x_493, x_492, x_8, x_9, x_10, x_11, x_12, x_13, x_479);
x_495 = lean_ctor_get(x_494, 1);
lean_inc(x_495);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_496 = x_494;
} else {
 lean_dec_ref(x_494);
 x_496 = lean_box(0);
}
x_497 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
x_498 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_498, 0, x_497);
lean_ctor_set(x_498, 1, x_347);
x_499 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_499, 0, x_498);
if (lean_is_scalar(x_496)) {
 x_500 = lean_alloc_ctor(0, 2, 0);
} else {
 x_500 = x_496;
}
lean_ctor_set(x_500, 0, x_499);
lean_ctor_set(x_500, 1, x_495);
x_15 = x_500;
goto block_32;
}
}
}
case 1:
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_514 = lean_ctor_get(x_474, 1);
lean_inc(x_514);
lean_dec(x_474);
x_515 = lean_ctor_get(x_475, 0);
lean_inc(x_515);
lean_dec(x_475);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_516 = l_Lean_Meta_isExprDefEq(x_35, x_515, x_10, x_11, x_12, x_13, x_514);
if (lean_obj_tag(x_516) == 0)
{
lean_object* x_517; uint8_t x_518; 
x_517 = lean_ctor_get(x_516, 0);
lean_inc(x_517);
x_518 = lean_unbox(x_517);
lean_dec(x_517);
if (x_518 == 0)
{
lean_object* x_519; lean_object* x_520; uint8_t x_521; lean_object* x_522; lean_object* x_545; lean_object* x_546; lean_object* x_547; uint8_t x_548; 
x_519 = lean_ctor_get(x_516, 1);
lean_inc(x_519);
if (lean_is_exclusive(x_516)) {
 lean_ctor_release(x_516, 0);
 lean_ctor_release(x_516, 1);
 x_520 = x_516;
} else {
 lean_dec_ref(x_516);
 x_520 = lean_box(0);
}
x_545 = lean_st_ref_get(x_13, x_519);
x_546 = lean_ctor_get(x_545, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_546, 3);
lean_inc(x_547);
lean_dec(x_546);
x_548 = lean_ctor_get_uint8(x_547, sizeof(void*)*1);
lean_dec(x_547);
if (x_548 == 0)
{
lean_object* x_549; uint8_t x_550; 
x_549 = lean_ctor_get(x_545, 1);
lean_inc(x_549);
lean_dec(x_545);
x_550 = 0;
x_521 = x_550;
x_522 = x_549;
goto block_544;
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; uint8_t x_556; 
x_551 = lean_ctor_get(x_545, 1);
lean_inc(x_551);
lean_dec(x_545);
x_552 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4;
x_553 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__2(x_552, x_8, x_9, x_10, x_11, x_12, x_13, x_551);
x_554 = lean_ctor_get(x_553, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_553, 1);
lean_inc(x_555);
lean_dec(x_553);
x_556 = lean_unbox(x_554);
lean_dec(x_554);
x_521 = x_556;
x_522 = x_555;
goto block_544;
}
block_544:
{
if (x_521 == 0)
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; 
lean_dec(x_349);
x_523 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
x_524 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_524, 1, x_347);
x_525 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_525, 0, x_524);
if (lean_is_scalar(x_520)) {
 x_526 = lean_alloc_ctor(0, 2, 0);
} else {
 x_526 = x_520;
}
lean_ctor_set(x_526, 0, x_525);
lean_ctor_set(x_526, 1, x_522);
x_15 = x_526;
goto block_32;
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
lean_dec(x_520);
lean_inc(x_2);
x_527 = l_Std_fmt___at_Lean_Meta_instToMessageDataSimpLemma___spec__1(x_2);
x_528 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_528, 0, x_527);
x_529 = l_Lean_KernelException_toMessageData___closed__15;
x_530 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_530, 0, x_529);
lean_ctor_set(x_530, 1, x_528);
x_531 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__12;
x_532 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_532, 0, x_530);
lean_ctor_set(x_532, 1, x_531);
x_533 = l_Lean_indentExpr(x_349);
x_534 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_534, 0, x_532);
lean_ctor_set(x_534, 1, x_533);
x_535 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_535, 0, x_534);
lean_ctor_set(x_535, 1, x_529);
x_536 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4;
x_537 = l_Lean_addTrace___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__1(x_536, x_535, x_8, x_9, x_10, x_11, x_12, x_13, x_522);
x_538 = lean_ctor_get(x_537, 1);
lean_inc(x_538);
if (lean_is_exclusive(x_537)) {
 lean_ctor_release(x_537, 0);
 lean_ctor_release(x_537, 1);
 x_539 = x_537;
} else {
 lean_dec_ref(x_537);
 x_539 = lean_box(0);
}
x_540 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
x_541 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_541, 0, x_540);
lean_ctor_set(x_541, 1, x_347);
x_542 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_542, 0, x_541);
if (lean_is_scalar(x_539)) {
 x_543 = lean_alloc_ctor(0, 2, 0);
} else {
 x_543 = x_539;
}
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_538);
x_15 = x_543;
goto block_32;
}
}
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
lean_dec(x_349);
x_557 = lean_ctor_get(x_516, 1);
lean_inc(x_557);
if (lean_is_exclusive(x_516)) {
 lean_ctor_release(x_516, 0);
 lean_ctor_release(x_516, 1);
 x_558 = x_516;
} else {
 lean_dec_ref(x_516);
 x_558 = lean_box(0);
}
lean_inc(x_3);
x_559 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_559, 0, x_3);
lean_ctor_set(x_559, 1, x_347);
x_560 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_560, 0, x_559);
if (lean_is_scalar(x_558)) {
 x_561 = lean_alloc_ctor(0, 2, 0);
} else {
 x_561 = x_558;
}
lean_ctor_set(x_561, 0, x_560);
lean_ctor_set(x_561, 1, x_557);
x_15 = x_561;
goto block_32;
}
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
lean_dec(x_349);
lean_dec(x_347);
x_562 = lean_ctor_get(x_516, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_516, 1);
lean_inc(x_563);
if (lean_is_exclusive(x_516)) {
 lean_ctor_release(x_516, 0);
 lean_ctor_release(x_516, 1);
 x_564 = x_516;
} else {
 lean_dec_ref(x_516);
 x_564 = lean_box(0);
}
if (lean_is_scalar(x_564)) {
 x_565 = lean_alloc_ctor(1, 2, 0);
} else {
 x_565 = x_564;
}
lean_ctor_set(x_565, 0, x_562);
lean_ctor_set(x_565, 1, x_563);
x_15 = x_565;
goto block_32;
}
}
default: 
{
lean_object* x_566; lean_object* x_567; uint8_t x_568; lean_object* x_569; lean_object* x_592; lean_object* x_593; lean_object* x_594; uint8_t x_595; 
lean_dec(x_35);
x_566 = lean_ctor_get(x_474, 1);
lean_inc(x_566);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 lean_ctor_release(x_474, 1);
 x_567 = x_474;
} else {
 lean_dec_ref(x_474);
 x_567 = lean_box(0);
}
x_592 = lean_st_ref_get(x_13, x_566);
x_593 = lean_ctor_get(x_592, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_593, 3);
lean_inc(x_594);
lean_dec(x_593);
x_595 = lean_ctor_get_uint8(x_594, sizeof(void*)*1);
lean_dec(x_594);
if (x_595 == 0)
{
lean_object* x_596; uint8_t x_597; 
x_596 = lean_ctor_get(x_592, 1);
lean_inc(x_596);
lean_dec(x_592);
x_597 = 0;
x_568 = x_597;
x_569 = x_596;
goto block_591;
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; uint8_t x_603; 
x_598 = lean_ctor_get(x_592, 1);
lean_inc(x_598);
lean_dec(x_592);
x_599 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4;
x_600 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__2(x_599, x_8, x_9, x_10, x_11, x_12, x_13, x_598);
x_601 = lean_ctor_get(x_600, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_600, 1);
lean_inc(x_602);
lean_dec(x_600);
x_603 = lean_unbox(x_601);
lean_dec(x_601);
x_568 = x_603;
x_569 = x_602;
goto block_591;
}
block_591:
{
if (x_568 == 0)
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
lean_dec(x_349);
x_570 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
x_571 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_571, 0, x_570);
lean_ctor_set(x_571, 1, x_347);
x_572 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_572, 0, x_571);
if (lean_is_scalar(x_567)) {
 x_573 = lean_alloc_ctor(0, 2, 0);
} else {
 x_573 = x_567;
}
lean_ctor_set(x_573, 0, x_572);
lean_ctor_set(x_573, 1, x_569);
x_15 = x_573;
goto block_32;
}
else
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; 
lean_dec(x_567);
lean_inc(x_2);
x_574 = l_Std_fmt___at_Lean_Meta_instToMessageDataSimpLemma___spec__1(x_2);
x_575 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_575, 0, x_574);
x_576 = l_Lean_KernelException_toMessageData___closed__15;
x_577 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_577, 0, x_576);
lean_ctor_set(x_577, 1, x_575);
x_578 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__10;
x_579 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_579, 0, x_577);
lean_ctor_set(x_579, 1, x_578);
x_580 = l_Lean_indentExpr(x_349);
x_581 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_581, 0, x_579);
lean_ctor_set(x_581, 1, x_580);
x_582 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_582, 0, x_581);
lean_ctor_set(x_582, 1, x_576);
x_583 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4;
x_584 = l_Lean_addTrace___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__1(x_583, x_582, x_8, x_9, x_10, x_11, x_12, x_13, x_569);
x_585 = lean_ctor_get(x_584, 1);
lean_inc(x_585);
if (lean_is_exclusive(x_584)) {
 lean_ctor_release(x_584, 0);
 lean_ctor_release(x_584, 1);
 x_586 = x_584;
} else {
 lean_dec_ref(x_584);
 x_586 = lean_box(0);
}
x_587 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
x_588 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_588, 0, x_587);
lean_ctor_set(x_588, 1, x_347);
x_589 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_589, 0, x_588);
if (lean_is_scalar(x_586)) {
 x_590 = lean_alloc_ctor(0, 2, 0);
} else {
 x_590 = x_586;
}
lean_ctor_set(x_590, 0, x_589);
lean_ctor_set(x_590, 1, x_585);
x_15 = x_590;
goto block_32;
}
}
}
}
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; 
lean_dec(x_349);
lean_dec(x_347);
lean_dec(x_35);
x_604 = lean_ctor_get(x_474, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_474, 1);
lean_inc(x_605);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 lean_ctor_release(x_474, 1);
 x_606 = x_474;
} else {
 lean_dec_ref(x_474);
 x_606 = lean_box(0);
}
if (lean_is_scalar(x_606)) {
 x_607 = lean_alloc_ctor(1, 2, 0);
} else {
 x_607 = x_606;
}
lean_ctor_set(x_607, 0, x_604);
lean_ctor_set(x_607, 1, x_605);
x_15 = x_607;
goto block_32;
}
}
block_453:
{
if (x_352 == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_349);
lean_dec(x_35);
lean_inc(x_3);
if (lean_is_scalar(x_37)) {
 x_354 = lean_alloc_ctor(0, 2, 0);
} else {
 x_354 = x_37;
}
lean_ctor_set(x_354, 0, x_3);
lean_ctor_set(x_354, 1, x_347);
x_355 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_355, 0, x_354);
if (lean_is_scalar(x_351)) {
 x_356 = lean_alloc_ctor(0, 2, 0);
} else {
 x_356 = x_351;
}
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_353);
x_15 = x_356;
goto block_32;
}
else
{
lean_object* x_357; 
lean_dec(x_351);
lean_inc(x_1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_349);
x_357 = lean_apply_8(x_1, x_349, x_8, x_9, x_10, x_11, x_12, x_13, x_353);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; uint8_t x_361; lean_object* x_362; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; 
lean_dec(x_35);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 x_360 = x_357;
} else {
 lean_dec_ref(x_357);
 x_360 = lean_box(0);
}
x_385 = lean_st_ref_get(x_13, x_359);
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_386, 3);
lean_inc(x_387);
lean_dec(x_386);
x_388 = lean_ctor_get_uint8(x_387, sizeof(void*)*1);
lean_dec(x_387);
if (x_388 == 0)
{
lean_object* x_389; uint8_t x_390; 
x_389 = lean_ctor_get(x_385, 1);
lean_inc(x_389);
lean_dec(x_385);
x_390 = 0;
x_361 = x_390;
x_362 = x_389;
goto block_384;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; 
x_391 = lean_ctor_get(x_385, 1);
lean_inc(x_391);
lean_dec(x_385);
x_392 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4;
x_393 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__2(x_392, x_8, x_9, x_10, x_11, x_12, x_13, x_391);
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
lean_dec(x_393);
x_396 = lean_unbox(x_394);
lean_dec(x_394);
x_361 = x_396;
x_362 = x_395;
goto block_384;
}
block_384:
{
if (x_361 == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_349);
x_363 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
if (lean_is_scalar(x_37)) {
 x_364 = lean_alloc_ctor(0, 2, 0);
} else {
 x_364 = x_37;
}
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_347);
x_365 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_365, 0, x_364);
if (lean_is_scalar(x_360)) {
 x_366 = lean_alloc_ctor(0, 2, 0);
} else {
 x_366 = x_360;
}
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_362);
x_15 = x_366;
goto block_32;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
lean_dec(x_360);
lean_inc(x_2);
x_367 = l_Std_fmt___at_Lean_Meta_instToMessageDataSimpLemma___spec__1(x_2);
x_368 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_368, 0, x_367);
x_369 = l_Lean_KernelException_toMessageData___closed__15;
x_370 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_368);
x_371 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__6;
x_372 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
x_373 = l_Lean_indentExpr(x_349);
x_374 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_373);
x_375 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_369);
x_376 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4;
x_377 = l_Lean_addTrace___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__1(x_376, x_375, x_8, x_9, x_10, x_11, x_12, x_13, x_362);
x_378 = lean_ctor_get(x_377, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_379 = x_377;
} else {
 lean_dec_ref(x_377);
 x_379 = lean_box(0);
}
x_380 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
if (lean_is_scalar(x_37)) {
 x_381 = lean_alloc_ctor(0, 2, 0);
} else {
 x_381 = x_37;
}
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_347);
x_382 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_382, 0, x_381);
if (lean_is_scalar(x_379)) {
 x_383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_383 = x_379;
}
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_378);
x_15 = x_383;
goto block_32;
}
}
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_397 = lean_ctor_get(x_357, 1);
lean_inc(x_397);
lean_dec(x_357);
x_398 = lean_ctor_get(x_358, 0);
lean_inc(x_398);
lean_dec(x_358);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_399 = l_Lean_Meta_isExprDefEq(x_35, x_398, x_10, x_11, x_12, x_13, x_397);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; uint8_t x_401; 
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
x_401 = lean_unbox(x_400);
lean_dec(x_400);
if (x_401 == 0)
{
lean_object* x_402; lean_object* x_403; uint8_t x_404; lean_object* x_405; lean_object* x_428; lean_object* x_429; lean_object* x_430; uint8_t x_431; 
x_402 = lean_ctor_get(x_399, 1);
lean_inc(x_402);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 x_403 = x_399;
} else {
 lean_dec_ref(x_399);
 x_403 = lean_box(0);
}
x_428 = lean_st_ref_get(x_13, x_402);
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_429, 3);
lean_inc(x_430);
lean_dec(x_429);
x_431 = lean_ctor_get_uint8(x_430, sizeof(void*)*1);
lean_dec(x_430);
if (x_431 == 0)
{
lean_object* x_432; uint8_t x_433; 
x_432 = lean_ctor_get(x_428, 1);
lean_inc(x_432);
lean_dec(x_428);
x_433 = 0;
x_404 = x_433;
x_405 = x_432;
goto block_427;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; 
x_434 = lean_ctor_get(x_428, 1);
lean_inc(x_434);
lean_dec(x_428);
x_435 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4;
x_436 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__2(x_435, x_8, x_9, x_10, x_11, x_12, x_13, x_434);
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_436, 1);
lean_inc(x_438);
lean_dec(x_436);
x_439 = lean_unbox(x_437);
lean_dec(x_437);
x_404 = x_439;
x_405 = x_438;
goto block_427;
}
block_427:
{
if (x_404 == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_349);
x_406 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
if (lean_is_scalar(x_37)) {
 x_407 = lean_alloc_ctor(0, 2, 0);
} else {
 x_407 = x_37;
}
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_347);
x_408 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_408, 0, x_407);
if (lean_is_scalar(x_403)) {
 x_409 = lean_alloc_ctor(0, 2, 0);
} else {
 x_409 = x_403;
}
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_405);
x_15 = x_409;
goto block_32;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_403);
lean_inc(x_2);
x_410 = l_Std_fmt___at_Lean_Meta_instToMessageDataSimpLemma___spec__1(x_2);
x_411 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_411, 0, x_410);
x_412 = l_Lean_KernelException_toMessageData___closed__15;
x_413 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_411);
x_414 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__8;
x_415 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_415, 0, x_413);
lean_ctor_set(x_415, 1, x_414);
x_416 = l_Lean_indentExpr(x_349);
x_417 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_417, 0, x_415);
lean_ctor_set(x_417, 1, x_416);
x_418 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_412);
x_419 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4;
x_420 = l_Lean_addTrace___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__1(x_419, x_418, x_8, x_9, x_10, x_11, x_12, x_13, x_405);
x_421 = lean_ctor_get(x_420, 1);
lean_inc(x_421);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 x_422 = x_420;
} else {
 lean_dec_ref(x_420);
 x_422 = lean_box(0);
}
x_423 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__4___closed__1;
if (lean_is_scalar(x_37)) {
 x_424 = lean_alloc_ctor(0, 2, 0);
} else {
 x_424 = x_37;
}
lean_ctor_set(x_424, 0, x_423);
lean_ctor_set(x_424, 1, x_347);
x_425 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_425, 0, x_424);
if (lean_is_scalar(x_422)) {
 x_426 = lean_alloc_ctor(0, 2, 0);
} else {
 x_426 = x_422;
}
lean_ctor_set(x_426, 0, x_425);
lean_ctor_set(x_426, 1, x_421);
x_15 = x_426;
goto block_32;
}
}
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
lean_dec(x_349);
x_440 = lean_ctor_get(x_399, 1);
lean_inc(x_440);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 x_441 = x_399;
} else {
 lean_dec_ref(x_399);
 x_441 = lean_box(0);
}
lean_inc(x_3);
if (lean_is_scalar(x_37)) {
 x_442 = lean_alloc_ctor(0, 2, 0);
} else {
 x_442 = x_37;
}
lean_ctor_set(x_442, 0, x_3);
lean_ctor_set(x_442, 1, x_347);
x_443 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_443, 0, x_442);
if (lean_is_scalar(x_441)) {
 x_444 = lean_alloc_ctor(0, 2, 0);
} else {
 x_444 = x_441;
}
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_440);
x_15 = x_444;
goto block_32;
}
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_349);
lean_dec(x_347);
lean_dec(x_37);
x_445 = lean_ctor_get(x_399, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_399, 1);
lean_inc(x_446);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 x_447 = x_399;
} else {
 lean_dec_ref(x_399);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(1, 2, 0);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_445);
lean_ctor_set(x_448, 1, x_446);
x_15 = x_448;
goto block_32;
}
}
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
lean_dec(x_349);
lean_dec(x_347);
lean_dec(x_37);
lean_dec(x_35);
x_449 = lean_ctor_get(x_357, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_357, 1);
lean_inc(x_450);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 x_451 = x_357;
} else {
 lean_dec_ref(x_357);
 x_451 = lean_box(0);
}
if (lean_is_scalar(x_451)) {
 x_452 = lean_alloc_ctor(1, 2, 0);
} else {
 x_452 = x_451;
}
lean_ctor_set(x_452, 0, x_449);
lean_ctor_set(x_452, 1, x_450);
x_15 = x_452;
goto block_32;
}
}
}
}
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
lean_dec(x_347);
lean_dec(x_37);
lean_dec(x_35);
x_608 = lean_ctor_get(x_348, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_348, 1);
lean_inc(x_609);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_610 = x_348;
} else {
 lean_dec_ref(x_348);
 x_610 = lean_box(0);
}
if (lean_is_scalar(x_610)) {
 x_611 = lean_alloc_ctor(1, 2, 0);
} else {
 x_611 = x_610;
}
lean_ctor_set(x_611, 0, x_608);
lean_ctor_set(x_611, 1, x_609);
x_15 = x_611;
goto block_32;
}
}
}
}
block_32:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
x_25 = 1;
x_26 = x_6 + x_25;
x_6 = x_26;
x_7 = x_24;
x_14 = x_23;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
return x_15;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_15, 0);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_15);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_synthesizeArgs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_rewrite_synthesizeArgs___lambda__1___boxed), 8, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_12 = lean_array_get_size(x_4);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_toSubarray___rarg(x_4, x_13, x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_array_get_size(x_3);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3(x_1, x_2, x_15, x_3, x_18, x_19, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lean_Meta_Simp_rewrite_synthesizeArgs___closed__1;
x_25 = lean_box(0);
x_26 = lean_apply_8(x_24, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_20, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_29);
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3(x_1, x_2, x_3, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
return x_17;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_rewrite_synthesizeArgs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_synthesizeArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_rewrite_synthesizeArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_finalizeProof(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkPropExt(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
case 2:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_mkEqTrue(x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
default: 
{
lean_object* x_11; 
x_11 = l_Lean_Meta_mkEqFalse(x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
}
}
lean_object* l_Lean_Meta_Simp_rewrite_finalizeProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Meta_Simp_rewrite_finalizeProof(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_8, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_15, 3);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_12);
lean_inc(x_10);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Std_PersistentArray_push___rarg(x_21, x_23);
lean_ctor_set(x_16, 0, x_24);
x_25 = lean_st_ref_set(x_8, x_15, x_17);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
x_33 = lean_ctor_get(x_16, 0);
lean_inc(x_33);
lean_dec(x_16);
x_34 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_12);
lean_inc(x_10);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_10);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Std_PersistentArray_push___rarg(x_33, x_35);
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_32);
lean_ctor_set(x_15, 3, x_37);
x_38 = lean_st_ref_set(x_8, x_15, x_17);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_43 = lean_ctor_get(x_15, 0);
x_44 = lean_ctor_get(x_15, 1);
x_45 = lean_ctor_get(x_15, 2);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_15);
x_46 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
x_47 = lean_ctor_get(x_16, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_48 = x_16;
} else {
 lean_dec_ref(x_16);
 x_48 = lean_box(0);
}
x_49 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_12);
lean_inc(x_10);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_10);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Std_PersistentArray_push___rarg(x_47, x_50);
if (lean_is_scalar(x_48)) {
 x_52 = lean_alloc_ctor(0, 1, 1);
} else {
 x_52 = x_48;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_46);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_43);
lean_ctor_set(x_53, 1, x_44);
lean_ctor_set(x_53, 2, x_45);
lean_ctor_set(x_53, 3, x_52);
x_54 = lean_st_ref_set(x_8, x_53, x_17);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_Lean_checkTraceOption(x_9, x_1);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
lean_object* l_ReaderT_bind___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_ReaderT_bind___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__3___rarg), 9, 0);
return x_3;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_2(x_1, x_2, x_3);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___rarg(x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
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
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__4___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SimpLemma_getValue(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__2;
x_2 = l_Lean_Parser_Tactic_rewrite___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_14 = l_Lean_Meta_Simp_rewrite_finalizeProof(x_1, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_50 = lean_st_ref_get(x_12, x_16);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 3);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_ctor_get_uint8(x_52, sizeof(void*)*1);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = 0;
x_18 = x_55;
x_19 = x_54;
goto block_49;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_dec(x_50);
x_57 = l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__2___closed__1;
x_58 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__2(x_57, x_7, x_8, x_9, x_10, x_11, x_12, x_56);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_unbox(x_59);
lean_dec(x_59);
x_18 = x_61;
x_19 = x_60;
goto block_49;
}
block_49:
{
if (x_18 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
if (lean_is_scalar(x_17)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_17;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_17);
x_24 = l_Std_fmt___at_Lean_Meta_instToMessageDataSimpLemma___spec__1(x_4);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_KernelException_toMessageData___closed__15;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__8;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_5);
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Meta_synthInstance_x3f___lambda__2___closed__8;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_3);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_3);
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_26);
x_37 = l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__2___closed__1;
x_38 = l_Lean_addTrace___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__1(x_37, x_36, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_15);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_3);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_38, 0, x_43);
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_dec(x_38);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_15);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_3);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_14);
if (x_62 == 0)
{
return x_14;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_14, 0);
x_64 = lean_ctor_get(x_14, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_14);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unify");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__2;
x_2 = l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", perm rejected ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_Meta_Simp_rewrite_getRHS(x_1, x_2, x_10, x_11, x_12, x_13, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_18 = l_Lean_Meta_instantiateMVars(x_16, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = lean_ctor_get_uint8(x_4, sizeof(void*)*4 + 1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__2(x_1, x_3, x_20, x_4, x_5, x_22, x_8, x_9, x_10, x_11, x_12, x_13, x_21);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_26 = x_18;
} else {
 lean_dec_ref(x_18);
 x_26 = lean_box(0);
}
x_27 = lean_expr_lt(x_24, x_5);
if (x_27 == 0)
{
uint8_t x_28; lean_object* x_29; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_3);
x_51 = lean_st_ref_get(x_13, x_25);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_52, 3);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_ctor_get_uint8(x_53, sizeof(void*)*1);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = 0;
x_28 = x_56;
x_29 = x_55;
goto block_50;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_dec(x_51);
x_58 = l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__2;
x_59 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__2(x_58, x_8, x_9, x_10, x_11, x_12, x_13, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_unbox(x_60);
lean_dec(x_60);
x_28 = x_62;
x_29 = x_61;
goto block_50;
}
block_50:
{
if (x_28 == 0)
{
lean_object* x_30; 
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_26)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_26;
}
lean_ctor_set(x_30, 0, x_6);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_26);
x_31 = l_Std_fmt___at_Lean_Meta_instToMessageDataSimpLemma___spec__1(x_4);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Lean_KernelException_toMessageData___closed__15;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__4;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_5);
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Meta_synthInstance_x3f___lambda__2___closed__8;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_24);
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_33);
x_44 = l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__2;
x_45 = l_Lean_addTrace___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__1(x_44, x_43, x_8, x_9, x_10, x_11, x_12, x_13, x_29);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_6);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_6);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_26);
lean_dec(x_6);
x_63 = lean_box(0);
x_64 = l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__2(x_1, x_3, x_24, x_4, x_5, x_63, x_8, x_9, x_10, x_11, x_12, x_13, x_25);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_18);
if (x_65 == 0)
{
return x_18;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_18, 0);
x_67 = lean_ctor_get(x_18, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_18);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_mkAppN(x_1, x_2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_17 = l_Lean_Meta_instantiateMVars(x_16, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_hasAssignableMVar(x_18, x_11, x_12, x_13, x_14, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3(x_3, x_4, x_18, x_5, x_6, x_7, x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_23);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_20, 0);
lean_dec(x_27);
lean_ctor_set(x_20, 0, x_7);
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", failed to unify ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_changeWith___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
x_12 = l_Lean_Meta_inferType(x_4, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = 1;
x_17 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_13, x_16, x_15, x_17, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 2);
lean_inc(x_24);
x_26 = l_Lean_Meta_Simp_rewrite_getLHS(x_25, x_24, x_7, x_8, x_9, x_10, x_21);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_27);
x_29 = l_Lean_Meta_isExprDefEq(x_27, x_2, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_4);
lean_dec(x_3);
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
x_57 = lean_st_ref_get(x_10, x_32);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 3);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_ctor_get_uint8(x_59, sizeof(void*)*1);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec(x_57);
x_62 = 0;
x_34 = x_62;
x_35 = x_61;
goto block_56;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_dec(x_57);
x_64 = l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__2;
x_65 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__2(x_64, x_5, x_6, x_7, x_8, x_9, x_10, x_63);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_unbox(x_66);
lean_dec(x_66);
x_34 = x_68;
x_35 = x_67;
goto block_56;
}
block_56:
{
if (x_34 == 0)
{
lean_object* x_36; 
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_33)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_33;
}
lean_ctor_set(x_36, 0, x_15);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_33);
x_37 = l_Std_fmt___at_Lean_Meta_instToMessageDataSimpLemma___spec__1(x_1);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_KernelException_toMessageData___closed__15;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__5___closed__2;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_27);
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__5___closed__3;
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_2);
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_39);
x_50 = l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__2;
x_51 = l_Lean_addTrace___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__1(x_50, x_49, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set(x_51, 0, x_15);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_15);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_27);
x_69 = lean_ctor_get(x_29, 1);
lean_inc(x_69);
lean_dec(x_29);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_70 = l_Lean_Meta_Simp_rewrite_synthesizeArgs(x_3, x_1, x_22, x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
uint8_t x_73; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_70);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_70, 0);
lean_dec(x_74);
lean_ctor_set(x_70, 0, x_15);
return x_70;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
lean_dec(x_70);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_15);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
lean_dec(x_70);
x_78 = lean_box(0);
x_79 = l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__4(x_4, x_22, x_25, x_24, x_1, x_2, x_15, x_78, x_5, x_6, x_7, x_8, x_9, x_10, x_77);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_24);
lean_dec(x_22);
return x_79;
}
}
else
{
uint8_t x_80; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_70);
if (x_80 == 0)
{
return x_70;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_70, 0);
x_82 = lean_ctor_get(x_70, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_70);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
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
x_84 = !lean_is_exclusive(x_29);
if (x_84 == 0)
{
return x_29;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_29, 0);
x_86 = lean_ctor_get(x_29, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_29);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
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
x_88 = !lean_is_exclusive(x_18);
if (x_88 == 0)
{
return x_18;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_18, 0);
x_90 = lean_ctor_get(x_18, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_18);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
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
x_92 = !lean_is_exclusive(x_12);
if (x_92 == 0)
{
return x_12;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_12, 0);
x_94 = lean_ctor_get(x_12, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_12);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__1___boxed), 8, 1);
lean_closure_set(x_11, 0, x_3);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__5), 11, 3);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_2);
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__3___rarg), 9, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__4___rarg(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Simp_rewrite_tryLemma_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__2(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_15;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_16;
}
}
lean_object* l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__4(x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
return x_17;
}
}
lean_object* l_Array_insertionSort_swapLoop___at_Lean_Meta_Simp_rewrite___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lean_array_fget(x_1, x_2);
x_9 = lean_array_fget(x_1, x_7);
x_10 = lean_ctor_get(x_8, 2);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_nat_dec_lt(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_dec(x_7);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_13; 
x_13 = lean_array_fswap(x_1, x_2, x_7);
lean_dec(x_2);
x_1 = x_13;
x_2 = x_7;
x_3 = lean_box(0);
goto _start;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_Array_insertionSort_traverse___at_Lean_Meta_Simp_rewrite___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
x_10 = l_Array_insertionSort_swapLoop___at_Lean_Meta_Simp_rewrite___spec__2(x_1, x_2, lean_box(0));
x_11 = lean_nat_add(x_2, x_6);
lean_dec(x_2);
x_1 = x_10;
x_2 = x_11;
x_3 = x_7;
goto _start;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = x_6 < x_5;
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
x_17 = lean_array_uget(x_4, x_6);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_Meta_Simp_rewrite_tryLemma_x3f(x_1, x_2, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; size_t x_21; size_t x_22; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = x_6 + x_21;
lean_inc(x_3);
{
size_t _tmp_5 = x_22;
lean_object* _tmp_6 = x_3;
lean_object* _tmp_13 = x_20;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_14 = _tmp_13;
}
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_18, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_18, 0, x_28);
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_19, 0);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_18, 0, x_32);
return x_18;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_dec(x_18);
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_35 = x_19;
} else {
 lean_dec_ref(x_19);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 1, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_34);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_33);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_18);
if (x_40 == 0)
{
return x_18;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_18, 0);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_18);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
lean_object* l_Lean_Meta_Simp_rewrite___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("no lemmas found for ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_rewrite___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("-rewriting ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_rewrite___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_Simp_rewrite(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_12 = l_Lean_Meta_DiscrTree_getMatch___rarg(x_2, x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
x_16 = l_Array_isEmpty___rarg(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
x_17 = lean_array_get_size(x_13);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Array_insertionSort_traverse___at_Lean_Meta_Simp_rewrite___spec__1(x_13, x_18, x_17);
x_20 = lean_box(0);
x_21 = lean_array_get_size(x_19);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = 0;
x_24 = l_Array_findSomeM_x3f___rarg___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite___spec__3(x_1, x_3, x_24, x_19, x_22, x_23, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
lean_dec(x_19);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_box(0);
x_30 = l_Lean_Meta_Simp_rewrite___lambda__1(x_1, x_20, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_25, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_33);
return x_25;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
lean_dec(x_27);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_25);
if (x_37 == 0)
{
return x_25;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_25, 0);
x_39 = lean_ctor_get(x_25, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_25);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; lean_object* x_42; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_dec(x_13);
lean_dec(x_3);
x_66 = lean_st_ref_get(x_10, x_14);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 3);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_ctor_get_uint8(x_68, sizeof(void*)*1);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec(x_66);
x_71 = 0;
x_41 = x_71;
x_42 = x_70;
goto block_65;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_dec(x_66);
x_73 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__2;
x_74 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__2(x_73, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_unbox(x_75);
lean_dec(x_75);
x_41 = x_77;
x_42 = x_76;
goto block_65;
}
block_65:
{
if (x_41 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
if (lean_is_scalar(x_15)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_15;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_15);
x_46 = l_Lean_stringToMessageData(x_4);
x_47 = l_Lean_Meta_Simp_rewrite___closed__2;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_Meta_Simp_rewrite___closed__4;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_inc(x_1);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_1);
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_KernelException_toMessageData___closed__15;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__2;
x_56 = l_Lean_addTrace___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__1(x_55, x_54, x_5, x_6, x_7, x_8, x_9, x_10, x_42);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_1);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_56, 0, x_60);
return x_56;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_dec(x_56);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_12);
if (x_78 == 0)
{
return x_12;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_12, 0);
x_80 = lean_ctor_get(x_12, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_12);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite___spec__3(x_1, x_2, x_3, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
return x_17;
}
}
lean_object* l_Lean_Meta_Simp_rewrite___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_rewrite___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Meta_Simp_rewrite___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_rewrite(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Simp_preDefault___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("pre");
return x_1;
}
}
lean_object* l_Lean_Meta_Simp_preDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Meta_Simp_preDefault___closed__1;
x_13 = l_Lean_Meta_Simp_rewrite(x_1, x_11, x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_postDefault___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("post");
return x_1;
}
}
lean_object* l_Lean_Meta_Simp_postDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Meta_Simp_postDefault___closed__1;
x_13 = l_Lean_Meta_Simp_rewrite(x_1, x_11, x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Types(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Tactic_Simp_Rewrite(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Types(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Simp_rewrite_getRHS___closed__1 = _init_l_Lean_Meta_Simp_rewrite_getRHS___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_getRHS___closed__1);
l_Lean_Meta_Simp_rewrite_getRHS___closed__2 = _init_l_Lean_Meta_Simp_rewrite_getRHS___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_getRHS___closed__2);
l_Lean_Meta_Simp_rewrite_getRHS___closed__3 = _init_l_Lean_Meta_Simp_rewrite_getRHS___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_getRHS___closed__3);
l_Lean_Meta_Simp_rewrite_getRHS___closed__4 = _init_l_Lean_Meta_Simp_rewrite_getRHS___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_getRHS___closed__4);
l_Lean_Meta_Simp_rewrite_getRHS___closed__5 = _init_l_Lean_Meta_Simp_rewrite_getRHS___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_getRHS___closed__5);
l_Lean_Meta_Simp_rewrite_getRHS___closed__6 = _init_l_Lean_Meta_Simp_rewrite_getRHS___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_getRHS___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__7);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__8);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__9 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__9();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__9);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__10 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__10();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__10);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__11 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__11();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__11);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__12 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__12();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_synthesizeArgs___spec__3___closed__12);
l_Lean_Meta_Simp_rewrite_synthesizeArgs___closed__1 = _init_l_Lean_Meta_Simp_rewrite_synthesizeArgs___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_synthesizeArgs___closed__1);
l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__2___closed__1 = _init_l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__2___closed__1);
l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__1 = _init_l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__1);
l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__2 = _init_l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__2);
l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__3 = _init_l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__3);
l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__4 = _init_l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__3___closed__4);
l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__5___closed__1 = _init_l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__5___closed__1);
l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__5___closed__2 = _init_l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__5___closed__2);
l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__5___closed__3 = _init_l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_tryLemma_x3f___lambda__5___closed__3);
l_Lean_Meta_Simp_rewrite___closed__1 = _init_l_Lean_Meta_Simp_rewrite___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite___closed__1);
l_Lean_Meta_Simp_rewrite___closed__2 = _init_l_Lean_Meta_Simp_rewrite___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite___closed__2);
l_Lean_Meta_Simp_rewrite___closed__3 = _init_l_Lean_Meta_Simp_rewrite___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite___closed__3);
l_Lean_Meta_Simp_rewrite___closed__4 = _init_l_Lean_Meta_Simp_rewrite___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite___closed__4);
l_Lean_Meta_Simp_preDefault___closed__1 = _init_l_Lean_Meta_Simp_preDefault___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_preDefault___closed__1);
l_Lean_Meta_Simp_postDefault___closed__1 = _init_l_Lean_Meta_Simp_postDefault___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_postDefault___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
