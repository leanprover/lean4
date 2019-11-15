// Lean compiler output
// Module: Init.Lean.Meta.Basic
// Imports: Init.Control.Reader Init.Lean.NameGenerator Init.Lean.Environment Init.Lean.LOption Init.Lean.Trace Init.Lean.Class Init.Lean.ReducibilityAttrs Init.Lean.Meta.Exception
#include "runtime/lean.h"
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
lean_object* l_Lean_Meta_withNewLocalInstances___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getExprMVarAssignment(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isReducible(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux(lean_object*);
lean_object* l_Lean_Meta_getTransparency(lean_object*, lean_object*);
lean_object* l_Lean_Meta_dbgTrace___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_2__reduceAll_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVarId___boxed(lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClassQuick___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEnv___boxed(lean_object*);
lean_object* l_Lean_Meta_usingAtLeastTransparency___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallTelescope___spec__1(lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_resettingTypeClassCache___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLCtx(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_2__reduceAll_x3f___boxed(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_forallTelescopeReducing(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_forallTelescope___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_findLevelDepth(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstance___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallTelescope___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwBug___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main(lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_usingTransparency___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_expr_hash(lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_4__getOptions___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_4__getOptions(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConstNoEx(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_savingCache(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_forallTelescope___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConstAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__4(lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_9__lambdaTelescopeAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope(lean_object*);
lean_object* lean_dbg_trace(lean_object*, lean_object*);
lean_object* l_Lean_Meta_TransparencyMode_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwEx___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_dbgTrace___rarg___closed__1;
lean_object* l_Lean_Meta_assignLevelMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClassQuick___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_Inhabited;
lean_object* l_Lean_Meta_mkFreshLevelMVarId___rarg(lean_object*);
lean_object* l_Lean_Meta_throwBug___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_3__reduceReducibleOnly_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Meta_isClassExpensive___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__5(lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_5__getTraceState___boxed(lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_5__getTraceState___rarg(lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_dbgTrace___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_Hashable___boxed(lean_object*);
lean_object* l_Lean_Meta_getMCtx(lean_object*);
lean_object* lean_metavar_ctx_get_expr_assignment(lean_object*, lean_object*);
lean_object* l_Lean_Meta_usingDefault(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_HasBeq___boxed(lean_object*, lean_object*);
lean_object* lean_expr_mk_fvar(lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_tracer___closed__2;
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main(lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_1__whenDebugging___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_Inhabited;
lean_object* l_Lean_Meta_getMVarDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReducible___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MetaM_inhabited___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_tracer___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_InfoCacheKey_HasBeq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReadOnlyLevelMVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshId(lean_object*);
lean_object* l_Lean_Meta_getMCtx___boxed(lean_object*);
lean_object* l_Lean_Meta_isReadOnlyLevelMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstance(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_resettingTypeClassCache(lean_object*);
lean_object* l_Lean_Meta_isClassExpensive(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClassQuickConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_usingTransparency(lean_object*);
lean_object* l_Lean_Meta_getConstAux(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEnv(lean_object*);
lean_object* l_Lean_Meta_throwEx___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_assign_expr(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshId___rarg(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Meta_isClassExpensive___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ParamInfo_inhabited;
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__4___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope(lean_object*);
lean_object* l_Lean_Meta_getTransparency___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprMVarAssigned(lean_object*, lean_object*, lean_object*);
size_t l_Lean_Meta_InfoCacheKey_Hashable(lean_object*);
lean_object* l_Lean_Meta_tracer;
lean_object* l_Lean_Meta_isExprMVarAssigned___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallTelescope___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClassExpensive___main___closed__1;
lean_object* l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClassQuick(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_9__lambdaTelescopeAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateMVars(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__4___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_5__getTraceState(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Meta_dbgTrace___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
size_t l_Option_hash___at_Lean_Meta_InfoCacheKey_Hashable___spec__1(lean_object*);
lean_object* l_Lean_Meta_getConfig(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticExprMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ParamInfo_inhabited___closed__1;
lean_object* l_Lean_Meta_instantiateLevelMVars___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEnv___rarg(lean_object*);
lean_object* l_Lean_Meta_instantiateLevelMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances(lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_throwBug(lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_8__forallTelescopeReducingAux(lean_object*);
lean_object* l_Lean_Meta_usingTransparency___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getExprMVarAssignment___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
size_t lean_usize_mix_hash(size_t, size_t);
lean_object* l_Lean_Meta_tracer___closed__1;
lean_object* l_Lean_Meta_forallTelescope(lean_object*);
uint8_t lean_is_class(lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_HashMap_Inhabited___closed__1;
lean_object* l___private_Init_Lean_Meta_Basic_6__liftMkBindingM(lean_object*);
lean_object* l_Lean_Meta_mkFreshId___boxed(lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_8__forallTelescopeReducingAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConstNoEx___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_EIO_Monad___closed__1;
uint8_t lean_metavar_ctx_is_expr_assigned(lean_object*, lean_object*);
lean_object* l_Lean_Meta_dbgTrace(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Exception_Inhabited___closed__1;
lean_object* l___private_Init_Lean_Meta_Basic_6__liftMkBindingM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_1__whenDebugging(lean_object*);
lean_object* l_Lean_Meta_getConst___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_usingAtLeastTransparency(lean_object*);
lean_object* l_Lean_Meta_getLCtx___boxed(lean_object*, lean_object*);
lean_object* lean_metavar_ctx_find_decl(lean_object*, lean_object*);
lean_object* l_Lean_Meta_tracer___closed__4;
lean_object* l_Lean_Meta_liftStateMCtx(lean_object*);
lean_object* l_Lean_Meta_tracer___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_Inhabited___closed__1;
lean_object* l_Lean_Meta_forallBoundedTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MetaM_inhabited(lean_object*, lean_object*);
lean_object* l_Lean_Meta_TransparencyMode_Hashable___closed__1;
extern lean_object* l_Lean_Expr_inhabited___closed__1;
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwEx(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Option_hash___at_Lean_Meta_InfoCacheKey_Hashable___spec__1___boxed(lean_object*);
lean_object* l_Lean_Meta_TransparencyMode_hash___boxed(lean_object*);
lean_object* l_Lean_Meta_isClassQuick___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticExprMVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_addLevelMVarDecl(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVarId(lean_object*);
uint8_t lean_expr_has_expr_mvar(lean_object*);
lean_object* l_Lean_Meta_tracer___closed__3;
lean_object* l_Lean_Meta_liftStateMCtx___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__4___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_liftStateMCtx___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMCtx___rarg(lean_object*);
size_t l_Lean_Meta_TransparencyMode_hash(uint8_t);
lean_object* l_Lean_Meta_isClassQuickConst___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_TransparencyMode_HasBeq;
lean_object* l_Lean_Meta_TransparencyMode_Hashable;
lean_object* l_Lean_Meta_TransparencyMode_lt___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
lean_object* lean_metavar_ctx_assign_level(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_9__lambdaTelescopeAux___main(lean_object*);
lean_object* l_Lean_Meta_TransparencyMode_HasBeq___closed__1;
lean_object* l_Lean_Meta_savingCache___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_usingAtLeastTransparency___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_3__reduceReducibleOnly_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isReducible(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__2(lean_object*);
lean_object* l_Lean_Meta_isClassExpensive___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_9__lambdaTelescopeAux(lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___at_Lean_MetavarContext_mkBinding___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MetaM_inhabited___rarg(lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_level_mvar(lean_object*);
uint8_t _init_l_Lean_Meta_TransparencyMode_Inhabited() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
uint8_t l_Lean_Meta_TransparencyMode_beq(uint8_t x_1, uint8_t x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; 
x_3 = lean_box(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
}
case 1:
{
lean_object* x_6; 
x_6 = lean_box(x_2);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 0;
return x_8;
}
}
default: 
{
lean_object* x_9; 
x_9 = lean_box(x_2);
if (lean_obj_tag(x_9) == 2)
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = 0;
return x_11;
}
}
}
}
}
lean_object* l_Lean_Meta_TransparencyMode_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_TransparencyMode_beq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* _init_l_Lean_Meta_TransparencyMode_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_TransparencyMode_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_TransparencyMode_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_TransparencyMode_HasBeq___closed__1;
return x_1;
}
}
size_t l_Lean_Meta_TransparencyMode_hash(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
size_t x_2; 
x_2 = 7;
return x_2;
}
case 1:
{
size_t x_3; 
x_3 = 11;
return x_3;
}
default: 
{
size_t x_4; 
x_4 = 13;
return x_4;
}
}
}
}
lean_object* l_Lean_Meta_TransparencyMode_hash___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_TransparencyMode_hash(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_TransparencyMode_Hashable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_TransparencyMode_hash___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_TransparencyMode_Hashable() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_TransparencyMode_Hashable___closed__1;
return x_1;
}
}
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t x_1, uint8_t x_2) {
_start:
{
switch (x_1) {
case 0:
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
case 1:
{
lean_object* x_4; 
x_4 = lean_box(x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
}
default: 
{
lean_object* x_7; 
x_7 = lean_box(x_2);
if (lean_obj_tag(x_7) == 2)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 1;
return x_9;
}
}
}
}
}
lean_object* l_Lean_Meta_TransparencyMode_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_TransparencyMode_lt(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* _init_l_Lean_Meta_ParamInfo_inhabited___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 1, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 2, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 3, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_ParamInfo_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_ParamInfo_inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Meta_InfoCacheKey_Inhabited___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 1;
x_3 = l_Lean_Expr_inhabited___closed__1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_InfoCacheKey_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_InfoCacheKey_Inhabited___closed__1;
return x_1;
}
}
size_t l_Option_hash___at_Lean_Meta_InfoCacheKey_Hashable___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
size_t x_2; 
x_2 = 11;
return x_2;
}
else
{
lean_object* x_3; size_t x_4; size_t x_5; size_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_usize_of_nat(x_3);
x_5 = 13;
x_6 = lean_usize_mix_hash(x_4, x_5);
return x_6;
}
}
}
size_t l_Lean_Meta_InfoCacheKey_Hashable(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; size_t x_8; size_t x_9; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Meta_TransparencyMode_hash(x_2);
x_6 = lean_expr_hash(x_3);
x_7 = l_Option_hash___at_Lean_Meta_InfoCacheKey_Hashable___spec__1(x_4);
x_8 = lean_usize_mix_hash(x_6, x_7);
x_9 = lean_usize_mix_hash(x_5, x_8);
return x_9;
}
}
lean_object* l_Option_hash___at_Lean_Meta_InfoCacheKey_Hashable___spec__1___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Option_hash___at_Lean_Meta_InfoCacheKey_Hashable___spec__1(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_InfoCacheKey_Hashable___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_InfoCacheKey_Hashable(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
uint8_t l_Lean_Meta_InfoCacheKey_HasBeq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_Lean_Meta_TransparencyMode_beq(x_3, x_6);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
else
{
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_11; 
x_11 = lean_expr_eqv(x_4, x_7);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
else
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_nat_dec_eq(x_14, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_expr_eqv(x_4, x_7);
return x_18;
}
}
}
}
}
}
lean_object* l_Lean_Meta_InfoCacheKey_HasBeq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_InfoCacheKey_HasBeq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_MetaM_inhabited___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Exception_Inhabited___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_MetaM_inhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_MetaM_inhabited___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Meta_MetaM_inhabited___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_MetaM_inhabited(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_getLCtx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_getLCtx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_getLCtx(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_getConfig(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_getConfig___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_getConfig(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_getMCtx___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_getMCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getMCtx___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getMCtx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_getMCtx(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_getEnv___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_getEnv(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_getEnv___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getEnv___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_getEnv(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_throwEx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
lean_object* l_Lean_Meta_throwEx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_throwEx___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_throwEx___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_throwEx___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_throwBug___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
lean_object* l_Lean_Meta_throwBug(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_throwBug___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_throwBug___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_throwBug___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_1__whenDebugging___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 3);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
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
}
lean_object* l___private_Init_Lean_Meta_Basic_1__whenDebugging(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Basic_1__whenDebugging___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkFreshId___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
x_7 = lean_name_mk_numeral(x_5, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_1);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_12);
lean_inc(x_11);
x_13 = lean_name_mk_numeral(x_11, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_12, x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_1, 3, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_1);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_1, 3);
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 4);
x_23 = lean_ctor_get(x_1, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_18);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
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
lean_inc(x_25);
lean_inc(x_24);
x_27 = lean_name_mk_numeral(x_24, x_25);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_25, x_28);
lean_dec(x_25);
if (lean_is_scalar(x_26)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_26;
}
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set(x_31, 2, x_21);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set(x_31, 4, x_22);
lean_ctor_set(x_31, 5, x_23);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
lean_object* l_Lean_Meta_mkFreshId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshId___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkFreshId___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_mkFreshId(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_2__reduceAll_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 4);
x_5 = 0;
x_6 = l_Lean_Meta_TransparencyMode_beq(x_4, x_5);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_2__reduceAll_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Meta_Basic_2__reduceAll_x3f(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_3__reduceReducibleOnly_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 4);
x_5 = 2;
x_6 = l_Lean_Meta_TransparencyMode_beq(x_4, x_5);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_3__reduceReducibleOnly_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Meta_Basic_3__reduceReducibleOnly_x3f(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_getTransparency(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 4);
x_5 = lean_box(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_getTransparency___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_getTransparency(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_4__getOptions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_4__getOptions___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Meta_Basic_4__getOptions(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_isReducible(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_isReducible(x_4, x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
lean_object* l_Lean_Meta_isReducible___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isReducible(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_usingTransparency___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_ctor_set_uint8(x_6, sizeof(void*)*1 + 4, x_1);
x_8 = lean_apply_2(x_2, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_11 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
x_12 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 2);
x_13 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 3);
lean_inc(x_9);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_10);
lean_ctor_set_uint8(x_14, sizeof(void*)*1 + 1, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*1 + 2, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1 + 3, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*1 + 4, x_1);
lean_ctor_set(x_3, 0, x_14);
x_15 = lean_apply_2(x_2, x_3, x_4);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_3, 2);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_3);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
x_21 = lean_ctor_get_uint8(x_16, sizeof(void*)*1 + 1);
x_22 = lean_ctor_get_uint8(x_16, sizeof(void*)*1 + 2);
x_23 = lean_ctor_get_uint8(x_16, sizeof(void*)*1 + 3);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_24 = x_16;
} else {
 lean_dec_ref(x_16);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 1, 5);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_20);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 1, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 2, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 3, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 4, x_1);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_17);
lean_ctor_set(x_26, 2, x_18);
x_27 = lean_apply_2(x_2, x_26, x_4);
return x_27;
}
}
}
lean_object* l_Lean_Meta_usingTransparency(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_usingTransparency___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_usingTransparency___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Meta_usingTransparency___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Meta_usingAtLeastTransparency___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
uint8_t x_8; uint8_t x_9; 
x_8 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 4);
x_9 = l_Lean_Meta_TransparencyMode_lt(x_8, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_apply_2(x_2, x_3, x_4);
return x_10;
}
else
{
lean_object* x_11; 
lean_ctor_set_uint8(x_6, sizeof(void*)*1 + 4, x_1);
x_11 = lean_apply_2(x_2, x_3, x_4);
return x_11;
}
}
else
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_14 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
x_15 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 2);
x_16 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 3);
x_17 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 4);
lean_inc(x_12);
lean_dec(x_6);
x_18 = l_Lean_Meta_TransparencyMode_lt(x_17, x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_13);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 1, x_14);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 2, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 3, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 4, x_17);
lean_ctor_set(x_3, 0, x_19);
x_20 = lean_apply_2(x_2, x_3, x_4);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_13);
lean_ctor_set_uint8(x_21, sizeof(void*)*1 + 1, x_14);
lean_ctor_set_uint8(x_21, sizeof(void*)*1 + 2, x_15);
lean_ctor_set_uint8(x_21, sizeof(void*)*1 + 3, x_16);
lean_ctor_set_uint8(x_21, sizeof(void*)*1 + 4, x_1);
lean_ctor_set(x_3, 0, x_21);
x_22 = lean_apply_2(x_2, x_3, x_4);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
x_25 = lean_ctor_get(x_3, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
x_28 = lean_ctor_get_uint8(x_23, sizeof(void*)*1 + 1);
x_29 = lean_ctor_get_uint8(x_23, sizeof(void*)*1 + 2);
x_30 = lean_ctor_get_uint8(x_23, sizeof(void*)*1 + 3);
x_31 = lean_ctor_get_uint8(x_23, sizeof(void*)*1 + 4);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_32 = x_23;
} else {
 lean_dec_ref(x_23);
 x_32 = lean_box(0);
}
x_33 = l_Lean_Meta_TransparencyMode_lt(x_31, x_1);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 1, 5);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_27);
lean_ctor_set_uint8(x_34, sizeof(void*)*1 + 1, x_28);
lean_ctor_set_uint8(x_34, sizeof(void*)*1 + 2, x_29);
lean_ctor_set_uint8(x_34, sizeof(void*)*1 + 3, x_30);
lean_ctor_set_uint8(x_34, sizeof(void*)*1 + 4, x_31);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_35, 2, x_25);
x_36 = lean_apply_2(x_2, x_35, x_4);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
if (lean_is_scalar(x_32)) {
 x_37 = lean_alloc_ctor(0, 1, 5);
} else {
 x_37 = x_32;
}
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_27);
lean_ctor_set_uint8(x_37, sizeof(void*)*1 + 1, x_28);
lean_ctor_set_uint8(x_37, sizeof(void*)*1 + 2, x_29);
lean_ctor_set_uint8(x_37, sizeof(void*)*1 + 3, x_30);
lean_ctor_set_uint8(x_37, sizeof(void*)*1 + 4, x_1);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_24);
lean_ctor_set(x_38, 2, x_25);
x_39 = lean_apply_2(x_2, x_38, x_4);
return x_39;
}
}
}
}
lean_object* l_Lean_Meta_usingAtLeastTransparency(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_usingAtLeastTransparency___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_usingAtLeastTransparency___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Meta_usingAtLeastTransparency___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticExprMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_5);
x_6 = lean_metavar_ctx_find_decl(x_5, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 3);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
else
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_5);
x_22 = 1;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
return x_24;
}
}
}
}
lean_object* l_Lean_Meta_isReadOnlyOrSyntheticExprMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isReadOnlyOrSyntheticExprMVar(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_isReadOnlyLevelMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = l_Lean_MetavarContext_findLevelDepth(x_5, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
else
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
}
}
}
lean_object* l_Lean_Meta_isReadOnlyLevelMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isReadOnlyLevelMVar(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_isExprMVarAssigned(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_metavar_ctx_is_expr_assigned(x_4, x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
lean_object* l_Lean_Meta_isExprMVarAssigned___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isExprMVarAssigned(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_getExprMVarAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_metavar_ctx_get_expr_assignment(x_4, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_Meta_getExprMVarAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getExprMVarAssignment(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_assignExprMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get_uint8(x_22, sizeof(void*)*1 + 3);
if (x_23 == 0)
{
x_5 = x_4;
goto block_21;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_inc(x_1);
x_25 = lean_metavar_ctx_is_expr_assigned(x_24, x_1);
if (x_25 == 0)
{
x_5 = x_4;
goto block_21;
}
else
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_2);
x_26 = l_Lean_Meta_throwBug___rarg(x_1, x_3, x_4);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
block_21:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_metavar_ctx_assign_expr(x_7, x_1, x_2);
lean_ctor_set(x_5, 1, x_8);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 2);
x_14 = lean_ctor_get(x_5, 3);
x_15 = lean_ctor_get(x_5, 4);
x_16 = lean_ctor_get(x_5, 5);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_17 = lean_metavar_ctx_assign_expr(x_12, x_1, x_2);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_13);
lean_ctor_set(x_18, 3, x_14);
lean_ctor_set(x_18, 4, x_15);
lean_ctor_set(x_18, 5, x_16);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
}
lean_object* l_Lean_Meta_assignExprMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_assignExprMVar(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Meta_dbgTrace___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Meta_dbgTrace___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_dbgTrace___rarg___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_dbgTrace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_apply_1(x_1, x_2);
x_6 = l_Lean_Meta_dbgTrace___rarg___closed__1;
x_7 = lean_dbg_trace(x_5, x_6);
x_8 = lean_apply_2(x_7, x_3, x_4);
return x_8;
}
}
lean_object* l_Lean_Meta_dbgTrace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_dbgTrace___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_dbgTrace___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_dbgTrace___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_5__getTraceState___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_5__getTraceState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Basic_5__getTraceState___rarg), 1, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_5__getTraceState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Meta_Basic_5__getTraceState(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_tracer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 4);
x_6 = lean_apply_1(x_1, x_5);
lean_ctor_set(x_3, 4, x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get(x_3, 4);
x_14 = lean_ctor_get(x_3, 5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_15 = lean_apply_1(x_1, x_13);
x_16 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_15);
lean_ctor_set(x_16, 5, x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
lean_object* _init_l_Lean_Meta_tracer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Basic_4__getOptions___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_tracer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_tracer___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_tracer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Basic_5__getTraceState___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_tracer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_tracer___closed__1;
x_2 = l_Lean_Meta_tracer___closed__2;
x_3 = l_Lean_Meta_tracer___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_tracer() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_tracer___closed__4;
return x_1;
}
}
lean_object* l_Lean_Meta_tracer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_tracer___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_getConstAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_5);
x_7 = lean_environment_find(x_5, x_1);
if (lean_obj_tag(x_7) == 0)
{
if (x_2 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_6);
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 2)
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 4);
x_16 = 0;
x_17 = l_Lean_Meta_TransparencyMode_beq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_4);
return x_20;
}
}
else
{
lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; 
lean_dec(x_13);
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*1 + 4);
x_23 = 2;
x_24 = l_Lean_Meta_TransparencyMode_beq(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_5);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_4);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = l_Lean_isReducible(x_5, x_1);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_7);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
return x_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_4);
return x_29;
}
}
}
}
}
}
lean_object* l_Lean_Meta_getConstAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Meta_getConstAux(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Meta_getConst(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = 1;
x_5 = l_Lean_Meta_getConstAux(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Meta_getConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getConst(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_getConstNoEx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = l_Lean_Meta_getConstAux(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Meta_getConstNoEx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getConstNoEx(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_getLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_4);
x_5 = lean_local_ctx_find(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_4);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_Lean_Meta_getMVarDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_5);
x_6 = lean_metavar_ctx_find_decl(x_5, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_Lean_Meta_getMVarDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getMVarDecl(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_instantiateMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_expr_has_expr_mvar(x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = lean_expr_has_level_mvar(x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_Lean_MetavarContext_instantiateMVars(x_8, x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_ctor_set(x_3, 1, x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_19 = l_Lean_MetavarContext_instantiateMVars(x_14, x_1);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_15);
lean_ctor_set(x_22, 3, x_16);
lean_ctor_set(x_22, 4, x_17);
lean_ctor_set(x_22, 5, x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_3, 1);
x_26 = l_Lean_MetavarContext_instantiateMVars(x_25, x_1);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_ctor_set(x_3, 1, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_3, 0);
x_31 = lean_ctor_get(x_3, 1);
x_32 = lean_ctor_get(x_3, 2);
x_33 = lean_ctor_get(x_3, 3);
x_34 = lean_ctor_get(x_3, 4);
x_35 = lean_ctor_get(x_3, 5);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_3);
x_36 = l_Lean_MetavarContext_instantiateMVars(x_31, x_1);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_32);
lean_ctor_set(x_39, 3, x_33);
lean_ctor_set(x_39, 4, x_34);
lean_ctor_set(x_39, 5, x_35);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* l_Lean_Meta_instantiateMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_instantiateMVars(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_6__liftMkBindingM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 3);
x_9 = l_HashMap_Inhabited___closed__1;
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
lean_inc(x_4);
x_11 = lean_apply_2(x_1, x_4, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_4);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_ctor_set(x_3, 3, x_15);
lean_ctor_set(x_3, 1, x_14);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_ctor_set(x_3, 3, x_19);
lean_ctor_set(x_3, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_11, 1);
x_24 = lean_ctor_get(x_11, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_21, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_21, 3);
lean_inc(x_28);
lean_dec(x_21);
lean_inc(x_6);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_26);
x_30 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
lean_ctor_set(x_3, 3, x_32);
lean_ctor_set(x_3, 1, x_31);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_11, 0, x_30);
return x_11;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_ctor_get(x_11, 1);
lean_inc(x_33);
lean_dec(x_11);
x_34 = lean_ctor_get(x_21, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_21, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_21, 3);
lean_inc(x_37);
lean_dec(x_21);
lean_inc(x_6);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_6);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_35);
x_39 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_ctor_get(x_33, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_dec(x_33);
lean_ctor_set(x_3, 3, x_41);
lean_ctor_set(x_3, 1, x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_3);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_11);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_11, 1);
x_45 = lean_ctor_get(x_11, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_dec(x_21);
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
lean_inc(x_47);
lean_inc(x_6);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_6);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_4);
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_dec(x_44);
lean_ctor_set(x_3, 3, x_50);
lean_ctor_set(x_3, 1, x_47);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_11, 0, x_49);
return x_11;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_11, 1);
lean_inc(x_51);
lean_dec(x_11);
x_52 = lean_ctor_get(x_21, 1);
lean_inc(x_52);
lean_dec(x_21);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_inc(x_53);
lean_inc(x_6);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_6);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_4);
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_dec(x_51);
lean_ctor_set(x_3, 3, x_56);
lean_ctor_set(x_3, 1, x_53);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_3);
return x_57;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_ctor_get(x_3, 0);
x_59 = lean_ctor_get(x_3, 1);
x_60 = lean_ctor_get(x_3, 2);
x_61 = lean_ctor_get(x_3, 3);
x_62 = lean_ctor_get(x_3, 4);
x_63 = lean_ctor_get(x_3, 5);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_3);
x_64 = l_HashMap_Inhabited___closed__1;
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_61);
lean_ctor_set(x_65, 2, x_64);
lean_inc(x_4);
x_66 = lean_apply_2(x_1, x_4, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_4);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
 x_69 = lean_box(0);
}
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_72, 0, x_58);
lean_ctor_set(x_72, 1, x_70);
lean_ctor_set(x_72, 2, x_60);
lean_ctor_set(x_72, 3, x_71);
lean_ctor_set(x_72, 4, x_62);
lean_ctor_set(x_72, 5, x_63);
if (lean_is_scalar(x_69)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_69;
}
lean_ctor_set(x_73, 0, x_67);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
else
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_66, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_4);
x_75 = lean_ctor_get(x_66, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_76 = x_66;
} else {
 lean_dec_ref(x_66);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_74, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_74, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_74, 3);
lean_inc(x_80);
lean_dec(x_74);
lean_inc(x_58);
x_81 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_81, 0, x_58);
lean_ctor_set(x_81, 1, x_77);
lean_ctor_set(x_81, 2, x_78);
x_82 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
lean_ctor_set(x_82, 2, x_81);
x_83 = lean_ctor_get(x_75, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_75, 1);
lean_inc(x_84);
lean_dec(x_75);
x_85 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_85, 0, x_58);
lean_ctor_set(x_85, 1, x_83);
lean_ctor_set(x_85, 2, x_60);
lean_ctor_set(x_85, 3, x_84);
lean_ctor_set(x_85, 4, x_62);
lean_ctor_set(x_85, 5, x_63);
if (lean_is_scalar(x_76)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_76;
}
lean_ctor_set(x_86, 0, x_82);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_87 = lean_ctor_get(x_66, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_88 = x_66;
} else {
 lean_dec_ref(x_66);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_74, 1);
lean_inc(x_89);
lean_dec(x_74);
x_90 = lean_ctor_get(x_87, 0);
lean_inc(x_90);
lean_inc(x_90);
lean_inc(x_58);
x_91 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_91, 0, x_58);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_91, 2, x_4);
x_92 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
lean_dec(x_87);
x_94 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_94, 0, x_58);
lean_ctor_set(x_94, 1, x_90);
lean_ctor_set(x_94, 2, x_60);
lean_ctor_set(x_94, 3, x_93);
lean_ctor_set(x_94, 4, x_62);
lean_ctor_set(x_94, 5, x_63);
if (lean_is_scalar(x_88)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_88;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Basic_6__liftMkBindingM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Basic_6__liftMkBindingM___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Array_isEmpty___rarg(x_1);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 3);
x_11 = l_HashMap_Inhabited___closed__1;
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
x_13 = 0;
lean_inc(x_6);
x_14 = l_Lean_MetavarContext_MkBinding_mkBinding___at_Lean_MetavarContext_mkBinding___spec__1(x_13, x_6, x_1, x_2, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_ctor_set(x_4, 3, x_18);
lean_ctor_set(x_4, 1, x_17);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_ctor_set(x_4, 3, x_22);
lean_ctor_set(x_4, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_4);
return x_23;
}
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_14, 1);
x_27 = lean_ctor_get(x_14, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_24, 3);
lean_inc(x_31);
lean_dec(x_24);
lean_inc(x_8);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_8);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_32, 2, x_29);
x_33 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_ctor_get(x_26, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
lean_ctor_set(x_4, 3, x_35);
lean_ctor_set(x_4, 1, x_34);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 0, x_33);
return x_14;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
lean_dec(x_14);
x_37 = lean_ctor_get(x_24, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_24, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_24, 3);
lean_inc(x_40);
lean_dec(x_24);
lean_inc(x_8);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_8);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 2, x_38);
x_42 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_dec(x_36);
lean_ctor_set(x_4, 3, x_44);
lean_ctor_set(x_4, 1, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_4);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_14);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_14, 1);
x_48 = lean_ctor_get(x_14, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_24, 1);
lean_inc(x_49);
lean_dec(x_24);
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_inc(x_50);
lean_inc(x_8);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_8);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_6);
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_dec(x_47);
lean_ctor_set(x_4, 3, x_53);
lean_ctor_set(x_4, 1, x_50);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 0, x_52);
return x_14;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_14, 1);
lean_inc(x_54);
lean_dec(x_14);
x_55 = lean_ctor_get(x_24, 1);
lean_inc(x_55);
lean_dec(x_24);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_inc(x_56);
lean_inc(x_8);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_8);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_6);
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
lean_ctor_set(x_4, 3, x_59);
lean_ctor_set(x_4, 1, x_56);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_4);
return x_60;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_61 = lean_ctor_get(x_4, 0);
x_62 = lean_ctor_get(x_4, 1);
x_63 = lean_ctor_get(x_4, 2);
x_64 = lean_ctor_get(x_4, 3);
x_65 = lean_ctor_get(x_4, 4);
x_66 = lean_ctor_get(x_4, 5);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_4);
x_67 = l_HashMap_Inhabited___closed__1;
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_64);
lean_ctor_set(x_68, 2, x_67);
x_69 = 0;
lean_inc(x_6);
x_70 = l_Lean_MetavarContext_MkBinding_mkBinding___at_Lean_MetavarContext_mkBinding___spec__1(x_69, x_6, x_1, x_2, x_68);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_6);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_76 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_76, 0, x_61);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 2, x_63);
lean_ctor_set(x_76, 3, x_75);
lean_ctor_set(x_76, 4, x_65);
lean_ctor_set(x_76, 5, x_66);
if (lean_is_scalar(x_73)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_73;
}
lean_ctor_set(x_77, 0, x_71);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
else
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_70, 0);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_6);
x_79 = lean_ctor_get(x_70, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_80 = x_70;
} else {
 lean_dec_ref(x_70);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_78, 2);
lean_inc(x_83);
x_84 = lean_ctor_get(x_78, 3);
lean_inc(x_84);
lean_dec(x_78);
lean_inc(x_61);
x_85 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_85, 0, x_61);
lean_ctor_set(x_85, 1, x_81);
lean_ctor_set(x_85, 2, x_82);
x_86 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
lean_ctor_set(x_86, 2, x_85);
x_87 = lean_ctor_get(x_79, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_79, 1);
lean_inc(x_88);
lean_dec(x_79);
x_89 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_89, 0, x_61);
lean_ctor_set(x_89, 1, x_87);
lean_ctor_set(x_89, 2, x_63);
lean_ctor_set(x_89, 3, x_88);
lean_ctor_set(x_89, 4, x_65);
lean_ctor_set(x_89, 5, x_66);
if (lean_is_scalar(x_80)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_80;
}
lean_ctor_set(x_90, 0, x_86);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_91 = lean_ctor_get(x_70, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_92 = x_70;
} else {
 lean_dec_ref(x_70);
 x_92 = lean_box(0);
}
x_93 = lean_ctor_get(x_78, 1);
lean_inc(x_93);
lean_dec(x_78);
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_94);
lean_inc(x_94);
lean_inc(x_61);
x_95 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_95, 0, x_61);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_95, 2, x_6);
x_96 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_ctor_get(x_91, 1);
lean_inc(x_97);
lean_dec(x_91);
x_98 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_98, 0, x_61);
lean_ctor_set(x_98, 1, x_94);
lean_ctor_set(x_98, 2, x_63);
lean_ctor_set(x_98, 3, x_97);
lean_ctor_set(x_98, 4, x_65);
lean_ctor_set(x_98, 5, x_66);
if (lean_is_scalar(x_92)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_92;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
else
{
lean_object* x_100; 
lean_dec(x_3);
lean_dec(x_1);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_2);
lean_ctor_set(x_100, 1, x_4);
return x_100;
}
}
}
lean_object* l_Lean_Meta_mkLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Array_isEmpty___rarg(x_1);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 3);
x_11 = l_HashMap_Inhabited___closed__1;
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
x_13 = 1;
lean_inc(x_6);
x_14 = l_Lean_MetavarContext_MkBinding_mkBinding___at_Lean_MetavarContext_mkBinding___spec__1(x_13, x_6, x_1, x_2, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_ctor_set(x_4, 3, x_18);
lean_ctor_set(x_4, 1, x_17);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_ctor_set(x_4, 3, x_22);
lean_ctor_set(x_4, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_4);
return x_23;
}
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_14, 1);
x_27 = lean_ctor_get(x_14, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_24, 3);
lean_inc(x_31);
lean_dec(x_24);
lean_inc(x_8);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_8);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_32, 2, x_29);
x_33 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_ctor_get(x_26, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
lean_ctor_set(x_4, 3, x_35);
lean_ctor_set(x_4, 1, x_34);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 0, x_33);
return x_14;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
lean_dec(x_14);
x_37 = lean_ctor_get(x_24, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_24, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_24, 3);
lean_inc(x_40);
lean_dec(x_24);
lean_inc(x_8);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_8);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 2, x_38);
x_42 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_dec(x_36);
lean_ctor_set(x_4, 3, x_44);
lean_ctor_set(x_4, 1, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_4);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_14);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_14, 1);
x_48 = lean_ctor_get(x_14, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_24, 1);
lean_inc(x_49);
lean_dec(x_24);
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_inc(x_50);
lean_inc(x_8);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_8);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_6);
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_dec(x_47);
lean_ctor_set(x_4, 3, x_53);
lean_ctor_set(x_4, 1, x_50);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 0, x_52);
return x_14;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_14, 1);
lean_inc(x_54);
lean_dec(x_14);
x_55 = lean_ctor_get(x_24, 1);
lean_inc(x_55);
lean_dec(x_24);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_inc(x_56);
lean_inc(x_8);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_8);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_6);
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
lean_ctor_set(x_4, 3, x_59);
lean_ctor_set(x_4, 1, x_56);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_4);
return x_60;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_61 = lean_ctor_get(x_4, 0);
x_62 = lean_ctor_get(x_4, 1);
x_63 = lean_ctor_get(x_4, 2);
x_64 = lean_ctor_get(x_4, 3);
x_65 = lean_ctor_get(x_4, 4);
x_66 = lean_ctor_get(x_4, 5);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_4);
x_67 = l_HashMap_Inhabited___closed__1;
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_64);
lean_ctor_set(x_68, 2, x_67);
x_69 = 1;
lean_inc(x_6);
x_70 = l_Lean_MetavarContext_MkBinding_mkBinding___at_Lean_MetavarContext_mkBinding___spec__1(x_69, x_6, x_1, x_2, x_68);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_6);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_76 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_76, 0, x_61);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 2, x_63);
lean_ctor_set(x_76, 3, x_75);
lean_ctor_set(x_76, 4, x_65);
lean_ctor_set(x_76, 5, x_66);
if (lean_is_scalar(x_73)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_73;
}
lean_ctor_set(x_77, 0, x_71);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
else
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_70, 0);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_6);
x_79 = lean_ctor_get(x_70, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_80 = x_70;
} else {
 lean_dec_ref(x_70);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_78, 2);
lean_inc(x_83);
x_84 = lean_ctor_get(x_78, 3);
lean_inc(x_84);
lean_dec(x_78);
lean_inc(x_61);
x_85 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_85, 0, x_61);
lean_ctor_set(x_85, 1, x_81);
lean_ctor_set(x_85, 2, x_82);
x_86 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
lean_ctor_set(x_86, 2, x_85);
x_87 = lean_ctor_get(x_79, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_79, 1);
lean_inc(x_88);
lean_dec(x_79);
x_89 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_89, 0, x_61);
lean_ctor_set(x_89, 1, x_87);
lean_ctor_set(x_89, 2, x_63);
lean_ctor_set(x_89, 3, x_88);
lean_ctor_set(x_89, 4, x_65);
lean_ctor_set(x_89, 5, x_66);
if (lean_is_scalar(x_80)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_80;
}
lean_ctor_set(x_90, 0, x_86);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_91 = lean_ctor_get(x_70, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_92 = x_70;
} else {
 lean_dec_ref(x_70);
 x_92 = lean_box(0);
}
x_93 = lean_ctor_get(x_78, 1);
lean_inc(x_93);
lean_dec(x_78);
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_94);
lean_inc(x_94);
lean_inc(x_61);
x_95 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_95, 0, x_61);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_95, 2, x_6);
x_96 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_ctor_get(x_91, 1);
lean_inc(x_97);
lean_dec(x_91);
x_98 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_98, 0, x_61);
lean_ctor_set(x_98, 1, x_94);
lean_ctor_set(x_98, 2, x_63);
lean_ctor_set(x_98, 3, x_97);
lean_ctor_set(x_98, 4, x_65);
lean_ctor_set(x_98, 5, x_66);
if (lean_is_scalar(x_92)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_92;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
else
{
lean_object* x_100; 
lean_dec(x_3);
lean_dec(x_1);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_2);
lean_ctor_set(x_100, 1, x_4);
return x_100;
}
}
}
lean_object* l_Lean_Meta_savingCache___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
x_5 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 2);
lean_dec(x_9);
lean_ctor_set(x_7, 2, x_4);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_7, 3);
x_13 = lean_ctor_get(x_7, 4);
x_14 = lean_ctor_get(x_7, 5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_4);
lean_ctor_set(x_15, 3, x_12);
lean_ctor_set(x_15, 4, x_13);
lean_ctor_set(x_15, 5, x_14);
lean_ctor_set(x_5, 1, x_15);
return x_5;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_16, 4);
lean_inc(x_21);
x_22 = lean_ctor_get(x_16, 5);
lean_inc(x_22);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 lean_ctor_release(x_16, 4);
 lean_ctor_release(x_16, 5);
 x_23 = x_16;
} else {
 lean_dec_ref(x_16);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(0, 6, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 2, x_4);
lean_ctor_set(x_24, 3, x_20);
lean_ctor_set(x_24, 4, x_21);
lean_ctor_set(x_24, 5, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_5, 1);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 2);
lean_dec(x_29);
lean_ctor_set(x_27, 2, x_4);
return x_5;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_ctor_get(x_27, 1);
x_32 = lean_ctor_get(x_27, 3);
x_33 = lean_ctor_get(x_27, 4);
x_34 = lean_ctor_get(x_27, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_27);
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_35, 2, x_4);
lean_ctor_set(x_35, 3, x_32);
lean_ctor_set(x_35, 4, x_33);
lean_ctor_set(x_35, 5, x_34);
lean_ctor_set(x_5, 1, x_35);
return x_5;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_5, 1);
x_37 = lean_ctor_get(x_5, 0);
lean_inc(x_36);
lean_inc(x_37);
lean_dec(x_5);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_36, 3);
lean_inc(x_40);
x_41 = lean_ctor_get(x_36, 4);
lean_inc(x_41);
x_42 = lean_ctor_get(x_36, 5);
lean_inc(x_42);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 lean_ctor_release(x_36, 3);
 lean_ctor_release(x_36, 4);
 lean_ctor_release(x_36, 5);
 x_43 = x_36;
} else {
 lean_dec_ref(x_36);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 6, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_39);
lean_ctor_set(x_44, 2, x_4);
lean_ctor_set(x_44, 3, x_40);
lean_ctor_set(x_44, 4, x_41);
lean_ctor_set(x_44, 5, x_42);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
lean_object* l_Lean_Meta_savingCache(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_savingCache___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_isClassQuickConst(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_1);
x_5 = lean_is_class(x_4, x_1);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; 
x_6 = 1;
x_7 = l_Lean_Meta_getConstAux(x_1, x_6, x_2, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_8);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_7, 0);
lean_dec(x_16);
x_17 = lean_box(2);
lean_ctor_set(x_7, 0, x_17);
return x_7;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_box(2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
return x_7;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
}
}
lean_object* l_Lean_Meta_isClassQuickConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isClassQuickConst(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_isClassQuick___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_metavar_ctx_get_expr_assignment(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_1 = x_9;
goto _start;
}
}
case 4:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_Meta_isClassQuickConst(x_11, x_2, x_3);
return x_12;
}
case 5:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lean_Expr_getAppFn___main(x_13);
lean_dec(x_13);
switch (lean_obj_tag(x_14)) {
case 4:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Meta_isClassQuickConst(x_15, x_2, x_3);
return x_16;
}
case 6:
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
x_17 = lean_box(2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
default: 
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
}
case 7:
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
lean_dec(x_1);
x_1 = x_21;
goto _start;
}
case 8:
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_23 = lean_box(2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
return x_24;
}
case 10:
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_1 = x_25;
goto _start;
}
case 11:
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_27 = lean_box(2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
return x_28;
}
default: 
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_3);
return x_30;
}
}
}
}
lean_object* l_Lean_Meta_isClassQuick___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isClassQuick___main(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_isClassQuick(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isClassQuick___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_isClassQuick___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isClassQuick(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_resettingTypeClassCache___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_resettingTypeClassCache(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_resettingTypeClassCache___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withNewLocalInstance___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_array_push(x_7, x_8);
lean_ctor_set(x_4, 2, x_9);
x_10 = lean_apply_2(x_3, x_4, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
x_15 = lean_array_push(x_13, x_14);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_apply_2(x_3, x_16, x_5);
return x_17;
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstance(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstance___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_apply_2(x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = l_Lean_Expr_fvarId_x21(x_10);
lean_inc(x_5);
x_12 = l_Lean_Meta_getLocalDecl(x_11, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_LocalDecl_type(x_13);
lean_dec(x_13);
lean_inc(x_15);
x_16 = l_Lean_Meta_isClassQuick___main(x_15, x_5, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
switch (lean_obj_tag(x_17)) {
case 0:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_10);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_3, x_19);
lean_dec(x_3);
x_3 = x_20;
x_6 = x_18;
goto _start;
}
case 1:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_15);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_3, x_24);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_5, 2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_10);
x_29 = lean_array_push(x_27, x_28);
lean_ctor_set(x_5, 2, x_29);
x_3 = x_25;
x_6 = x_22;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_5, 0);
x_32 = lean_ctor_get(x_5, 1);
x_33 = lean_ctor_get(x_5, 2);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_5);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_10);
x_35 = lean_array_push(x_33, x_34);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_35);
x_3 = x_25;
x_5 = x_36;
x_6 = x_22;
goto _start;
}
}
default: 
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_dec(x_16);
lean_inc(x_1);
lean_inc(x_5);
x_39 = lean_apply_3(x_1, x_15, x_5, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_10);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_3, x_42);
lean_dec(x_3);
x_3 = x_43;
x_6 = x_41;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = lean_ctor_get(x_40, 0);
lean_inc(x_46);
lean_dec(x_40);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_3, x_47);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_5);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_5, 2);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_10);
x_52 = lean_array_push(x_50, x_51);
lean_ctor_set(x_5, 2, x_52);
x_3 = x_48;
x_6 = x_45;
goto _start;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_5, 0);
x_55 = lean_ctor_get(x_5, 1);
x_56 = lean_ctor_get(x_5, 2);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_5);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_46);
lean_ctor_set(x_57, 1, x_10);
x_58 = lean_array_push(x_56, x_57);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_55);
lean_ctor_set(x_59, 2, x_58);
x_3 = x_48;
x_5 = x_59;
x_6 = x_45;
goto _start;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_39);
if (x_61 == 0)
{
return x_39;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_39, 0);
x_63 = lean_ctor_get(x_39, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_39);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_16);
if (x_65 == 0)
{
return x_16;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_16, 0);
x_67 = lean_ctor_get(x_16, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_16);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_12);
if (x_69 == 0)
{
return x_12;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_12, 0);
x_71 = lean_ctor_get(x_12, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_12);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___main___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_withNewLocalInstances___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_withNewLocalInstances___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_withNewLocalInstances___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isForall(x_10);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_14 = lean_apply_4(x_1, x_2, x_3, x_11, x_12);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_3);
x_15 = l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___rarg(x_4, x_5, x_6, x_7, x_1, x_8, x_2, x_9, x_10, x_11, x_12);
return x_15;
}
}
}
lean_object* l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
if (lean_obj_tag(x_9) == 7)
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_37 = lean_ctor_get(x_9, 0);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_39 = lean_ctor_get(x_9, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_9, 2);
lean_inc(x_40);
lean_dec(x_9);
x_41 = lean_array_get_size(x_7);
lean_inc(x_7);
x_42 = lean_expr_instantiate_rev_range(x_39, x_8, x_41, x_7);
lean_dec(x_41);
lean_dec(x_39);
x_43 = l_Lean_Meta_mkFreshId___rarg(x_11);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_44);
x_46 = lean_local_ctx_mk_local_decl(x_6, x_44, x_37, x_42, x_38);
x_47 = lean_expr_mk_fvar(x_44);
x_48 = lean_array_push(x_7, x_47);
if (lean_obj_tag(x_4) == 0)
{
x_6 = x_46;
x_7 = x_48;
x_9 = x_40;
x_11 = x_45;
goto _start;
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_4, 0);
lean_inc(x_50);
x_51 = lean_array_get_size(x_48);
x_52 = lean_nat_dec_lt(x_51, x_50);
lean_dec(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_4);
lean_dec(x_1);
lean_inc(x_48);
x_53 = lean_expr_instantiate_rev_range(x_40, x_8, x_51, x_48);
lean_dec(x_51);
lean_dec(x_40);
lean_inc(x_48);
x_54 = lean_apply_2(x_5, x_48, x_53);
x_55 = !lean_is_exclusive(x_10);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_10, 1);
lean_dec(x_56);
lean_ctor_set(x_10, 1, x_46);
x_57 = l_Lean_Meta_withNewLocalInstances___main___rarg(x_2, x_48, x_8, x_54, x_10, x_45);
lean_dec(x_48);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_10, 0);
x_59 = lean_ctor_get(x_10, 2);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_10);
x_60 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_46);
lean_ctor_set(x_60, 2, x_59);
x_61 = l_Lean_Meta_withNewLocalInstances___main___rarg(x_2, x_48, x_8, x_54, x_60, x_45);
lean_dec(x_48);
return x_61;
}
}
else
{
lean_dec(x_51);
x_6 = x_46;
x_7 = x_48;
x_9 = x_40;
x_11 = x_45;
goto _start;
}
}
}
else
{
lean_object* x_63; 
x_63 = lean_box(0);
x_12 = x_63;
goto block_36;
}
block_36:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_12);
x_13 = lean_array_get_size(x_7);
lean_inc(x_7);
x_14 = lean_expr_instantiate_rev_range(x_9, x_8, x_13, x_7);
lean_dec(x_9);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_10, 1);
lean_dec(x_16);
lean_inc(x_6);
lean_ctor_set(x_10, 1, x_6);
if (x_3 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
lean_inc(x_7);
x_17 = lean_apply_2(x_5, x_7, x_14);
x_18 = l_Lean_Meta_withNewLocalInstances___main___rarg(x_2, x_7, x_8, x_17, x_10, x_11);
lean_dec(x_7);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_1);
lean_inc(x_14);
x_19 = lean_apply_1(x_1, x_14);
x_20 = lean_box(x_3);
lean_inc(x_2);
lean_inc(x_7);
x_21 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___rarg___lambda__1___boxed), 12, 9);
lean_closure_set(x_21, 0, x_5);
lean_closure_set(x_21, 1, x_7);
lean_closure_set(x_21, 2, x_14);
lean_closure_set(x_21, 3, x_1);
lean_closure_set(x_21, 4, x_2);
lean_closure_set(x_21, 5, x_20);
lean_closure_set(x_21, 6, x_4);
lean_closure_set(x_21, 7, x_6);
lean_closure_set(x_21, 8, x_13);
x_22 = l_EIO_Monad___closed__1;
x_23 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, lean_box(0));
lean_closure_set(x_23, 2, lean_box(0));
lean_closure_set(x_23, 3, x_19);
lean_closure_set(x_23, 4, x_21);
x_24 = l_Lean_Meta_withNewLocalInstances___main___rarg(x_2, x_7, x_8, x_23, x_10, x_11);
lean_dec(x_7);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
lean_inc(x_6);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_6);
lean_ctor_set(x_27, 2, x_26);
if (x_3 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
lean_inc(x_7);
x_28 = lean_apply_2(x_5, x_7, x_14);
x_29 = l_Lean_Meta_withNewLocalInstances___main___rarg(x_2, x_7, x_8, x_28, x_27, x_11);
lean_dec(x_7);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc(x_1);
lean_inc(x_14);
x_30 = lean_apply_1(x_1, x_14);
x_31 = lean_box(x_3);
lean_inc(x_2);
lean_inc(x_7);
x_32 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___rarg___lambda__1___boxed), 12, 9);
lean_closure_set(x_32, 0, x_5);
lean_closure_set(x_32, 1, x_7);
lean_closure_set(x_32, 2, x_14);
lean_closure_set(x_32, 3, x_1);
lean_closure_set(x_32, 4, x_2);
lean_closure_set(x_32, 5, x_31);
lean_closure_set(x_32, 6, x_4);
lean_closure_set(x_32, 7, x_6);
lean_closure_set(x_32, 8, x_13);
x_33 = l_EIO_Monad___closed__1;
x_34 = lean_alloc_closure((void*)(l_ReaderT_bind___rarg), 6, 5);
lean_closure_set(x_34, 0, x_33);
lean_closure_set(x_34, 1, lean_box(0));
lean_closure_set(x_34, 2, lean_box(0));
lean_closure_set(x_34, 3, x_30);
lean_closure_set(x_34, 4, x_32);
x_35 = l_Lean_Meta_withNewLocalInstances___main___rarg(x_2, x_7, x_8, x_34, x_27, x_11);
lean_dec(x_7);
return x_35;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___rarg(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___rarg(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_8__forallTelescopeReducingAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_3);
x_8 = lean_apply_3(x_1, x_3, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Expr_isForall(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Array_empty___closed__1;
x_13 = lean_apply_4(x_5, x_12, x_3, x_6, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_14 = lean_ctor_get(x_10, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
x_16 = 1;
x_17 = l_Array_empty___closed__1;
x_18 = lean_unsigned_to_nat(0u);
x_19 = l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___rarg(x_1, x_2, x_16, x_4, x_5, x_15, x_17, x_18, x_9, x_6, x_10);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_19, 1);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 2);
lean_dec(x_23);
lean_ctor_set(x_21, 2, x_14);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
x_26 = lean_ctor_get(x_21, 3);
x_27 = lean_ctor_get(x_21, 4);
x_28 = lean_ctor_get(x_21, 5);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
x_29 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_14);
lean_ctor_set(x_29, 3, x_26);
lean_ctor_set(x_29, 4, x_27);
lean_ctor_set(x_29, 5, x_28);
lean_ctor_set(x_19, 1, x_29);
return x_19;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_19, 1);
x_31 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
lean_inc(x_31);
lean_dec(x_19);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_30, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_30, 4);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 5);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 lean_ctor_release(x_30, 3);
 lean_ctor_release(x_30, 4);
 lean_ctor_release(x_30, 5);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 6, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_14);
lean_ctor_set(x_38, 3, x_34);
lean_ctor_set(x_38, 4, x_35);
lean_ctor_set(x_38, 5, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_19);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_19, 1);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 2);
lean_dec(x_43);
lean_ctor_set(x_41, 2, x_14);
return x_19;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_41, 0);
x_45 = lean_ctor_get(x_41, 1);
x_46 = lean_ctor_get(x_41, 3);
x_47 = lean_ctor_get(x_41, 4);
x_48 = lean_ctor_get(x_41, 5);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_41);
x_49 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_14);
lean_ctor_set(x_49, 3, x_46);
lean_ctor_set(x_49, 4, x_47);
lean_ctor_set(x_49, 5, x_48);
lean_ctor_set(x_19, 1, x_49);
return x_19;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_50 = lean_ctor_get(x_19, 1);
x_51 = lean_ctor_get(x_19, 0);
lean_inc(x_50);
lean_inc(x_51);
lean_dec(x_19);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_50, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_50, 4);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 5);
lean_inc(x_56);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 lean_ctor_release(x_50, 2);
 lean_ctor_release(x_50, 3);
 lean_ctor_release(x_50, 4);
 lean_ctor_release(x_50, 5);
 x_57 = x_50;
} else {
 lean_dec_ref(x_50);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 6, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_53);
lean_ctor_set(x_58, 2, x_14);
lean_ctor_set(x_58, 3, x_54);
lean_ctor_set(x_58, 4, x_55);
lean_ctor_set(x_58, 5, x_56);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_51);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_8);
if (x_60 == 0)
{
return x_8;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_8, 0);
x_62 = lean_ctor_get(x_8, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_8);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Basic_8__forallTelescopeReducingAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Basic_8__forallTelescopeReducingAux___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_isClassExpensive___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_getAppFn___main(x_3);
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_inc(x_7);
x_9 = lean_is_class(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_6);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
}
}
lean_object* _init_l_Lean_Meta_isClassExpensive___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_isClassExpensive___main___lambda__1___boxed), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_isClassExpensive___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_isClassExpensive___main), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_box(0);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 2;
lean_ctor_set_uint8(x_8, sizeof(void*)*1 + 4, x_10);
x_11 = l_Lean_Meta_isClassExpensive___main___closed__1;
x_12 = l___private_Init_Lean_Meta_Basic_8__forallTelescopeReducingAux___rarg(x_1, x_5, x_2, x_6, x_11, x_3, x_4);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_15 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 1);
x_16 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 2);
x_17 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 3);
lean_inc(x_13);
lean_dec(x_8);
x_18 = 2;
x_19 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_14);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 1, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 2, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 3, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 4, x_18);
lean_ctor_set(x_3, 0, x_19);
x_20 = l_Lean_Meta_isClassExpensive___main___closed__1;
x_21 = l___private_Init_Lean_Meta_Basic_8__forallTelescopeReducingAux___rarg(x_1, x_5, x_2, x_6, x_20, x_3, x_4);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_3, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_22, sizeof(void*)*1);
x_27 = lean_ctor_get_uint8(x_22, sizeof(void*)*1 + 1);
x_28 = lean_ctor_get_uint8(x_22, sizeof(void*)*1 + 2);
x_29 = lean_ctor_get_uint8(x_22, sizeof(void*)*1 + 3);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_30 = x_22;
} else {
 lean_dec_ref(x_22);
 x_30 = lean_box(0);
}
x_31 = 2;
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 1, 5);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_26);
lean_ctor_set_uint8(x_32, sizeof(void*)*1 + 1, x_27);
lean_ctor_set_uint8(x_32, sizeof(void*)*1 + 2, x_28);
lean_ctor_set_uint8(x_32, sizeof(void*)*1 + 3, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*1 + 4, x_31);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_23);
lean_ctor_set(x_33, 2, x_24);
x_34 = l_Lean_Meta_isClassExpensive___main___closed__1;
x_35 = l___private_Init_Lean_Meta_Basic_8__forallTelescopeReducingAux___rarg(x_1, x_5, x_2, x_6, x_34, x_33, x_4);
return x_35;
}
}
}
lean_object* l_Lean_Meta_isClassExpensive___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_isClassExpensive___main___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Meta_isClassExpensive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_isClassExpensive___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_array_get_size(x_3);
lean_inc(x_3);
x_11 = lean_expr_instantiate_rev_range(x_5, x_4, x_10, x_3);
lean_dec(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_7, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_1);
x_14 = lean_apply_4(x_2, x_3, x_11, x_8, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
x_15 = lean_array_fget(x_6, x_7);
x_16 = l_Lean_Expr_fvarId_x21(x_15);
lean_inc(x_8);
x_17 = l_Lean_Meta_getLocalDecl(x_16, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_LocalDecl_type(x_18);
lean_dec(x_18);
lean_inc(x_20);
x_21 = l_Lean_Meta_isClassQuick___main(x_20, x_8, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
switch (lean_obj_tag(x_22)) {
case 0:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_15);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_7, x_24);
lean_dec(x_7);
x_7 = x_25;
x_9 = x_23;
goto _start;
}
case 1:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_20);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_7, x_29);
lean_dec(x_7);
x_31 = !lean_is_exclusive(x_8);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_8, 2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_15);
x_34 = lean_array_push(x_32, x_33);
lean_ctor_set(x_8, 2, x_34);
x_7 = x_30;
x_9 = x_27;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_8, 0);
x_37 = lean_ctor_get(x_8, 1);
x_38 = lean_ctor_get(x_8, 2);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_8);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_28);
lean_ctor_set(x_39, 1, x_15);
x_40 = lean_array_push(x_38, x_39);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 2, x_40);
x_7 = x_30;
x_8 = x_41;
x_9 = x_27;
goto _start;
}
}
default: 
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_21, 1);
lean_inc(x_43);
lean_dec(x_21);
lean_inc(x_8);
lean_inc(x_1);
x_44 = l_Lean_Meta_isClassExpensive___main(x_1, x_20, x_8, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_15);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_7, x_47);
lean_dec(x_7);
x_7 = x_48;
x_9 = x_46;
goto _start;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_dec(x_44);
x_51 = lean_ctor_get(x_45, 0);
lean_inc(x_51);
lean_dec(x_45);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_7, x_52);
lean_dec(x_7);
x_54 = !lean_is_exclusive(x_8);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_8, 2);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_15);
x_57 = lean_array_push(x_55, x_56);
lean_ctor_set(x_8, 2, x_57);
x_7 = x_53;
x_9 = x_50;
goto _start;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_8, 0);
x_60 = lean_ctor_get(x_8, 1);
x_61 = lean_ctor_get(x_8, 2);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_8);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_51);
lean_ctor_set(x_62, 1, x_15);
x_63 = lean_array_push(x_61, x_62);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_60);
lean_ctor_set(x_64, 2, x_63);
x_7 = x_53;
x_8 = x_64;
x_9 = x_50;
goto _start;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_44);
if (x_66 == 0)
{
return x_44;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_44, 0);
x_68 = lean_ctor_get(x_44, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_44);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_21);
if (x_70 == 0)
{
return x_21;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_21, 0);
x_72 = lean_ctor_get(x_21, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_21);
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
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_17);
if (x_74 == 0)
{
return x_17;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_17, 0);
x_76 = lean_ctor_get(x_17, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_17);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__2___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_ReaderT_bind___at_Lean_Meta_forallTelescope___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_3(x_2, x_6, x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Meta_forallTelescope___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_forallTelescope___spec__3___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__4___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Lean_Expr_isForall(x_9);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_13 = lean_apply_4(x_1, x_2, x_3, x_10, x_11);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_3);
x_14 = l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallTelescope___spec__1___rarg(x_4, x_1, x_5, x_6, x_7, x_2, x_8, x_9, x_10, x_11);
return x_14;
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__4___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_inc(x_1);
lean_inc(x_10);
x_15 = lean_apply_1(x_1, x_10);
x_16 = lean_box(x_3);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_6);
lean_inc(x_2);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__4___rarg___lambda__1___boxed), 11, 8);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_6);
lean_closure_set(x_17, 2, x_10);
lean_closure_set(x_17, 3, x_1);
lean_closure_set(x_17, 4, x_16);
lean_closure_set(x_17, 5, x_4);
lean_closure_set(x_17, 6, x_5);
lean_closure_set(x_17, 7, x_9);
x_18 = lean_array_get_size(x_11);
x_19 = lean_nat_dec_lt(x_12, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_20 = l_ReaderT_bind___at_Lean_Meta_forallTelescope___spec__3___rarg(x_15, x_17, x_13, x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
lean_dec(x_15);
x_21 = lean_array_fget(x_11, x_12);
x_22 = l_Lean_Expr_fvarId_x21(x_21);
lean_inc(x_13);
x_23 = l_Lean_Meta_getLocalDecl(x_22, x_13, x_14);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_LocalDecl_type(x_24);
lean_dec(x_24);
lean_inc(x_26);
x_27 = l_Lean_Meta_isClassQuick___main(x_26, x_13, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
switch (lean_obj_tag(x_28)) {
case 0:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_26);
lean_dec(x_21);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_12, x_30);
lean_dec(x_12);
x_12 = x_31;
x_14 = x_29;
goto _start;
}
case 1:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_26);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_12, x_35);
lean_dec(x_12);
x_37 = !lean_is_exclusive(x_13);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_13, 2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_21);
x_40 = lean_array_push(x_38, x_39);
lean_ctor_set(x_13, 2, x_40);
x_12 = x_36;
x_14 = x_33;
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_13, 0);
x_43 = lean_ctor_get(x_13, 1);
x_44 = lean_ctor_get(x_13, 2);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_13);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_34);
lean_ctor_set(x_45, 1, x_21);
x_46 = lean_array_push(x_44, x_45);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_43);
lean_ctor_set(x_47, 2, x_46);
x_12 = x_36;
x_13 = x_47;
x_14 = x_33;
goto _start;
}
}
default: 
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_27, 1);
lean_inc(x_49);
lean_dec(x_27);
lean_inc(x_13);
lean_inc(x_1);
x_50 = l_Lean_Meta_isClassExpensive___main(x_1, x_26, x_13, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_21);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_12, x_53);
lean_dec(x_12);
x_12 = x_54;
x_14 = x_52;
goto _start;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_dec(x_50);
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
lean_dec(x_51);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_add(x_12, x_58);
lean_dec(x_12);
x_60 = !lean_is_exclusive(x_13);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_13, 2);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_21);
x_63 = lean_array_push(x_61, x_62);
lean_ctor_set(x_13, 2, x_63);
x_12 = x_59;
x_14 = x_56;
goto _start;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_13, 0);
x_66 = lean_ctor_get(x_13, 1);
x_67 = lean_ctor_get(x_13, 2);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_13);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_57);
lean_ctor_set(x_68, 1, x_21);
x_69 = lean_array_push(x_67, x_68);
x_70 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set(x_70, 1, x_66);
lean_ctor_set(x_70, 2, x_69);
x_12 = x_59;
x_13 = x_70;
x_14 = x_56;
goto _start;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_50);
if (x_72 == 0)
{
return x_50;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_50, 0);
x_74 = lean_ctor_get(x_50, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_50);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_27);
if (x_76 == 0)
{
return x_27;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_27, 0);
x_78 = lean_ctor_get(x_27, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_27);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_23);
if (x_80 == 0)
{
return x_23;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_23, 0);
x_82 = lean_ctor_get(x_23, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_23);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__4___rarg___boxed), 14, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_inc(x_6);
x_11 = lean_expr_mk_fvar(x_6);
lean_inc(x_3);
x_12 = lean_array_push(x_3, x_11);
x_13 = lean_array_get_size(x_12);
lean_inc(x_12);
x_14 = lean_expr_instantiate_rev_range(x_5, x_4, x_13, x_12);
lean_dec(x_13);
x_15 = lean_array_get_size(x_7);
x_16 = lean_nat_dec_lt(x_8, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_apply_4(x_2, x_12, x_14, x_9, x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
lean_dec(x_12);
x_18 = lean_array_fget(x_7, x_8);
x_19 = l_Lean_Expr_fvarId_x21(x_18);
lean_inc(x_9);
x_20 = l_Lean_Meta_getLocalDecl(x_19, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_LocalDecl_type(x_21);
lean_dec(x_21);
lean_inc(x_23);
x_24 = l_Lean_Meta_isClassQuick___main(x_23, x_9, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
switch (lean_obj_tag(x_25)) {
case 0:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_18);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_8, x_27);
lean_dec(x_8);
x_8 = x_28;
x_10 = x_26;
goto _start;
}
case 1:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_23);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_8, x_32);
lean_dec(x_8);
x_34 = !lean_is_exclusive(x_9);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_9, 2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_18);
x_37 = lean_array_push(x_35, x_36);
lean_ctor_set(x_9, 2, x_37);
x_8 = x_33;
x_10 = x_30;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_9, 0);
x_40 = lean_ctor_get(x_9, 1);
x_41 = lean_ctor_get(x_9, 2);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_9);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_31);
lean_ctor_set(x_42, 1, x_18);
x_43 = lean_array_push(x_41, x_42);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_40);
lean_ctor_set(x_44, 2, x_43);
x_8 = x_33;
x_9 = x_44;
x_10 = x_30;
goto _start;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_24, 1);
lean_inc(x_46);
lean_dec(x_24);
lean_inc(x_9);
lean_inc(x_1);
x_47 = l_Lean_Meta_isClassExpensive___main(x_1, x_23, x_9, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_18);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_8, x_50);
lean_dec(x_8);
x_8 = x_51;
x_10 = x_49;
goto _start;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_dec(x_47);
x_54 = lean_ctor_get(x_48, 0);
lean_inc(x_54);
lean_dec(x_48);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_add(x_8, x_55);
lean_dec(x_8);
x_57 = !lean_is_exclusive(x_9);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_9, 2);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_18);
x_60 = lean_array_push(x_58, x_59);
lean_ctor_set(x_9, 2, x_60);
x_8 = x_56;
x_10 = x_53;
goto _start;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_9, 0);
x_63 = lean_ctor_get(x_9, 1);
x_64 = lean_ctor_get(x_9, 2);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_9);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_54);
lean_ctor_set(x_65, 1, x_18);
x_66 = lean_array_push(x_64, x_65);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_63);
lean_ctor_set(x_67, 2, x_66);
x_8 = x_56;
x_9 = x_67;
x_10 = x_53;
goto _start;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_47);
if (x_69 == 0)
{
return x_47;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_47, 0);
x_71 = lean_ctor_get(x_47, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_47);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_24);
if (x_73 == 0)
{
return x_24;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_24, 0);
x_75 = lean_ctor_get(x_24, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_24);
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
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_20);
if (x_77 == 0)
{
return x_20;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_20, 0);
x_79 = lean_ctor_get(x_20, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_20);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__5___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallTelescope___spec__1___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
if (lean_obj_tag(x_8) == 7)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_8, 0);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_8, 2);
lean_inc(x_27);
lean_dec(x_8);
x_28 = lean_array_get_size(x_6);
lean_inc(x_6);
x_29 = lean_expr_instantiate_rev_range(x_26, x_7, x_28, x_6);
lean_dec(x_28);
lean_dec(x_26);
x_30 = l_Lean_Meta_mkFreshId___rarg(x_10);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_31);
x_33 = lean_local_ctx_mk_local_decl(x_5, x_31, x_24, x_29, x_25);
lean_inc(x_31);
x_34 = lean_expr_mk_fvar(x_31);
lean_inc(x_6);
x_35 = lean_array_push(x_6, x_34);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_31);
lean_dec(x_6);
x_5 = x_33;
x_6 = x_35;
x_8 = x_27;
x_10 = x_32;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_4, 0);
lean_inc(x_37);
x_38 = lean_array_get_size(x_35);
x_39 = lean_nat_dec_lt(x_38, x_37);
lean_dec(x_37);
lean_dec(x_38);
if (x_39 == 0)
{
uint8_t x_40; 
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_9);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_9, 1);
lean_dec(x_41);
lean_ctor_set(x_9, 1, x_33);
lean_inc(x_7);
x_42 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__5___rarg(x_1, x_2, x_6, x_7, x_27, x_31, x_35, x_7, x_9, x_32);
lean_dec(x_35);
lean_dec(x_27);
lean_dec(x_7);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_9, 0);
x_44 = lean_ctor_get(x_9, 2);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_9);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_33);
lean_ctor_set(x_45, 2, x_44);
lean_inc(x_7);
x_46 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__5___rarg(x_1, x_2, x_6, x_7, x_27, x_31, x_35, x_7, x_45, x_32);
lean_dec(x_35);
lean_dec(x_27);
lean_dec(x_7);
return x_46;
}
}
else
{
lean_dec(x_31);
lean_dec(x_6);
x_5 = x_33;
x_6 = x_35;
x_8 = x_27;
x_10 = x_32;
goto _start;
}
}
}
else
{
lean_object* x_48; 
x_48 = lean_box(0);
x_11 = x_48;
goto block_23;
}
block_23:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_11);
x_12 = lean_array_get_size(x_6);
lean_inc(x_6);
x_13 = lean_expr_instantiate_rev_range(x_8, x_7, x_12, x_6);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_9, 1);
lean_dec(x_15);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_5);
if (x_3 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__2___rarg(x_1, x_2, x_6, x_7, x_8, x_6, x_7, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_16;
}
else
{
lean_object* x_17; 
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_13, x_6, x_7, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 2);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
lean_inc(x_5);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_5);
lean_ctor_set(x_20, 2, x_19);
if (x_3 == 0)
{
lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__2___rarg(x_1, x_2, x_6, x_7, x_8, x_6, x_7, x_20, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_21;
}
else
{
lean_object* x_22; 
lean_inc(x_7);
lean_inc(x_6);
x_22 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_13, x_6, x_7, x_20, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_22;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallTelescope___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallTelescope___spec__1___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_forallTelescope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = 0;
x_10 = l_Array_empty___closed__1;
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallTelescope___spec__1___rarg(x_1, x_3, x_9, x_8, x_7, x_10, x_11, x_2, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 2);
lean_dec(x_16);
lean_ctor_set(x_14, 2, x_6);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
x_19 = lean_ctor_get(x_14, 3);
x_20 = lean_ctor_get(x_14, 4);
x_21 = lean_ctor_get(x_14, 5);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_14);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_6);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set(x_22, 4, x_20);
lean_ctor_set(x_22, 5, x_21);
lean_ctor_set(x_12, 1, x_22);
return x_12;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_12, 1);
x_24 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_inc(x_24);
lean_dec(x_12);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 3);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 4);
lean_inc(x_28);
x_29 = lean_ctor_get(x_23, 5);
lean_inc(x_29);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 lean_ctor_release(x_23, 4);
 lean_ctor_release(x_23, 5);
 x_30 = x_23;
} else {
 lean_dec_ref(x_23);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 6, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_6);
lean_ctor_set(x_31, 3, x_27);
lean_ctor_set(x_31, 4, x_28);
lean_ctor_set(x_31, 5, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_12);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_12, 1);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 2);
lean_dec(x_36);
lean_ctor_set(x_34, 2, x_6);
return x_12;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_34, 0);
x_38 = lean_ctor_get(x_34, 1);
x_39 = lean_ctor_get(x_34, 3);
x_40 = lean_ctor_get(x_34, 4);
x_41 = lean_ctor_get(x_34, 5);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_34);
x_42 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_38);
lean_ctor_set(x_42, 2, x_6);
lean_ctor_set(x_42, 3, x_39);
lean_ctor_set(x_42, 4, x_40);
lean_ctor_set(x_42, 5, x_41);
lean_ctor_set(x_12, 1, x_42);
return x_12;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = lean_ctor_get(x_12, 1);
x_44 = lean_ctor_get(x_12, 0);
lean_inc(x_43);
lean_inc(x_44);
lean_dec(x_12);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 3);
lean_inc(x_47);
x_48 = lean_ctor_get(x_43, 4);
lean_inc(x_48);
x_49 = lean_ctor_get(x_43, 5);
lean_inc(x_49);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 lean_ctor_release(x_43, 4);
 lean_ctor_release(x_43, 5);
 x_50 = x_43;
} else {
 lean_dec_ref(x_43);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 6, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_46);
lean_ctor_set(x_51, 2, x_6);
lean_ctor_set(x_51, 3, x_47);
lean_ctor_set(x_51, 4, x_48);
lean_ctor_set(x_51, 5, x_49);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_44);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
lean_object* l_Lean_Meta_forallTelescope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__4___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__4___rarg___lambda__1(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__4___rarg(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
return x_16;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_withNewLocalInstances___main___at_Lean_Meta_forallTelescope___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallTelescope___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Lean_Meta_Basic_7__forallTelescopeReducingAuxAux___main___at_Lean_Meta_forallTelescope___spec__1___rarg(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_isClassExpensive), 4, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_box(0);
x_8 = l___private_Init_Lean_Meta_Basic_8__forallTelescopeReducingAux___rarg(x_1, x_6, x_2, x_7, x_3, x_4, x_5);
return x_8;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_isClassExpensive), 4, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l___private_Init_Lean_Meta_Basic_8__forallTelescopeReducingAux___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_isClass(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
x_5 = l_Lean_Meta_isClassQuick___main(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 0:
{
uint8_t x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
case 1:
{
uint8_t x_13; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
default: 
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_dec(x_5);
x_22 = l_Lean_Meta_isClassExpensive___main(x_1, x_2, x_3, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
return x_5;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_5, 0);
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_5);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Basic_9__lambdaTelescopeAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
switch (lean_obj_tag(x_6)) {
case 6:
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_6, 2);
lean_inc(x_25);
lean_dec(x_6);
x_26 = lean_array_get_size(x_4);
lean_inc(x_4);
x_27 = lean_expr_instantiate_rev_range(x_24, x_5, x_26, x_4);
lean_dec(x_26);
lean_dec(x_24);
x_28 = l_Lean_Meta_mkFreshId___rarg(x_8);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_29);
x_31 = lean_local_ctx_mk_local_decl(x_3, x_29, x_22, x_27, x_23);
x_32 = lean_expr_mk_fvar(x_29);
x_33 = lean_array_push(x_4, x_32);
x_3 = x_31;
x_4 = x_33;
x_6 = x_25;
x_8 = x_30;
goto _start;
}
case 8:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_35 = lean_ctor_get(x_6, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_6, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_6, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_6, 3);
lean_inc(x_38);
lean_dec(x_6);
x_39 = lean_array_get_size(x_4);
lean_inc(x_4);
x_40 = lean_expr_instantiate_rev_range(x_36, x_5, x_39, x_4);
lean_dec(x_36);
lean_inc(x_4);
x_41 = lean_expr_instantiate_rev_range(x_37, x_5, x_39, x_4);
lean_dec(x_39);
lean_dec(x_37);
x_42 = l_Lean_Meta_mkFreshId___rarg(x_8);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_43);
x_45 = lean_local_ctx_mk_let_decl(x_3, x_43, x_35, x_40, x_41);
x_46 = lean_expr_mk_fvar(x_43);
x_47 = lean_array_push(x_4, x_46);
x_3 = x_45;
x_4 = x_47;
x_6 = x_38;
x_8 = x_44;
goto _start;
}
default: 
{
lean_object* x_49; 
x_49 = lean_box(0);
x_9 = x_49;
goto block_21;
}
}
block_21:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_9);
x_10 = lean_array_get_size(x_4);
lean_inc(x_4);
x_11 = lean_expr_instantiate_rev_range(x_6, x_5, x_10, x_4);
lean_dec(x_10);
lean_dec(x_6);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_isClassExpensive), 4, 1);
lean_closure_set(x_12, 0, x_1);
lean_inc(x_4);
x_13 = lean_apply_2(x_2, x_4, x_11);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_7, 1);
lean_dec(x_15);
lean_ctor_set(x_7, 1, x_3);
x_16 = l_Lean_Meta_withNewLocalInstances___main___rarg(x_12, x_4, x_5, x_13, x_7, x_8);
lean_dec(x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 2);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_3);
lean_ctor_set(x_19, 2, x_18);
x_20 = l_Lean_Meta_withNewLocalInstances___main___rarg(x_12, x_4, x_5, x_13, x_19, x_8);
lean_dec(x_4);
return x_20;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Basic_9__lambdaTelescopeAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Basic_9__lambdaTelescopeAux___main___rarg), 8, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_9__lambdaTelescopeAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Lean_Meta_Basic_9__lambdaTelescopeAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_9__lambdaTelescopeAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Basic_9__lambdaTelescopeAux___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = l_Array_empty___closed__1;
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Init_Lean_Meta_Basic_9__lambdaTelescopeAux___main___rarg(x_1, x_3, x_7, x_8, x_9, x_2, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 2);
lean_dec(x_14);
lean_ctor_set(x_12, 2, x_6);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 3);
x_18 = lean_ctor_get(x_12, 4);
x_19 = lean_ctor_get(x_12, 5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
x_20 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_6);
lean_ctor_set(x_20, 3, x_17);
lean_ctor_set(x_20, 4, x_18);
lean_ctor_set(x_20, 5, x_19);
lean_ctor_set(x_10, 1, x_20);
return x_10;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_10, 1);
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 3);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 4);
lean_inc(x_26);
x_27 = lean_ctor_get(x_21, 5);
lean_inc(x_27);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 lean_ctor_release(x_21, 3);
 lean_ctor_release(x_21, 4);
 lean_ctor_release(x_21, 5);
 x_28 = x_21;
} else {
 lean_dec_ref(x_21);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 6, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_6);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
lean_ctor_set(x_29, 5, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_10);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_10, 1);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 2);
lean_dec(x_34);
lean_ctor_set(x_32, 2, x_6);
return x_10;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = lean_ctor_get(x_32, 1);
x_37 = lean_ctor_get(x_32, 3);
x_38 = lean_ctor_get(x_32, 4);
x_39 = lean_ctor_get(x_32, 5);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_32);
x_40 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_40, 2, x_6);
lean_ctor_set(x_40, 3, x_37);
lean_ctor_set(x_40, 4, x_38);
lean_ctor_set(x_40, 5, x_39);
lean_ctor_set(x_10, 1, x_40);
return x_10;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_10, 1);
x_42 = lean_ctor_get(x_10, 0);
lean_inc(x_41);
lean_inc(x_42);
lean_dec(x_10);
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
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 lean_ctor_release(x_41, 4);
 lean_ctor_release(x_41, 5);
 x_48 = x_41;
} else {
 lean_dec_ref(x_41);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 6, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_44);
lean_ctor_set(x_49, 2, x_6);
lean_ctor_set(x_49, 3, x_45);
lean_ctor_set(x_49, 4, x_46);
lean_ctor_set(x_49, 5, x_47);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
lean_object* l_Lean_Meta_lambdaTelescope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_liftStateMCtx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
x_14 = lean_ctor_get(x_3, 4);
x_15 = lean_ctor_get(x_3, 5);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_16 = lean_apply_1(x_1, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_12);
lean_ctor_set(x_19, 3, x_13);
lean_ctor_set(x_19, 4, x_14);
lean_ctor_set(x_19, 5, x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
lean_object* l_Lean_Meta_liftStateMCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_liftStateMCtx___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_liftStateMCtx___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_liftStateMCtx___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_instantiateLevelMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_MetavarContext_instantiateLevelMVars___main(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
x_14 = lean_ctor_get(x_3, 4);
x_15 = lean_ctor_get(x_3, 5);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_16 = l_Lean_MetavarContext_instantiateLevelMVars___main(x_1, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_12);
lean_ctor_set(x_19, 3, x_13);
lean_ctor_set(x_19, 4, x_14);
lean_ctor_set(x_19, 5, x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
lean_object* l_Lean_Meta_instantiateLevelMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_instantiateLevelMVars(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_assignLevelMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_metavar_ctx_assign_level(x_6, x_1, x_2);
lean_ctor_set(x_4, 1, x_7);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 2);
x_13 = lean_ctor_get(x_4, 3);
x_14 = lean_ctor_get(x_4, 4);
x_15 = lean_ctor_get(x_4, 5);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_16 = lean_metavar_ctx_assign_level(x_11, x_1, x_2);
x_17 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_12);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set(x_17, 4, x_14);
lean_ctor_set(x_17, 5, x_15);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
lean_object* l_Lean_Meta_assignLevelMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_assignLevelMVar(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Meta_mkFreshLevelMVarId___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Meta_mkFreshId___rarg(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_8 = l_Lean_MetavarContext_addLevelMVarDecl(x_7, x_6);
lean_ctor_set(x_4, 1, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 2);
x_13 = lean_ctor_get(x_4, 3);
x_14 = lean_ctor_get(x_4, 4);
x_15 = lean_ctor_get(x_4, 5);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
lean_inc(x_9);
x_16 = l_Lean_MetavarContext_addLevelMVarDecl(x_11, x_9);
x_17 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_12);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set(x_17, 4, x_14);
lean_ctor_set(x_17, 5, x_15);
lean_ctor_set(x_2, 1, x_17);
return x_2;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_inc(x_19);
lean_dec(x_2);
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
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 lean_ctor_release(x_18, 5);
 x_26 = x_18;
} else {
 lean_dec_ref(x_18);
 x_26 = lean_box(0);
}
lean_inc(x_19);
x_27 = l_Lean_MetavarContext_addLevelMVarDecl(x_21, x_19);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 6, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set(x_28, 3, x_23);
lean_ctor_set(x_28, 4, x_24);
lean_ctor_set(x_28, 5, x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
lean_object* l_Lean_Meta_mkFreshLevelMVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshLevelMVarId___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkFreshLevelMVarId___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_mkFreshLevelMVarId(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_usingDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
lean_ctor_set_uint8(x_6, sizeof(void*)*1 + 4, x_8);
x_9 = lean_apply_3(x_1, x_2, x_3, x_4);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_12 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
x_13 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 2);
x_14 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 3);
lean_inc(x_10);
lean_dec(x_6);
x_15 = 1;
x_16 = lean_alloc_ctor(0, 1, 5);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_11);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 1, x_12);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 2, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 3, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 4, x_15);
lean_ctor_set(x_3, 0, x_16);
x_17 = lean_apply_3(x_1, x_2, x_3, x_4);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_3, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
x_23 = lean_ctor_get_uint8(x_18, sizeof(void*)*1 + 1);
x_24 = lean_ctor_get_uint8(x_18, sizeof(void*)*1 + 2);
x_25 = lean_ctor_get_uint8(x_18, sizeof(void*)*1 + 3);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_26 = x_18;
} else {
 lean_dec_ref(x_18);
 x_26 = lean_box(0);
}
x_27 = 1;
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 1, 5);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*1 + 1, x_23);
lean_ctor_set_uint8(x_28, sizeof(void*)*1 + 2, x_24);
lean_ctor_set_uint8(x_28, sizeof(void*)*1 + 3, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*1 + 4, x_27);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_19);
lean_ctor_set(x_29, 2, x_20);
x_30 = lean_apply_3(x_1, x_2, x_29, x_4);
return x_30;
}
}
}
lean_object* initialize_Init_Control_Reader(lean_object*);
lean_object* initialize_Init_Lean_NameGenerator(lean_object*);
lean_object* initialize_Init_Lean_Environment(lean_object*);
lean_object* initialize_Init_Lean_LOption(lean_object*);
lean_object* initialize_Init_Lean_Trace(lean_object*);
lean_object* initialize_Init_Lean_Class(lean_object*);
lean_object* initialize_Init_Lean_ReducibilityAttrs(lean_object*);
lean_object* initialize_Init_Lean_Meta_Exception(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Reader(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_NameGenerator(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_LOption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Trace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Class(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_ReducibilityAttrs(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Exception(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_TransparencyMode_Inhabited = _init_l_Lean_Meta_TransparencyMode_Inhabited();
l_Lean_Meta_TransparencyMode_HasBeq___closed__1 = _init_l_Lean_Meta_TransparencyMode_HasBeq___closed__1();
lean_mark_persistent(l_Lean_Meta_TransparencyMode_HasBeq___closed__1);
l_Lean_Meta_TransparencyMode_HasBeq = _init_l_Lean_Meta_TransparencyMode_HasBeq();
lean_mark_persistent(l_Lean_Meta_TransparencyMode_HasBeq);
l_Lean_Meta_TransparencyMode_Hashable___closed__1 = _init_l_Lean_Meta_TransparencyMode_Hashable___closed__1();
lean_mark_persistent(l_Lean_Meta_TransparencyMode_Hashable___closed__1);
l_Lean_Meta_TransparencyMode_Hashable = _init_l_Lean_Meta_TransparencyMode_Hashable();
lean_mark_persistent(l_Lean_Meta_TransparencyMode_Hashable);
l_Lean_Meta_ParamInfo_inhabited___closed__1 = _init_l_Lean_Meta_ParamInfo_inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_ParamInfo_inhabited___closed__1);
l_Lean_Meta_ParamInfo_inhabited = _init_l_Lean_Meta_ParamInfo_inhabited();
lean_mark_persistent(l_Lean_Meta_ParamInfo_inhabited);
l_Lean_Meta_InfoCacheKey_Inhabited___closed__1 = _init_l_Lean_Meta_InfoCacheKey_Inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_InfoCacheKey_Inhabited___closed__1);
l_Lean_Meta_InfoCacheKey_Inhabited = _init_l_Lean_Meta_InfoCacheKey_Inhabited();
lean_mark_persistent(l_Lean_Meta_InfoCacheKey_Inhabited);
l_Lean_Meta_dbgTrace___rarg___closed__1 = _init_l_Lean_Meta_dbgTrace___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_dbgTrace___rarg___closed__1);
l_Lean_Meta_tracer___closed__1 = _init_l_Lean_Meta_tracer___closed__1();
lean_mark_persistent(l_Lean_Meta_tracer___closed__1);
l_Lean_Meta_tracer___closed__2 = _init_l_Lean_Meta_tracer___closed__2();
lean_mark_persistent(l_Lean_Meta_tracer___closed__2);
l_Lean_Meta_tracer___closed__3 = _init_l_Lean_Meta_tracer___closed__3();
lean_mark_persistent(l_Lean_Meta_tracer___closed__3);
l_Lean_Meta_tracer___closed__4 = _init_l_Lean_Meta_tracer___closed__4();
lean_mark_persistent(l_Lean_Meta_tracer___closed__4);
l_Lean_Meta_tracer = _init_l_Lean_Meta_tracer();
lean_mark_persistent(l_Lean_Meta_tracer);
l_Lean_Meta_isClassExpensive___main___closed__1 = _init_l_Lean_Meta_isClassExpensive___main___closed__1();
lean_mark_persistent(l_Lean_Meta_isClassExpensive___main___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
