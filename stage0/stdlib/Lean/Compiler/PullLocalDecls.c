// Lean compiler output
// Module: Lean.Compiler.PullLocalDecls
// Imports: Init Lean.Compiler.CompilerM Lean.Compiler.Decl
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
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_dependsOn___boxed(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Compiler_Decl_pullInstances___closed__1;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_dependsOn___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_visitLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Compiler_mkLetUsingScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__3;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_PullLocalDecls_mkLambda___closed__3;
static lean_object* l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_visitLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_PullLocalDecls_visitLet___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_pullInstances___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_pullInstances(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_pullLocalDecls___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_Decl_mapValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_visitCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_visitLet___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_PullLocalDecls_visitLet___spec__1___closed__1;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_pullInstances___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_PullLocalDecls_visitLet___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_visitLet___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__5(lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_visitCases___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__4___lambda__1___boxed(lean_object**);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findUnsafe_x3f(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLiftReaderT(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value(lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__6;
lean_object* l_Lean_Compiler_mkLetDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__7;
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_PullLocalDecls_visitLet___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_PullLocalDecls_visitLet___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_PullLocalDecls_dependsOn___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_findDecl_x3f___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_PullLocalDecls_visitCases___closed__1;
static lean_object* l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__2;
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__1;
static lean_object* l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__2;
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__8;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__4;
static lean_object* l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__5;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_State_toPull___default;
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_Compiler_visitLambdaCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_PullLocalDecls___hyg_1426_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_findDecl_x3f___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__7;
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_pullLocalDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__2;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_visitCases___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___boxed(lean_object**);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__4;
static lean_object* l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__1;
static lean_object* l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
static lean_object* l_Lean_Compiler_PullLocalDecls_mkLambda___closed__4;
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_PullLocalDecls_mkLambda___closed__1;
static lean_object* l_Lean_Compiler_PullLocalDecls_mkLambda___closed__2;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_Compiler_check_checkBlock___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_visitLambda(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__3;
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__3___boxed(lean_object**);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__6;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_panic___at_Lean_Compiler_PullLocalDecls_visitLet___spec__1___closed__2;
lean_object* l_Lean_Compiler_isCasesApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_visitLet___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__8;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__4___boxed(lean_object**);
lean_object* l_Std_RBNode_findCore___at_Lean_Compiler_check_checkBlock___spec__3(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_PullLocalDecls_dependsOn(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__9;
static lean_object* l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__4;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__1;
extern lean_object* l_instInhabitedPUnit;
static lean_object* l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__10;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Compiler_PullLocalDecls_State_toPull___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_PullLocalDecls_dependsOn___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_isFVar(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Expr_fvarId_x21(x_2);
x_6 = l_Std_RBNode_findCore___at_Lean_Compiler_check_checkBlock___spec__3(x_1, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_PullLocalDecls_dependsOn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_PullLocalDecls_dependsOn___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 1;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_dependsOn___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_PullLocalDecls_dependsOn___lambda__1(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_dependsOn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_PullLocalDecls_dependsOn(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_findDecl_x3f___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_local_ctx_find(x_13, x_1);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_local_ctx_find(x_17, x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__1;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__2;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__3;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__4;
x_9 = lean_panic_fn(x_8, x_1);
x_10 = lean_apply_6(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_array_push(x_5, x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_box(0);
x_16 = l_Std_RBNode_insert___at_Lean_Compiler_check_checkBlock___spec__6(x_3, x_2, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_12);
return x_19;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.PullLocalDecls", 28);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.PullLocalDecls.mkLambda", 37);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__1;
x_2 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__2;
x_3 = lean_unsigned_to_nat(31u);
x_4 = lean_unsigned_to_nat(70u);
x_5 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Util", 9);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("getElem!", 8);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index out of bounds", 19);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__5;
x_2 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__6;
x_3 = lean_unsigned_to_nat(73u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__7;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_17 = x_12;
} else {
 lean_dec_ref(x_12);
 x_17 = lean_box(0);
}
x_18 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_18 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_5);
lean_dec(x_2);
x_96 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__8;
x_97 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_96);
x_19 = x_97;
goto block_95;
}
else
{
lean_object* x_98; 
x_98 = lean_array_fget(x_5, x_2);
lean_dec(x_2);
lean_dec(x_5);
x_19 = x_98;
goto block_95;
}
block_95:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_19);
x_20 = l_Lean_Expr_fvarId_x21(x_19);
x_21 = l_Lean_Compiler_findDecl_x3f___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__1(x_20, x_6, x_7, x_8, x_9, x_10, x_11);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_19);
lean_dec(x_4);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__4;
x_25 = l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2(x_24, x_6, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
if (lean_is_scalar(x_17)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_17;
}
lean_ctor_set(x_28, 0, x_15);
lean_ctor_set(x_28, 1, x_16);
if (lean_is_scalar(x_14)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_14;
}
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_25, 0, x_30);
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
if (lean_is_scalar(x_17)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_17;
}
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_16);
if (lean_is_scalar(x_14)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_14;
}
lean_ctor_set(x_33, 0, x_13);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_36 = !lean_is_exclusive(x_25);
if (x_36 == 0)
{
return x_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_25, 0);
x_38 = lean_ctor_get(x_25, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_25);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_22, 0);
lean_inc(x_40);
lean_dec(x_22);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_40);
lean_dec(x_19);
lean_dec(x_4);
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
lean_dec(x_21);
x_42 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__4;
x_43 = l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2(x_42, x_6, x_7, x_8, x_9, x_10, x_41);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
if (lean_is_scalar(x_17)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_17;
}
lean_ctor_set(x_46, 0, x_15);
lean_ctor_set(x_46, 1, x_16);
if (lean_is_scalar(x_14)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_14;
}
lean_ctor_set(x_47, 0, x_13);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_43, 0, x_48);
return x_43;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_dec(x_43);
if (lean_is_scalar(x_17)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_17;
}
lean_ctor_set(x_50, 0, x_15);
lean_ctor_set(x_50, 1, x_16);
if (lean_is_scalar(x_14)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_14;
}
lean_ctor_set(x_51, 0, x_13);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_54 = !lean_is_exclusive(x_43);
if (x_54 == 0)
{
return x_43;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_43, 0);
x_56 = lean_ctor_get(x_43, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_43);
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
x_58 = !lean_is_exclusive(x_21);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_21, 1);
x_60 = lean_ctor_get(x_21, 0);
lean_dec(x_60);
x_61 = lean_ctor_get(x_40, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_40, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_40, 4);
lean_inc(x_63);
lean_dec(x_40);
x_64 = l_Std_RBNode_findCore___at_Lean_Compiler_check_checkBlock___spec__3(x_4, x_61);
lean_dec(x_4);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_63);
lean_dec(x_62);
lean_free_object(x_21);
lean_dec(x_17);
lean_dec(x_14);
x_65 = lean_box(0);
x_66 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__1(x_19, x_61, x_13, x_15, x_16, x_65, x_6, x_7, x_8, x_9, x_10, x_59);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_66;
}
else
{
uint8_t x_67; 
lean_dec(x_64);
lean_inc(x_13);
x_67 = l_Lean_Compiler_PullLocalDecls_dependsOn(x_63, x_13);
if (x_67 == 0)
{
uint8_t x_68; 
lean_inc(x_13);
x_68 = l_Lean_Compiler_PullLocalDecls_dependsOn(x_62, x_13);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_61);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_69 = lean_array_push(x_15, x_19);
if (lean_is_scalar(x_17)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_17;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_16);
if (lean_is_scalar(x_14)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_14;
}
lean_ctor_set(x_71, 0, x_13);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_21, 0, x_72);
return x_21;
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_free_object(x_21);
lean_dec(x_17);
lean_dec(x_14);
x_73 = lean_box(0);
x_74 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__1(x_19, x_61, x_13, x_15, x_16, x_73, x_6, x_7, x_8, x_9, x_10, x_59);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_62);
lean_free_object(x_21);
lean_dec(x_17);
lean_dec(x_14);
x_75 = lean_box(0);
x_76 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__1(x_19, x_61, x_13, x_15, x_16, x_75, x_6, x_7, x_8, x_9, x_10, x_59);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_21, 1);
lean_inc(x_77);
lean_dec(x_21);
x_78 = lean_ctor_get(x_40, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_40, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_40, 4);
lean_inc(x_80);
lean_dec(x_40);
x_81 = l_Std_RBNode_findCore___at_Lean_Compiler_check_checkBlock___spec__3(x_4, x_78);
lean_dec(x_4);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_17);
lean_dec(x_14);
x_82 = lean_box(0);
x_83 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__1(x_19, x_78, x_13, x_15, x_16, x_82, x_6, x_7, x_8, x_9, x_10, x_77);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_83;
}
else
{
uint8_t x_84; 
lean_dec(x_81);
lean_inc(x_13);
x_84 = l_Lean_Compiler_PullLocalDecls_dependsOn(x_80, x_13);
if (x_84 == 0)
{
uint8_t x_85; 
lean_inc(x_13);
x_85 = l_Lean_Compiler_PullLocalDecls_dependsOn(x_79, x_13);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_78);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_86 = lean_array_push(x_15, x_19);
if (lean_is_scalar(x_17)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_17;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_16);
if (lean_is_scalar(x_14)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_14;
}
lean_ctor_set(x_88, 0, x_13);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_77);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_17);
lean_dec(x_14);
x_91 = lean_box(0);
x_92 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__1(x_19, x_78, x_13, x_15, x_16, x_91, x_6, x_7, x_8, x_9, x_10, x_77);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_79);
lean_dec(x_17);
lean_dec(x_14);
x_93 = lean_box(0);
x_94 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__1(x_19, x_78, x_13, x_15, x_16, x_93, x_6, x_7, x_8, x_9, x_10, x_77);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_94;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
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
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_apply_8(x_21, lean_box(0), x_19, x_13, x_14, x_15, x_16, x_17, x_18);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_nat_add(x_2, x_3);
lean_dec(x_2);
x_25 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_24, x_11, x_3, x_23, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_10);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_10, x_9);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_8, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_8, x_22);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_4);
lean_inc(x_5);
lean_inc(x_7);
lean_inc(x_9);
x_25 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2), 11, 5);
lean_closure_set(x_25, 0, x_12);
lean_closure_set(x_25, 1, x_9);
lean_closure_set(x_25, 2, x_7);
lean_closure_set(x_25, 3, x_5);
lean_closure_set(x_25, 4, x_4);
x_26 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__3___boxed), 18, 11);
lean_closure_set(x_26, 0, x_1);
lean_closure_set(x_26, 1, x_9);
lean_closure_set(x_26, 2, x_11);
lean_closure_set(x_26, 3, x_2);
lean_closure_set(x_26, 4, x_3);
lean_closure_set(x_26, 5, x_4);
lean_closure_set(x_26, 6, x_5);
lean_closure_set(x_26, 7, x_6);
lean_closure_set(x_26, 8, x_7);
lean_closure_set(x_26, 9, x_23);
lean_closure_set(x_26, 10, x_10);
x_27 = lean_apply_10(x_24, lean_box(0), lean_box(0), x_25, x_26, x_13, x_14, x_15, x_16, x_17, x_18);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_apply_8(x_29, lean_box(0), x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_apply_8(x_32, lean_box(0), x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_apply_8(x_20, lean_box(0), x_18, x_12, x_13, x_14, x_15, x_16, x_17);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_nat_add(x_2, x_3);
lean_dec(x_2);
x_24 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__4(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_23, x_10, x_3, x_22, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_9);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_9, x_8);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_7, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_7, x_21);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_4);
lean_inc(x_5);
lean_inc(x_6);
lean_inc(x_8);
x_24 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2), 11, 5);
lean_closure_set(x_24, 0, x_11);
lean_closure_set(x_24, 1, x_8);
lean_closure_set(x_24, 2, x_6);
lean_closure_set(x_24, 3, x_5);
lean_closure_set(x_24, 4, x_4);
x_25 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__4___lambda__1___boxed), 17, 10);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_8);
lean_closure_set(x_25, 2, x_10);
lean_closure_set(x_25, 3, x_2);
lean_closure_set(x_25, 4, x_3);
lean_closure_set(x_25, 5, x_4);
lean_closure_set(x_25, 6, x_5);
lean_closure_set(x_25, 7, x_6);
lean_closure_set(x_25, 8, x_22);
lean_closure_set(x_25, 9, x_9);
x_26 = lean_apply_10(x_23, lean_box(0), lean_box(0), x_24, x_25, x_12, x_13, x_14, x_15, x_16, x_17);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_apply_8(x_28, lean_box(0), x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_apply_8(x_31, lean_box(0), x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Expr_fvarId_x21(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_box(0);
x_11 = l_Std_RBNode_insert___at_Lean_Compiler_check_checkBlock___spec__6(x_4, x_7, x_10);
x_2 = x_9;
x_4 = x_11;
goto _start;
}
else
{
return x_4;
}
}
}
static lean_object* _init_l_Lean_Compiler_PullLocalDecls_mkLambda___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__2;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_PullLocalDecls_mkLambda___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_instMonadLiftReaderT), 3, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_PullLocalDecls_mkLambda___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_lift), 4, 3);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
lean_closure_set(x_1, 2, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_PullLocalDecls_mkLambda___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_mkLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_8, x_14);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_5, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = lean_array_get_size(x_1);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
x_25 = lean_array_get_size(x_15);
x_26 = l_Lean_Compiler_PullLocalDecls_mkLambda___closed__4;
lean_inc(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_1);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_1);
x_28 = x_21;
goto block_65;
}
else
{
uint8_t x_66; 
x_66 = lean_nat_dec_le(x_22, x_22);
if (x_66 == 0)
{
lean_dec(x_22);
lean_dec(x_1);
x_28 = x_21;
goto block_65;
}
else
{
size_t x_67; size_t x_68; lean_object* x_69; 
x_67 = 0;
x_68 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_69 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__5(x_1, x_67, x_68, x_21);
lean_dec(x_1);
x_28 = x_69;
goto block_65;
}
}
block_65:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_Compiler_PullLocalDecls_mkLambda___closed__1;
x_31 = l_Lean_Compiler_PullLocalDecls_mkLambda___closed__2;
x_32 = l_Lean_Compiler_PullLocalDecls_mkLambda___closed__3;
x_33 = lean_unsigned_to_nat(1u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc_n(x_25, 2);
x_34 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__4(x_30, x_31, x_32, x_15, x_19, x_25, x_25, x_2, x_25, x_33, x_29, x_4, x_5, x_6, x_7, x_8, x_20);
lean_dec(x_25);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_st_ref_get(x_8, x_37);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_st_ref_take(x_6, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_43, 1);
x_47 = l_Array_shrink___rarg(x_46, x_2);
lean_dec(x_2);
x_48 = l_Array_append___rarg(x_47, x_38);
lean_ctor_set(x_43, 1, x_48);
x_49 = lean_st_ref_set(x_6, x_43, x_44);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_Lean_Compiler_mkLambda(x_39, x_3, x_6, x_7, x_8, x_50);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_39);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_43, 0);
x_53 = lean_ctor_get(x_43, 1);
x_54 = lean_ctor_get(x_43, 2);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_43);
x_55 = l_Array_shrink___rarg(x_53, x_2);
lean_dec(x_2);
x_56 = l_Array_append___rarg(x_55, x_38);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_54);
x_58 = lean_st_ref_set(x_6, x_57, x_44);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_Lean_Compiler_mkLambda(x_39, x_3, x_6, x_7, x_8, x_59);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_39);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_34);
if (x_61 == 0)
{
return x_34;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_34, 0);
x_63 = lean_ctor_get(x_34, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_34);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_findDecl_x3f___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_findDecl_x3f___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__3___boxed(lean_object** _args) {
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
lean_object* x_19; 
x_19 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___boxed(lean_object** _args) {
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
lean_object* x_19; 
x_19 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_8);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__4___lambda__1___boxed(lean_object** _args) {
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
lean_object* x_18; 
x_18 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__4___boxed(lean_object** _args) {
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
lean_object* x_18; 
x_18 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_visitLambda(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = l_Lean_Compiler_visitLambdaCore(x_1, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_st_ref_get(x_7, x_11);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_5, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_get_size(x_19);
lean_dec(x_19);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_12);
x_21 = l_Lean_Compiler_PullLocalDecls_visitLet(x_13, x_12, x_3, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_21) == 0)
{
if (x_2 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Compiler_PullLocalDecls_mkLambda(x_12, x_20, x_22, x_3, x_4, x_5, x_6, x_7, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_3);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_27 = l_Lean_Compiler_mkLetUsingScope(x_25, x_5, x_6, x_7, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Compiler_mkLambda(x_12, x_28, x_5, x_6, x_7, x_29);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_12);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_PullLocalDecls_visitLet___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__2;
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_PullLocalDecls_visitLet___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_PullLocalDecls_visitLet___spec__1___closed__1;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_PullLocalDecls_visitLet___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_panic___at_Lean_Compiler_PullLocalDecls_visitLet___spec__1___closed__2;
x_9 = lean_panic_fn(x_8, x_1);
x_10 = lean_apply_6(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at_Lean_Compiler_PullLocalDecls_visitLet___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_PullLocalDecls_visitLet___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_PullLocalDecls_visitLet___spec__2___closed__1;
x_11 = lean_st_ref_get(x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_5, 2);
x_15 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_13, x_14, x_1);
lean_dec(x_13);
x_16 = lean_box(x_15);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_ctor_get(x_5, 2);
x_20 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_17, x_19, x_1);
lean_dec(x_17);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__3;
x_3 = l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__4;
x_4 = l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__5;
x_5 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set(x_5, 5, x_2);
lean_ctor_set(x_5, 6, x_3);
lean_ctor_set(x_5, 7, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_st_ref_get(x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_7, x_12);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_5, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_6, 2);
x_21 = l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__6;
lean_inc(x_20);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_20);
x_23 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_2);
x_24 = lean_st_ref_take(x_7, x_18);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_28 = lean_ctor_get(x_25, 3);
x_29 = l_Lean_Compiler_PullLocalDecls_mkLambda___closed__4;
x_30 = 0;
x_31 = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_30);
lean_inc(x_9);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_9);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Std_PersistentArray_push___rarg(x_28, x_32);
lean_ctor_set(x_25, 3, x_33);
x_34 = lean_st_ref_set(x_7, x_25, x_26);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_41 = lean_ctor_get(x_25, 0);
x_42 = lean_ctor_get(x_25, 1);
x_43 = lean_ctor_get(x_25, 2);
x_44 = lean_ctor_get(x_25, 3);
x_45 = lean_ctor_get(x_25, 4);
x_46 = lean_ctor_get(x_25, 5);
x_47 = lean_ctor_get(x_25, 6);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_25);
x_48 = l_Lean_Compiler_PullLocalDecls_mkLambda___closed__4;
x_49 = 0;
x_50 = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_23);
lean_ctor_set(x_50, 2, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*3, x_49);
lean_inc(x_9);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_9);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Std_PersistentArray_push___rarg(x_44, x_51);
x_53 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_53, 0, x_41);
lean_ctor_set(x_53, 1, x_42);
lean_ctor_set(x_53, 2, x_43);
lean_ctor_set(x_53, 3, x_52);
lean_ctor_set(x_53, 4, x_45);
lean_ctor_set(x_53, 5, x_46);
lean_ctor_set(x_53, 6, x_47);
x_54 = lean_st_ref_set(x_7, x_53, x_26);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_visitLet___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = lean_array_push(x_1, x_2);
x_12 = l_Lean_Compiler_PullLocalDecls_visitLet(x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_visitLet___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_take(x_5, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_LocalDecl_fvarId(x_1);
x_16 = lean_box(0);
x_17 = l_Std_RBNode_insert___at_Lean_Compiler_check_checkBlock___spec__6(x_13, x_15, x_16);
x_18 = lean_st_ref_set(x_5, x_17, x_14);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_apply_7(x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_19);
return x_20;
}
}
static lean_object* _init_l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.PullLocalDecls.visitLet", 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__1;
x_2 = l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__1;
x_3 = lean_unsigned_to_nat(67u);
x_4 = lean_unsigned_to_nat(47u);
x_5 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Compiler", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("pullLocalDecls", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__4;
x_2 = l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("candidate", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__6;
x_2 = l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_14 = l_Lean_Compiler_mkLetDecl(x_1, x_2, x_6, x_3, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_15);
x_17 = l_Lean_Expr_fvarId_x21(x_15);
x_18 = l_Lean_Compiler_findDecl_x3f___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__1(x_17, x_8, x_9, x_10, x_11, x_12, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__2;
x_22 = l_panic___at_Lean_Compiler_PullLocalDecls_visitLet___spec__1(x_21, x_8, x_9, x_10, x_11, x_12, x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_st_ref_get(x_12, x_23);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_get(x_9, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_8);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_24);
x_30 = lean_apply_6(x_8, x_24, x_28, x_10, x_11, x_12, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_24);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_box(0);
x_35 = l_Lean_Compiler_PullLocalDecls_visitLet___lambda__1(x_4, x_15, x_5, x_34, x_8, x_9, x_10, x_11, x_12, x_33);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
lean_inc(x_15);
x_37 = lean_alloc_closure((void*)(l_Lean_Compiler_PullLocalDecls_visitLet___lambda__1), 10, 3);
lean_closure_set(x_37, 0, x_4);
lean_closure_set(x_37, 1, x_15);
lean_closure_set(x_37, 2, x_5);
x_38 = l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__8;
x_39 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_PullLocalDecls_visitLet___spec__2(x_38, x_8, x_9, x_10, x_11, x_12, x_36);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_15);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_box(0);
x_44 = l_Lean_Compiler_PullLocalDecls_visitLet___lambda__2(x_24, x_37, x_43, x_8, x_9, x_10, x_11, x_12, x_42);
lean_dec(x_24);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_15);
x_47 = l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__10;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3(x_38, x_49, x_8, x_9, x_10, x_11, x_12, x_45);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Compiler_PullLocalDecls_visitLet___lambda__2(x_24, x_37, x_51, x_8, x_9, x_10, x_11, x_12, x_52);
lean_dec(x_51);
lean_dec(x_24);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_30);
if (x_54 == 0)
{
return x_30;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_30, 0);
x_56 = lean_ctor_get(x_30, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_30);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_visitLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec(x_1);
x_14 = lean_expr_instantiate_rev(x_10, x_2);
lean_dec(x_10);
x_15 = lean_expr_instantiate_rev(x_11, x_2);
lean_dec(x_11);
x_16 = l_Lean_Expr_isLambda(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3(x_9, x_14, x_13, x_2, x_12, x_15, x_17, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
else
{
uint8_t x_19; lean_object* x_20; 
x_19 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l_Lean_Compiler_PullLocalDecls_visitLambda(x_15, x_19, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3(x_9, x_14, x_13, x_2, x_12, x_21, x_23, x_3, x_4, x_5, x_6, x_7, x_22);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_29);
x_30 = l_Lean_Compiler_isCasesApp_x3f(x_29, x_6, x_7, x_8);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l_Lean_Compiler_PullLocalDecls_visitCases(x_37, x_29, x_3, x_4, x_5, x_6, x_7, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_29);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
return x_30;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_30, 0);
x_41 = lean_ctor_get(x_30, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_30);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_visitCases___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_1, x_15);
lean_dec(x_1);
x_17 = lean_array_get_size(x_5);
x_18 = lean_nat_dec_lt(x_2, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_16;
x_2 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_21 = lean_array_fget(x_5, x_2);
x_22 = lean_box(0);
x_23 = lean_array_fset(x_5, x_2, x_22);
x_24 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_25 = l_Lean_Compiler_PullLocalDecls_visitLambda(x_21, x_24, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_array_fset(x_23, x_2, x_26);
x_29 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_16;
x_2 = x_29;
x_5 = x_28;
x_11 = x_27;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
lean_object* x_35; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_11);
return x_35;
}
}
else
{
lean_object* x_36; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_5);
lean_ctor_set(x_36, 1, x_11);
return x_36;
}
}
}
static lean_object* _init_l_Lean_Compiler_PullLocalDecls_visitCases___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_visitCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_9);
x_11 = l_Lean_Compiler_PullLocalDecls_visitCases___closed__1;
lean_inc(x_10);
x_12 = lean_mk_array(x_10, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_10, x_13);
lean_dec(x_10);
lean_inc(x_2);
x_15 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_12, x_14);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 2);
lean_inc(x_19);
lean_dec(x_16);
lean_inc(x_17);
x_20 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_visitCases___spec__1(x_17, x_18, x_17, x_19, x_15, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_19);
lean_dec(x_17);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Lean_Expr_getAppFn(x_2);
lean_dec(x_2);
x_24 = l_Lean_mkAppN(x_23, x_22);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = l_Lean_Expr_getAppFn(x_2);
lean_dec(x_2);
x_28 = l_Lean_mkAppN(x_27, x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_visitLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Compiler_PullLocalDecls_visitLambda(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_PullLocalDecls_visitLet___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_PullLocalDecls_visitLet___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_visitLet___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_PullLocalDecls_visitLet___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_visitCases___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_visitCases___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_pullLocalDecls___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_7 = lean_box(0);
x_8 = lean_st_ref_get(x_5, x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_mk_ref(x_7, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
lean_inc(x_5);
lean_inc(x_11);
x_14 = l_Lean_Compiler_PullLocalDecls_visitLambda(x_2, x_13, x_1, x_11, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_5, x_16);
lean_dec(x_5);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_11, x_18);
lean_dec(x_11);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_15);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_11);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_pullLocalDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_Decl_pullLocalDecls___lambda__1), 6, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = l_Lean_Compiler_Decl_mapValue(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_pullInstances___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_LocalDecl_type(x_1);
x_8 = l_Lean_Compiler_isClass_x3f(x_7, x_4, x_5, x_6);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = l_Lean_LocalDecl_value(x_1);
if (lean_obj_tag(x_12) == 11)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Std_RBNode_findCore___at_Lean_Compiler_check_checkBlock___spec__3(x_2, x_14);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; lean_object* x_17; 
x_16 = 0;
x_17 = lean_box(x_16);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
else
{
uint8_t x_18; lean_object* x_19; 
lean_dec(x_15);
x_18 = 1;
x_19 = lean_box(x_18);
lean_ctor_set(x_8, 0, x_19);
return x_8;
}
}
else
{
uint8_t x_20; lean_object* x_21; 
lean_dec(x_13);
x_20 = 0;
x_21 = lean_box(x_20);
lean_ctor_set(x_8, 0, x_21);
return x_8;
}
}
else
{
uint8_t x_22; lean_object* x_23; 
lean_dec(x_12);
x_22 = 0;
x_23 = lean_box(x_22);
lean_ctor_set(x_8, 0, x_23);
return x_8;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_dec(x_8);
x_25 = l_Lean_LocalDecl_value(x_1);
if (lean_obj_tag(x_25) == 11)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 2);
lean_inc(x_26);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Std_RBNode_findCore___at_Lean_Compiler_check_checkBlock___spec__3(x_2, x_27);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_29 = 0;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
return x_31;
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_28);
x_32 = 1;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_24);
return x_34;
}
}
else
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_26);
x_35 = 0;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_24);
return x_37;
}
}
else
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_25);
x_38 = 0;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_24);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_9);
x_41 = !lean_is_exclusive(x_8);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_8, 0);
lean_dec(x_42);
x_43 = 1;
x_44 = lean_box(x_43);
lean_ctor_set(x_8, 0, x_44);
return x_8;
}
else
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_8, 1);
lean_inc(x_45);
lean_dec(x_8);
x_46 = 1;
x_47 = lean_box(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_Decl_pullInstances___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_Decl_pullInstances___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_pullInstances(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Compiler_Decl_pullInstances___closed__1;
x_6 = l_Lean_Compiler_Decl_pullLocalDecls(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_pullInstances___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_Decl_pullInstances___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_PullLocalDecls___hyg_1426_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__8;
x_3 = 0;
x_4 = l_Lean_registerTraceClass(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_Decl(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_PullLocalDecls(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Decl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_PullLocalDecls_State_toPull___default = _init_l_Lean_Compiler_PullLocalDecls_State_toPull___default();
lean_mark_persistent(l_Lean_Compiler_PullLocalDecls_State_toPull___default);
l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__1 = _init_l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__1);
l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__2 = _init_l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__2);
l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__3 = _init_l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__3();
lean_mark_persistent(l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__3);
l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__4 = _init_l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__4();
lean_mark_persistent(l_panic___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__2___closed__4);
l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__1);
l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__2 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__2);
l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__3 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__3);
l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__4 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__4();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__4);
l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__5 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__5();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__5);
l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__6 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__6();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__6);
l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__7 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__7();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__7);
l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__8 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__8();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_PullLocalDecls_mkLambda___spec__3___lambda__2___closed__8);
l_Lean_Compiler_PullLocalDecls_mkLambda___closed__1 = _init_l_Lean_Compiler_PullLocalDecls_mkLambda___closed__1();
lean_mark_persistent(l_Lean_Compiler_PullLocalDecls_mkLambda___closed__1);
l_Lean_Compiler_PullLocalDecls_mkLambda___closed__2 = _init_l_Lean_Compiler_PullLocalDecls_mkLambda___closed__2();
lean_mark_persistent(l_Lean_Compiler_PullLocalDecls_mkLambda___closed__2);
l_Lean_Compiler_PullLocalDecls_mkLambda___closed__3 = _init_l_Lean_Compiler_PullLocalDecls_mkLambda___closed__3();
lean_mark_persistent(l_Lean_Compiler_PullLocalDecls_mkLambda___closed__3);
l_Lean_Compiler_PullLocalDecls_mkLambda___closed__4 = _init_l_Lean_Compiler_PullLocalDecls_mkLambda___closed__4();
lean_mark_persistent(l_Lean_Compiler_PullLocalDecls_mkLambda___closed__4);
l_panic___at_Lean_Compiler_PullLocalDecls_visitLet___spec__1___closed__1 = _init_l_panic___at_Lean_Compiler_PullLocalDecls_visitLet___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_PullLocalDecls_visitLet___spec__1___closed__1);
l_panic___at_Lean_Compiler_PullLocalDecls_visitLet___spec__1___closed__2 = _init_l_panic___at_Lean_Compiler_PullLocalDecls_visitLet___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_PullLocalDecls_visitLet___spec__1___closed__2);
l_Lean_isTracingEnabledFor___at_Lean_Compiler_PullLocalDecls_visitLet___spec__2___closed__1 = _init_l_Lean_isTracingEnabledFor___at_Lean_Compiler_PullLocalDecls_visitLet___spec__2___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at_Lean_Compiler_PullLocalDecls_visitLet___spec__2___closed__1);
l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__1 = _init_l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__1();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__1);
l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__2 = _init_l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__2);
l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__3 = _init_l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__3();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__3);
l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__4 = _init_l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__4();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__4);
l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__5 = _init_l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__5();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__5);
l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__6 = _init_l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__6();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_PullLocalDecls_visitLet___spec__3___closed__6);
l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__1 = _init_l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__1);
l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__2 = _init_l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__2);
l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__3 = _init_l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__3);
l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__4 = _init_l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__4);
l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__5 = _init_l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__5);
l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__6 = _init_l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__6);
l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__7 = _init_l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__7);
l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__8 = _init_l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__8();
lean_mark_persistent(l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__8);
l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__9 = _init_l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__9();
lean_mark_persistent(l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__9);
l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__10 = _init_l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__10();
lean_mark_persistent(l_Lean_Compiler_PullLocalDecls_visitLet___lambda__3___closed__10);
l_Lean_Compiler_PullLocalDecls_visitCases___closed__1 = _init_l_Lean_Compiler_PullLocalDecls_visitCases___closed__1();
lean_mark_persistent(l_Lean_Compiler_PullLocalDecls_visitCases___closed__1);
l_Lean_Compiler_Decl_pullInstances___closed__1 = _init_l_Lean_Compiler_Decl_pullInstances___closed__1();
lean_mark_persistent(l_Lean_Compiler_Decl_pullInstances___closed__1);
res = l_Lean_Compiler_initFn____x40_Lean_Compiler_PullLocalDecls___hyg_1426_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
