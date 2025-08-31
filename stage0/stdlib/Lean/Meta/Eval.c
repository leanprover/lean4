// Lean compiler output
// Module: Lean.Meta.Eval
// Imports: Lean.AddDecl Lean.Meta.Check Lean.Util.CollectLevelParams
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
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_isImportedConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_evalExprCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Meta_evalExprCore_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_KVMap_find(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__15;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___closed__1;
lean_object* l_Lean_Environment_importEnv_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__1;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__16;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9;
LEAN_EXPORT lean_object* l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_Meta_evalExprCore_spec__3___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__0;
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_evalExprCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__3;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__14;
extern lean_object* l_Lean_Elab_async;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___Lean_Meta_evalExprCore_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Meta_evalExprCore_spec__8(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_traceBlock___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11;
lean_object* l_Lean_collectLevelParams(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___Lean_Meta_evalExprCore_spec__2(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___closed__0;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_evalExprCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___Lean_Meta_evalExprCore_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_evalExprCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__2;
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12;
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_Meta_evalExprCore_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_Meta_evalExprCore_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_evalExprCore_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_evalExprCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___Lean_Meta_evalExprCore_spec__0___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___Lean_Meta_evalExprCore_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_5, 0, x_3);
x_6 = l_Lean_KVMap_insert(x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___Lean_Meta_evalExprCore_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_find(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec_ref(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec_ref(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_Meta_evalExprCore_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_find(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_6) == 3)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
return x_7;
}
else
{
lean_dec(x_6);
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4_spec__4_spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = l_Lean_stringToMessageData(x_7);
x_9 = l_Lean_throwError___at___Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4_spec__4___redArg(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_5, 2);
x_13 = l_Lean_Environment_evalConst___redArg(x_11, x_12, x_1, x_2);
x_14 = l_Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4___redArg(x_13, x_3, x_4, x_5, x_6, x_10);
lean_dec_ref(x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Meta_evalExprCore_spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_6 = 1;
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_Lean_Environment_isImportedConst(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
return x_6;
}
else
{
if (x_5 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
return x_6;
}
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
static lean_object* _init_l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__1;
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_ctor_get(x_6, 5);
lean_dec(x_9);
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__2;
lean_ctor_set(x_6, 5, x_11);
lean_ctor_set(x_6, 0, x_1);
x_12 = lean_st_ref_set(x_3, x_6, x_7);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_st_ref_take(x_2, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_15, 1);
lean_dec(x_18);
x_19 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__3;
lean_ctor_set(x_15, 1, x_19);
x_20 = lean_st_ref_set(x_2, x_15, x_16);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 2);
x_29 = lean_ctor_get(x_15, 3);
x_30 = lean_ctor_get(x_15, 4);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_31 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__3;
x_32 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_28);
lean_ctor_set(x_32, 3, x_29);
lean_ctor_set(x_32, 4, x_30);
x_33 = lean_st_ref_set(x_2, x_32, x_16);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_38 = lean_ctor_get(x_6, 1);
x_39 = lean_ctor_get(x_6, 2);
x_40 = lean_ctor_get(x_6, 3);
x_41 = lean_ctor_get(x_6, 4);
x_42 = lean_ctor_get(x_6, 6);
x_43 = lean_ctor_get(x_6, 7);
x_44 = lean_ctor_get(x_6, 8);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_6);
x_45 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__2;
x_46 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_38);
lean_ctor_set(x_46, 2, x_39);
lean_ctor_set(x_46, 3, x_40);
lean_ctor_set(x_46, 4, x_41);
lean_ctor_set(x_46, 5, x_45);
lean_ctor_set(x_46, 6, x_42);
lean_ctor_set(x_46, 7, x_43);
lean_ctor_set(x_46, 8, x_44);
x_47 = lean_st_ref_set(x_3, x_46, x_7);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = lean_st_ref_take(x_2, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec_ref(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_50, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_50, 3);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_50, 4);
lean_inc_ref(x_55);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 lean_ctor_release(x_50, 2);
 lean_ctor_release(x_50, 3);
 lean_ctor_release(x_50, 4);
 x_56 = x_50;
} else {
 lean_dec_ref(x_50);
 x_56 = lean_box(0);
}
x_57 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__3;
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 5, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_58, 2, x_53);
lean_ctor_set(x_58, 3, x_54);
lean_ctor_set(x_58, 4, x_55);
x_59 = lean_st_ref_set(x_2, x_58, x_51);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
x_62 = lean_box(0);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg(x_1, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg(x_1, x_4, x_6, x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc(x_6);
lean_inc(x_4);
x_14 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg(x_11, x_4, x_6, x_16);
lean_dec(x_6);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_dec_ref(x_14);
x_24 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg(x_11, x_4, x_6, x_23);
lean_dec(x_6);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_22);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiler env", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_async;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_tmp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11;
x_2 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to evaluate expression, it contains metavariables", 56, 56);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; 
x_276 = lean_st_ref_get(x_7, x_8);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec_ref(x_276);
lean_inc_ref(x_3);
x_293 = l_Lean_Expr_getUsedConstants(x_3);
x_294 = lean_unsigned_to_nat(0u);
x_295 = lean_array_get_size(x_293);
x_296 = lean_nat_dec_lt(x_294, x_295);
if (x_296 == 0)
{
lean_dec(x_295);
lean_dec_ref(x_293);
lean_dec(x_277);
goto block_292;
}
else
{
if (x_296 == 0)
{
lean_dec(x_295);
lean_dec_ref(x_293);
lean_dec(x_277);
goto block_292;
}
else
{
lean_object* x_297; size_t x_298; size_t x_299; uint8_t x_300; 
x_297 = lean_ctor_get(x_277, 0);
lean_inc_ref(x_297);
lean_dec(x_277);
x_298 = 0;
x_299 = lean_usize_of_nat(x_295);
lean_dec(x_295);
x_300 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Meta_evalExprCore_spec__8(x_297, x_293, x_298, x_299);
lean_dec_ref(x_293);
lean_dec_ref(x_297);
if (x_300 == 0)
{
goto block_292;
}
else
{
x_197 = x_4;
x_198 = x_5;
x_199 = x_6;
x_200 = x_7;
x_201 = x_278;
goto block_245;
}
}
}
block_41:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0;
x_32 = l_Lean_Option_get___at___Lean_Meta_evalExprCore_spec__3(x_15, x_31);
x_33 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_33, 0, x_16);
lean_ctor_set(x_33, 1, x_17);
lean_ctor_set(x_33, 2, x_15);
lean_ctor_set(x_33, 3, x_18);
lean_ctor_set(x_33, 4, x_32);
lean_ctor_set(x_33, 5, x_19);
lean_ctor_set(x_33, 6, x_20);
lean_ctor_set(x_33, 7, x_21);
lean_ctor_set(x_33, 8, x_22);
lean_ctor_set(x_33, 9, x_23);
lean_ctor_set(x_33, 10, x_24);
lean_ctor_set(x_33, 11, x_25);
lean_ctor_set(x_33, 12, x_26);
lean_ctor_set(x_33, 13, x_28);
lean_ctor_set_uint8(x_33, sizeof(void*)*14, x_10);
lean_ctor_set_uint8(x_33, sizeof(void*)*14 + 1, x_27);
lean_inc(x_29);
lean_inc_ref(x_33);
x_34 = l_Lean_addAndCompile(x_12, x_13, x_33, x_29, x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4___redArg(x_14, x_13, x_11, x_9, x_33, x_29, x_35);
lean_dec(x_29);
lean_dec_ref(x_33);
lean_dec(x_9);
lean_dec_ref(x_11);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec_ref(x_33);
lean_dec(x_29);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec(x_9);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
block_65:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_52 = lean_ctor_get(x_49, 0);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_49, 1);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_49, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_49, 5);
lean_inc(x_55);
x_56 = lean_ctor_get(x_49, 6);
lean_inc(x_56);
x_57 = lean_ctor_get(x_49, 7);
lean_inc(x_57);
x_58 = lean_ctor_get(x_49, 8);
lean_inc(x_58);
x_59 = lean_ctor_get(x_49, 9);
lean_inc(x_59);
x_60 = lean_ctor_get(x_49, 10);
lean_inc(x_60);
x_61 = lean_ctor_get(x_49, 11);
lean_inc(x_61);
x_62 = lean_ctor_get(x_49, 12);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_49, sizeof(void*)*14 + 1);
x_64 = lean_ctor_get(x_49, 13);
lean_inc_ref(x_64);
lean_dec_ref(x_49);
x_9 = x_42;
x_10 = x_43;
x_11 = x_44;
x_12 = x_45;
x_13 = x_46;
x_14 = x_47;
x_15 = x_48;
x_16 = x_52;
x_17 = x_53;
x_18 = x_54;
x_19 = x_55;
x_20 = x_56;
x_21 = x_57;
x_22 = x_58;
x_23 = x_59;
x_24 = x_60;
x_25 = x_61;
x_26 = x_62;
x_27 = x_63;
x_28 = x_64;
x_29 = x_50;
x_30 = x_51;
goto block_41;
}
block_100:
{
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_st_ref_take(x_75, x_74);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec_ref(x_77);
x_80 = !lean_is_exclusive(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_78, 0);
x_82 = lean_ctor_get(x_78, 5);
lean_dec(x_82);
x_83 = l_Lean_Kernel_enableDiag(x_81, x_67);
x_84 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__2;
lean_ctor_set(x_78, 5, x_84);
lean_ctor_set(x_78, 0, x_83);
x_85 = lean_st_ref_set(x_75, x_78, x_79);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec_ref(x_85);
x_42 = x_66;
x_43 = x_67;
x_44 = x_68;
x_45 = x_70;
x_46 = x_71;
x_47 = x_72;
x_48 = x_73;
x_49 = x_69;
x_50 = x_75;
x_51 = x_86;
goto block_65;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_87 = lean_ctor_get(x_78, 0);
x_88 = lean_ctor_get(x_78, 1);
x_89 = lean_ctor_get(x_78, 2);
x_90 = lean_ctor_get(x_78, 3);
x_91 = lean_ctor_get(x_78, 4);
x_92 = lean_ctor_get(x_78, 6);
x_93 = lean_ctor_get(x_78, 7);
x_94 = lean_ctor_get(x_78, 8);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_78);
x_95 = l_Lean_Kernel_enableDiag(x_87, x_67);
x_96 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__2;
x_97 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_88);
lean_ctor_set(x_97, 2, x_89);
lean_ctor_set(x_97, 3, x_90);
lean_ctor_set(x_97, 4, x_91);
lean_ctor_set(x_97, 5, x_96);
lean_ctor_set(x_97, 6, x_92);
lean_ctor_set(x_97, 7, x_93);
lean_ctor_set(x_97, 8, x_94);
x_98 = lean_st_ref_set(x_75, x_97, x_79);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec_ref(x_98);
x_42 = x_66;
x_43 = x_67;
x_44 = x_68;
x_45 = x_70;
x_46 = x_71;
x_47 = x_72;
x_48 = x_73;
x_49 = x_69;
x_50 = x_75;
x_51 = x_99;
goto block_65;
}
}
else
{
x_42 = x_66;
x_43 = x_67;
x_44 = x_68;
x_45 = x_70;
x_46 = x_71;
x_47 = x_72;
x_48 = x_73;
x_49 = x_69;
x_50 = x_75;
x_51 = x_74;
goto block_65;
}
}
block_196:
{
lean_object* x_110; 
lean_inc(x_108);
lean_inc_ref(x_107);
lean_inc(x_106);
lean_inc_ref(x_105);
lean_inc_ref(x_103);
x_110 = lean_infer_type(x_103, x_105, x_106, x_107, x_108, x_109);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec_ref(x_110);
lean_inc(x_108);
lean_inc_ref(x_107);
lean_inc(x_106);
lean_inc_ref(x_105);
lean_inc(x_111);
x_113 = lean_apply_6(x_1, x_111, x_105, x_106, x_107, x_108, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec_ref(x_113);
x_115 = lean_st_ref_get(x_108, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_116, 0);
lean_inc_ref(x_117);
lean_dec(x_116);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec_ref(x_115);
x_119 = lean_ctor_get(x_117, 2);
lean_inc_ref(x_119);
lean_dec_ref(x_117);
x_120 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1;
lean_inc(x_108);
lean_inc_ref(x_107);
x_121 = l_Lean_traceBlock___redArg(x_120, x_119, x_107, x_108, x_118);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec_ref(x_121);
x_123 = lean_st_ref_get(x_108, x_122);
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; uint8_t x_153; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_ctor_get(x_123, 1);
x_127 = lean_ctor_get(x_107, 0);
x_128 = lean_ctor_get(x_107, 1);
x_129 = lean_ctor_get(x_107, 2);
x_130 = lean_ctor_get(x_107, 3);
x_131 = lean_ctor_get(x_107, 5);
x_132 = lean_ctor_get(x_107, 6);
x_133 = lean_ctor_get(x_107, 7);
x_134 = lean_ctor_get(x_107, 8);
x_135 = lean_ctor_get(x_107, 9);
x_136 = lean_ctor_get(x_107, 10);
x_137 = lean_ctor_get(x_107, 11);
x_138 = lean_ctor_get(x_107, 12);
x_139 = lean_ctor_get_uint8(x_107, sizeof(void*)*14 + 1);
x_140 = lean_ctor_get(x_107, 13);
x_141 = lean_ctor_get(x_125, 0);
lean_inc_ref(x_141);
lean_dec(x_125);
x_142 = lean_array_to_list(x_101);
lean_inc(x_104);
x_143 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_143, 0, x_104);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set(x_143, 2, x_111);
x_144 = lean_box(0);
lean_inc(x_104);
lean_ctor_set_tag(x_123, 1);
lean_ctor_set(x_123, 1, x_102);
lean_ctor_set(x_123, 0, x_104);
x_145 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_103);
lean_ctor_set(x_145, 2, x_144);
lean_ctor_set(x_145, 3, x_123);
lean_ctor_set_uint8(x_145, sizeof(void*)*4, x_2);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = 1;
x_148 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2;
x_149 = 0;
lean_inc(x_129);
x_150 = l_Lean_Option_set___at___Lean_Meta_evalExprCore_spec__1(x_129, x_148, x_149);
x_151 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3;
x_152 = l_Lean_Option_get___at___Lean_Meta_evalExprCore_spec__2(x_150, x_151);
x_153 = l_Lean_Kernel_isDiagnosticsEnabled(x_141);
lean_dec_ref(x_141);
if (x_153 == 0)
{
if (x_152 == 0)
{
lean_inc_ref(x_140);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc_ref(x_128);
lean_inc_ref(x_127);
lean_dec_ref(x_107);
x_9 = x_106;
x_10 = x_152;
x_11 = x_105;
x_12 = x_146;
x_13 = x_147;
x_14 = x_104;
x_15 = x_150;
x_16 = x_127;
x_17 = x_128;
x_18 = x_130;
x_19 = x_131;
x_20 = x_132;
x_21 = x_133;
x_22 = x_134;
x_23 = x_135;
x_24 = x_136;
x_25 = x_137;
x_26 = x_138;
x_27 = x_139;
x_28 = x_140;
x_29 = x_108;
x_30 = x_126;
goto block_41;
}
else
{
x_66 = x_106;
x_67 = x_152;
x_68 = x_105;
x_69 = x_107;
x_70 = x_146;
x_71 = x_147;
x_72 = x_104;
x_73 = x_150;
x_74 = x_126;
x_75 = x_108;
x_76 = x_153;
goto block_100;
}
}
else
{
x_66 = x_106;
x_67 = x_152;
x_68 = x_105;
x_69 = x_107;
x_70 = x_146;
x_71 = x_147;
x_72 = x_104;
x_73 = x_150;
x_74 = x_126;
x_75 = x_108;
x_76 = x_152;
goto block_100;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; uint8_t x_183; 
x_154 = lean_ctor_get(x_123, 0);
x_155 = lean_ctor_get(x_123, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_123);
x_156 = lean_ctor_get(x_107, 0);
x_157 = lean_ctor_get(x_107, 1);
x_158 = lean_ctor_get(x_107, 2);
x_159 = lean_ctor_get(x_107, 3);
x_160 = lean_ctor_get(x_107, 5);
x_161 = lean_ctor_get(x_107, 6);
x_162 = lean_ctor_get(x_107, 7);
x_163 = lean_ctor_get(x_107, 8);
x_164 = lean_ctor_get(x_107, 9);
x_165 = lean_ctor_get(x_107, 10);
x_166 = lean_ctor_get(x_107, 11);
x_167 = lean_ctor_get(x_107, 12);
x_168 = lean_ctor_get_uint8(x_107, sizeof(void*)*14 + 1);
x_169 = lean_ctor_get(x_107, 13);
x_170 = lean_ctor_get(x_154, 0);
lean_inc_ref(x_170);
lean_dec(x_154);
x_171 = lean_array_to_list(x_101);
lean_inc(x_104);
x_172 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_172, 0, x_104);
lean_ctor_set(x_172, 1, x_171);
lean_ctor_set(x_172, 2, x_111);
x_173 = lean_box(0);
lean_inc(x_104);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_104);
lean_ctor_set(x_174, 1, x_102);
x_175 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_103);
lean_ctor_set(x_175, 2, x_173);
lean_ctor_set(x_175, 3, x_174);
lean_ctor_set_uint8(x_175, sizeof(void*)*4, x_2);
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_175);
x_177 = 1;
x_178 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2;
x_179 = 0;
lean_inc(x_158);
x_180 = l_Lean_Option_set___at___Lean_Meta_evalExprCore_spec__1(x_158, x_178, x_179);
x_181 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3;
x_182 = l_Lean_Option_get___at___Lean_Meta_evalExprCore_spec__2(x_180, x_181);
x_183 = l_Lean_Kernel_isDiagnosticsEnabled(x_170);
lean_dec_ref(x_170);
if (x_183 == 0)
{
if (x_182 == 0)
{
lean_inc_ref(x_169);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc_ref(x_157);
lean_inc_ref(x_156);
lean_dec_ref(x_107);
x_9 = x_106;
x_10 = x_182;
x_11 = x_105;
x_12 = x_176;
x_13 = x_177;
x_14 = x_104;
x_15 = x_180;
x_16 = x_156;
x_17 = x_157;
x_18 = x_159;
x_19 = x_160;
x_20 = x_161;
x_21 = x_162;
x_22 = x_163;
x_23 = x_164;
x_24 = x_165;
x_25 = x_166;
x_26 = x_167;
x_27 = x_168;
x_28 = x_169;
x_29 = x_108;
x_30 = x_155;
goto block_41;
}
else
{
x_66 = x_106;
x_67 = x_182;
x_68 = x_105;
x_69 = x_107;
x_70 = x_176;
x_71 = x_177;
x_72 = x_104;
x_73 = x_180;
x_74 = x_155;
x_75 = x_108;
x_76 = x_183;
goto block_100;
}
}
else
{
x_66 = x_106;
x_67 = x_182;
x_68 = x_105;
x_69 = x_107;
x_70 = x_176;
x_71 = x_177;
x_72 = x_104;
x_73 = x_180;
x_74 = x_155;
x_75 = x_108;
x_76 = x_182;
goto block_100;
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_111);
lean_dec(x_108);
lean_dec_ref(x_107);
lean_dec(x_106);
lean_dec_ref(x_105);
lean_dec(x_104);
lean_dec_ref(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
x_184 = !lean_is_exclusive(x_121);
if (x_184 == 0)
{
return x_121;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_121, 0);
x_186 = lean_ctor_get(x_121, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_121);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_111);
lean_dec(x_108);
lean_dec_ref(x_107);
lean_dec(x_106);
lean_dec_ref(x_105);
lean_dec(x_104);
lean_dec_ref(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
x_188 = !lean_is_exclusive(x_113);
if (x_188 == 0)
{
return x_113;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_113, 0);
x_190 = lean_ctor_get(x_113, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_113);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_108);
lean_dec_ref(x_107);
lean_dec(x_106);
lean_dec_ref(x_105);
lean_dec(x_104);
lean_dec_ref(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec_ref(x_1);
x_192 = !lean_is_exclusive(x_110);
if (x_192 == 0)
{
return x_110;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_110, 0);
x_194 = lean_ctor_get(x_110, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_110);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
block_245:
{
lean_object* x_202; lean_object* x_203; 
x_202 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5;
lean_inc(x_200);
lean_inc_ref(x_199);
x_203 = l_Lean_Core_mkFreshUserName(x_202, x_199, x_200, x_201);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec_ref(x_203);
x_206 = l_Lean_instantiateMVars___at___Lean_Meta_evalExprCore_spec__0___redArg(x_3, x_198, x_205);
x_207 = !lean_is_exclusive(x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_208 = lean_ctor_get(x_206, 0);
x_209 = lean_ctor_get(x_206, 1);
x_210 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12;
lean_inc(x_208);
x_211 = l_Lean_collectLevelParams(x_210, x_208);
x_212 = lean_ctor_get(x_211, 2);
lean_inc_ref(x_212);
lean_dec_ref(x_211);
x_213 = lean_box(0);
x_214 = l_Lean_Expr_hasMVar(x_208);
if (x_214 == 0)
{
lean_free_object(x_206);
x_101 = x_212;
x_102 = x_213;
x_103 = x_208;
x_104 = x_204;
x_105 = x_197;
x_106 = x_198;
x_107 = x_199;
x_108 = x_200;
x_109 = x_209;
goto block_196;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
lean_dec_ref(x_212);
lean_dec(x_204);
lean_dec_ref(x_1);
x_215 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__14;
x_216 = l_Lean_indentExpr(x_208);
lean_ctor_set_tag(x_206, 7);
lean_ctor_set(x_206, 1, x_216);
lean_ctor_set(x_206, 0, x_215);
x_217 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__16;
x_218 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_218, 0, x_206);
lean_ctor_set(x_218, 1, x_217);
x_219 = l_Lean_throwError___at___Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4_spec__4___redArg(x_218, x_197, x_198, x_199, x_200, x_209);
lean_dec(x_200);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
x_220 = !lean_is_exclusive(x_219);
if (x_220 == 0)
{
return x_219;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_219, 0);
x_222 = lean_ctor_get(x_219, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_219);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
return x_223;
}
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_224 = lean_ctor_get(x_206, 0);
x_225 = lean_ctor_get(x_206, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_206);
x_226 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12;
lean_inc(x_224);
x_227 = l_Lean_collectLevelParams(x_226, x_224);
x_228 = lean_ctor_get(x_227, 2);
lean_inc_ref(x_228);
lean_dec_ref(x_227);
x_229 = lean_box(0);
x_230 = l_Lean_Expr_hasMVar(x_224);
if (x_230 == 0)
{
x_101 = x_228;
x_102 = x_229;
x_103 = x_224;
x_104 = x_204;
x_105 = x_197;
x_106 = x_198;
x_107 = x_199;
x_108 = x_200;
x_109 = x_225;
goto block_196;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec_ref(x_228);
lean_dec(x_204);
lean_dec_ref(x_1);
x_231 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__14;
x_232 = l_Lean_indentExpr(x_224);
x_233 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
x_234 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__16;
x_235 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
x_236 = l_Lean_throwError___at___Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4_spec__4___redArg(x_235, x_197, x_198, x_199, x_200, x_225);
lean_dec(x_200);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_239 = x_236;
} else {
 lean_dec_ref(x_236);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
}
}
else
{
uint8_t x_241; 
lean_dec(x_200);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_241 = !lean_is_exclusive(x_203);
if (x_241 == 0)
{
return x_203;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_203, 0);
x_243 = lean_ctor_get(x_203, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_203);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
block_275:
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_255 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__2;
x_256 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_246);
lean_ctor_set(x_256, 2, x_247);
lean_ctor_set(x_256, 3, x_248);
lean_ctor_set(x_256, 4, x_249);
lean_ctor_set(x_256, 5, x_255);
lean_ctor_set(x_256, 6, x_250);
lean_ctor_set(x_256, 7, x_251);
lean_ctor_set(x_256, 8, x_252);
x_257 = lean_st_ref_set(x_7, x_256, x_253);
x_258 = lean_ctor_get(x_257, 1);
lean_inc(x_258);
lean_dec_ref(x_257);
x_259 = lean_st_ref_take(x_5, x_258);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec_ref(x_259);
x_262 = !lean_is_exclusive(x_260);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_263 = lean_ctor_get(x_260, 1);
lean_dec(x_263);
x_264 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__3;
lean_ctor_set(x_260, 1, x_264);
x_265 = lean_st_ref_set(x_5, x_260, x_261);
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
lean_dec_ref(x_265);
x_197 = x_4;
x_198 = x_5;
x_199 = x_6;
x_200 = x_7;
x_201 = x_266;
goto block_245;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_267 = lean_ctor_get(x_260, 0);
x_268 = lean_ctor_get(x_260, 2);
x_269 = lean_ctor_get(x_260, 3);
x_270 = lean_ctor_get(x_260, 4);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_260);
x_271 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__3;
x_272 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_272, 0, x_267);
lean_ctor_set(x_272, 1, x_271);
lean_ctor_set(x_272, 2, x_268);
lean_ctor_set(x_272, 3, x_269);
lean_ctor_set(x_272, 4, x_270);
x_273 = lean_st_ref_set(x_5, x_272, x_261);
x_274 = lean_ctor_get(x_273, 1);
lean_inc(x_274);
lean_dec_ref(x_273);
x_197 = x_4;
x_198 = x_5;
x_199 = x_6;
x_200 = x_7;
x_201 = x_274;
goto block_245;
}
}
block_292:
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_279 = lean_st_ref_take(x_7, x_278);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec_ref(x_279);
x_282 = lean_ctor_get(x_280, 0);
lean_inc_ref(x_282);
x_283 = lean_ctor_get(x_280, 1);
lean_inc(x_283);
x_284 = lean_ctor_get(x_280, 2);
lean_inc_ref(x_284);
x_285 = lean_ctor_get(x_280, 3);
lean_inc_ref(x_285);
x_286 = lean_ctor_get(x_280, 4);
lean_inc_ref(x_286);
x_287 = lean_ctor_get(x_280, 6);
lean_inc_ref(x_287);
x_288 = lean_ctor_get(x_280, 7);
lean_inc_ref(x_288);
x_289 = lean_ctor_get(x_280, 8);
lean_inc_ref(x_289);
lean_dec(x_280);
lean_inc_ref(x_282);
x_290 = l_Lean_Environment_importEnv_x3f(x_282);
if (lean_obj_tag(x_290) == 0)
{
x_246 = x_283;
x_247 = x_284;
x_248 = x_285;
x_249 = x_286;
x_250 = x_287;
x_251 = x_288;
x_252 = x_289;
x_253 = x_281;
x_254 = x_282;
goto block_275;
}
else
{
lean_object* x_291; 
lean_dec_ref(x_282);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
lean_dec_ref(x_290);
x_246 = x_283;
x_247 = x_284;
x_248 = x_285;
x_249 = x_286;
x_250 = x_287;
x_251 = x_288;
x_252 = x_289;
x_253 = x_281;
x_254 = x_291;
goto block_275;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_12);
lean_dec(x_10);
x_13 = lean_box(x_3);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_evalExprCore___redArg___lam__0___boxed), 8, 3);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_1);
x_15 = l_Lean_Environment_unlockAsync(x_12);
x_16 = l_Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9___redArg(x_15, x_14, x_4, x_5, x_6, x_7, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_evalExprCore___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_evalExprCore_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___Lean_Meta_evalExprCore_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_evalExprCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___Lean_Meta_evalExprCore_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___Lean_Meta_evalExprCore_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Option_set___at___Lean_Meta_evalExprCore_spec__1(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_Meta_evalExprCore_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___Lean_Meta_evalExprCore_spec__2(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_Meta_evalExprCore_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at___Lean_Meta_evalExprCore_spec__3(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4_spec__4_spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4___redArg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Meta_evalExprCore_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_Meta_evalExprCore_spec__8(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Meta_evalExprCore___redArg___lam__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_evalExprCore___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Meta_evalExprCore(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected type at evalExpr", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_8 = l_Lean_Meta_whnfD(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lean_Expr_isConstOf(x_10, x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_8);
x_13 = l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1;
x_14 = l_Lean_indentExpr(x_10);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__16;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at___Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4_spec__4___redArg(x_17, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_19 = lean_box(0);
lean_ctor_set(x_8, 0, x_19);
return x_8;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = l_Lean_Expr_isConstOf(x_20, x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1;
x_24 = l_Lean_indentExpr(x_20);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__16;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwError___at___Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4_spec__4___redArg(x_27, x_3, x_4, x_5, x_6, x_21);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_21);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_31 = !lean_is_exclusive(x_8);
if (x_31 == 0)
{
return x_8;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_8, 0);
x_33 = lean_ctor_get(x_8, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_8);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed), 7, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_Meta_evalExprCore___redArg(x_2, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_evalExpr_x27___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_evalExpr_x27___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_evalExpr_x27___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Meta_evalExpr_x27(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected type at `evalExpr` ", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_evalExpr___redArg___lam__0___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
lean_inc_ref(x_2);
x_8 = l_Lean_Meta_isExprDefEq(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = lean_box(0);
x_13 = l_Lean_Meta_evalExpr___redArg___lam__0___closed__0;
x_14 = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(x_2, x_1, x_12, x_13, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = l_Lean_Meta_evalExpr___redArg___lam__0___closed__2;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
x_19 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__16;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at___Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__4_spec__4_spec__4___redArg(x_20, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
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
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_8, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_8, 0, x_28);
return x_8;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_dec(x_8);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_32 = !lean_is_exclusive(x_8);
if (x_32 == 0)
{
return x_8;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_8, 0);
x_34 = lean_ctor_get(x_8, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_8);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr___redArg___lam__0), 7, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_Meta_evalExprCore___redArg(x_2, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_evalExpr___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_evalExpr___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Meta_evalExpr(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* initialize_Lean_AddDecl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_CollectLevelParams(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Eval(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_AddDecl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__0 = _init_l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__0();
lean_mark_persistent(l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__0);
l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__1 = _init_l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__1();
lean_mark_persistent(l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__1);
l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__2 = _init_l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__2();
lean_mark_persistent(l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__2);
l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__3 = _init_l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__3();
lean_mark_persistent(l_Lean_setEnv___at___Lean_withEnv___at___Lean_Meta_evalExprCore_spec__9_spec__9___redArg___closed__3);
l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0 = _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0);
l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1 = _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1);
l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2 = _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2);
l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3 = _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3);
l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4 = _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4();
lean_mark_persistent(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4);
l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5 = _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5();
lean_mark_persistent(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5);
l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6 = _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6();
lean_mark_persistent(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6);
l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7 = _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7();
lean_mark_persistent(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7);
l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8 = _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8();
lean_mark_persistent(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8);
l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9 = _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9();
lean_mark_persistent(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9);
l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10 = _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10();
lean_mark_persistent(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10);
l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11 = _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11();
lean_mark_persistent(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11);
l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12 = _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12();
lean_mark_persistent(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12);
l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13 = _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13();
lean_mark_persistent(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__13);
l_Lean_Meta_evalExprCore___redArg___lam__0___closed__14 = _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__14();
lean_mark_persistent(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__14);
l_Lean_Meta_evalExprCore___redArg___lam__0___closed__15 = _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__15();
lean_mark_persistent(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__15);
l_Lean_Meta_evalExprCore___redArg___lam__0___closed__16 = _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__16();
lean_mark_persistent(l_Lean_Meta_evalExprCore___redArg___lam__0___closed__16);
l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0 = _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0);
l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1 = _init_l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1);
l_Lean_Meta_evalExpr___redArg___lam__0___closed__0 = _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_evalExpr___redArg___lam__0___closed__0);
l_Lean_Meta_evalExpr___redArg___lam__0___closed__1 = _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_evalExpr___redArg___lam__0___closed__1);
l_Lean_Meta_evalExpr___redArg___lam__0___closed__2 = _init_l_Lean_Meta_evalExpr___redArg___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_evalExpr___redArg___lam__0___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
