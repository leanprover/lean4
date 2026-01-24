// Lean compiler output
// Module: Lean.Meta.Eval
// Imports: public import Lean.AddDecl public import Lean.Meta.Check public import Lean.Util.CollectLevelParams
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
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Environment_isImportedConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__0;
uint8_t lean_has_compile_error(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___closed__1;
lean_object* l_Lean_Environment_importEnv_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9;
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8;
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10;
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_async;
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(lean_object*, lean_object*, size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___boxed(lean_object*);
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_diagnostics;
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_traceBlock___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11;
lean_object* l_Lean_collectLevelParams(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12;
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_7) == 3)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
return x_8;
}
else
{
lean_dec(x_7);
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__8(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5_spec__8(x_1, x_2, x_3, x_4, x_5);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = l_Lean_stringToMessageData(x_7);
x_9 = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(x_8, x_2, x_3, x_4, x_5);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_ctor_set_tag(x_1, 0);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_abortCommandExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_st_ref_get(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec(x_8);
lean_inc(x_1);
x_10 = lean_has_compile_error(x_9, x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_st_ref_get(x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_5, 2);
x_14 = l_Lean_Environment_evalConst___redArg(x_12, x_13, x_1, x_2);
x_15 = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(x_14, x_3, x_4, x_5, x_6);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_16);
x_17 = lean_st_ref_get(x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_5, 2);
x_20 = l_Lean_Environment_evalConst___redArg(x_18, x_19, x_1, x_2);
x_21 = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(x_20, x_3, x_4, x_5, x_6);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(x_1, x_8, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_7 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_7, 0, x_3);
lean_inc(x_2);
x_8 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_2, x_7, x_5);
if (x_6 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__1;
x_10 = l_Lean_Name_isPrefixOf(x_9, x_2);
lean_dec(x_2);
lean_ctor_set(x_1, 0, x_8);
lean_ctor_set_uint8(x_1, sizeof(void*)*1, x_10);
return x_1;
}
else
{
lean_dec(x_2);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_inc(x_11);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_13, 0, x_3);
lean_inc(x_2);
x_14 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_2, x_13, x_11);
if (x_12 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__1;
x_16 = l_Lean_Name_isPrefixOf(x_15, x_2);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_12);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(x_1, x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiler env", 12, 12);
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
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__6;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__8;
x_2 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__7;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to evaluate expression, it contains metavariables", 56, 56);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; uint8_t x_75; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_206; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_206 = lean_st_ref_get(x_8);
lean_inc_ref(x_4);
x_219 = l_Lean_Expr_getUsedConstants(x_4);
x_220 = lean_unsigned_to_nat(0u);
x_221 = lean_array_get_size(x_219);
x_222 = lean_nat_dec_lt(x_220, x_221);
if (x_222 == 0)
{
lean_dec_ref(x_219);
lean_dec(x_206);
goto block_218;
}
else
{
if (x_222 == 0)
{
lean_dec_ref(x_219);
lean_dec(x_206);
goto block_218;
}
else
{
lean_object* x_223; size_t x_224; size_t x_225; uint8_t x_226; 
x_223 = lean_ctor_get(x_206, 0);
lean_inc_ref(x_223);
lean_dec(x_206);
x_224 = 0;
x_225 = lean_usize_of_nat(x_221);
x_226 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_evalExprCore_spec__6(x_223, x_219, x_224, x_225);
lean_dec_ref(x_219);
lean_dec_ref(x_223);
if (x_226 == 0)
{
goto block_218;
}
else
{
x_152 = x_5;
x_153 = x_6;
x_154 = x_7;
x_155 = x_8;
x_156 = lean_box(0);
goto block_180;
}
}
}
block_40:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = l_Lean_maxRecDepth;
x_33 = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__3(x_12, x_32);
x_34 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_34, 0, x_17);
lean_ctor_set(x_34, 1, x_18);
lean_ctor_set(x_34, 2, x_12);
lean_ctor_set(x_34, 3, x_19);
lean_ctor_set(x_34, 4, x_33);
lean_ctor_set(x_34, 5, x_20);
lean_ctor_set(x_34, 6, x_21);
lean_ctor_set(x_34, 7, x_22);
lean_ctor_set(x_34, 8, x_23);
lean_ctor_set(x_34, 9, x_24);
lean_ctor_set(x_34, 10, x_25);
lean_ctor_set(x_34, 11, x_26);
lean_ctor_set(x_34, 12, x_27);
lean_ctor_set(x_34, 13, x_29);
lean_ctor_set_uint8(x_34, sizeof(void*)*14, x_16);
lean_ctor_set_uint8(x_34, sizeof(void*)*14 + 1, x_28);
lean_inc(x_30);
lean_inc_ref(x_34);
x_35 = l_Lean_addAndCompile(x_10, x_13, x_34, x_30);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_dec_ref(x_35);
x_36 = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(x_14, x_1, x_15, x_11, x_34, x_30);
lean_dec(x_30);
lean_dec_ref(x_34);
lean_dec(x_11);
lean_dec_ref(x_15);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec_ref(x_34);
lean_dec(x_30);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_11);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
block_64:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_51 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_48, 3);
lean_inc(x_53);
x_54 = lean_ctor_get(x_48, 5);
lean_inc(x_54);
x_55 = lean_ctor_get(x_48, 6);
lean_inc(x_55);
x_56 = lean_ctor_get(x_48, 7);
lean_inc(x_56);
x_57 = lean_ctor_get(x_48, 8);
lean_inc(x_57);
x_58 = lean_ctor_get(x_48, 9);
lean_inc(x_58);
x_59 = lean_ctor_get(x_48, 10);
lean_inc(x_59);
x_60 = lean_ctor_get(x_48, 11);
lean_inc(x_60);
x_61 = lean_ctor_get(x_48, 12);
lean_inc(x_61);
x_62 = lean_ctor_get_uint8(x_48, sizeof(void*)*14 + 1);
x_63 = lean_ctor_get(x_48, 13);
lean_inc_ref(x_63);
lean_dec_ref(x_48);
x_10 = x_41;
x_11 = x_42;
x_12 = x_43;
x_13 = x_44;
x_14 = x_45;
x_15 = x_46;
x_16 = x_47;
x_17 = x_51;
x_18 = x_52;
x_19 = x_53;
x_20 = x_54;
x_21 = x_55;
x_22 = x_56;
x_23 = x_57;
x_24 = x_58;
x_25 = x_59;
x_26 = x_60;
x_27 = x_61;
x_28 = x_62;
x_29 = x_63;
x_30 = x_49;
x_31 = lean_box(0);
goto block_40;
}
block_95:
{
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_st_ref_take(x_74);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = lean_ctor_get(x_76, 5);
lean_dec(x_79);
x_80 = l_Lean_Kernel_enableDiag(x_78, x_73);
x_81 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2;
lean_ctor_set(x_76, 5, x_81);
lean_ctor_set(x_76, 0, x_80);
x_82 = lean_st_ref_set(x_74, x_76);
x_41 = x_65;
x_42 = x_66;
x_43 = x_67;
x_44 = x_70;
x_45 = x_71;
x_46 = x_72;
x_47 = x_73;
x_48 = x_68;
x_49 = x_74;
x_50 = lean_box(0);
goto block_64;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_83 = lean_ctor_get(x_76, 0);
x_84 = lean_ctor_get(x_76, 1);
x_85 = lean_ctor_get(x_76, 2);
x_86 = lean_ctor_get(x_76, 3);
x_87 = lean_ctor_get(x_76, 4);
x_88 = lean_ctor_get(x_76, 6);
x_89 = lean_ctor_get(x_76, 7);
x_90 = lean_ctor_get(x_76, 8);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_76);
x_91 = l_Lean_Kernel_enableDiag(x_83, x_73);
x_92 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2;
x_93 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_84);
lean_ctor_set(x_93, 2, x_85);
lean_ctor_set(x_93, 3, x_86);
lean_ctor_set(x_93, 4, x_87);
lean_ctor_set(x_93, 5, x_92);
lean_ctor_set(x_93, 6, x_88);
lean_ctor_set(x_93, 7, x_89);
lean_ctor_set(x_93, 8, x_90);
x_94 = lean_st_ref_set(x_74, x_93);
x_41 = x_65;
x_42 = x_66;
x_43 = x_67;
x_44 = x_70;
x_45 = x_71;
x_46 = x_72;
x_47 = x_73;
x_48 = x_68;
x_49 = x_74;
x_50 = lean_box(0);
goto block_64;
}
}
else
{
x_41 = x_65;
x_42 = x_66;
x_43 = x_67;
x_44 = x_70;
x_45 = x_71;
x_46 = x_72;
x_47 = x_73;
x_48 = x_68;
x_49 = x_74;
x_50 = lean_box(0);
goto block_64;
}
}
block_151:
{
lean_object* x_105; 
lean_inc(x_103);
lean_inc_ref(x_102);
lean_inc(x_101);
lean_inc_ref(x_100);
lean_inc_ref(x_98);
x_105 = lean_infer_type(x_98, x_100, x_101, x_102, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec_ref(x_105);
lean_inc(x_103);
lean_inc_ref(x_102);
lean_inc(x_101);
lean_inc_ref(x_100);
lean_inc(x_106);
x_107 = lean_apply_6(x_2, x_106, x_100, x_101, x_102, x_103, lean_box(0));
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec_ref(x_107);
x_108 = lean_st_ref_get(x_103);
x_109 = lean_ctor_get(x_108, 0);
lean_inc_ref(x_109);
lean_dec(x_108);
x_110 = lean_ctor_get(x_109, 2);
lean_inc_ref(x_110);
lean_dec_ref(x_109);
x_111 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__3;
lean_inc(x_103);
lean_inc_ref(x_102);
x_112 = l_Lean_traceBlock___redArg(x_111, x_110, x_102, x_103);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_141; 
lean_dec_ref(x_112);
x_113 = lean_st_ref_get(x_103);
x_114 = lean_ctor_get(x_102, 0);
x_115 = lean_ctor_get(x_102, 1);
x_116 = lean_ctor_get(x_102, 2);
x_117 = lean_ctor_get(x_102, 3);
x_118 = lean_ctor_get(x_102, 5);
x_119 = lean_ctor_get(x_102, 6);
x_120 = lean_ctor_get(x_102, 7);
x_121 = lean_ctor_get(x_102, 8);
x_122 = lean_ctor_get(x_102, 9);
x_123 = lean_ctor_get(x_102, 10);
x_124 = lean_ctor_get(x_102, 11);
x_125 = lean_ctor_get(x_102, 12);
x_126 = lean_ctor_get_uint8(x_102, sizeof(void*)*14 + 1);
x_127 = lean_ctor_get(x_102, 13);
x_128 = lean_ctor_get(x_113, 0);
lean_inc_ref(x_128);
lean_dec(x_113);
x_129 = lean_array_to_list(x_99);
lean_inc(x_97);
x_130 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_130, 0, x_97);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set(x_130, 2, x_106);
x_131 = lean_box(0);
lean_inc(x_97);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_97);
lean_ctor_set(x_132, 1, x_96);
x_133 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_98);
lean_ctor_set(x_133, 2, x_131);
lean_ctor_set(x_133, 3, x_132);
lean_ctor_set_uint8(x_133, sizeof(void*)*4, x_3);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
x_135 = 1;
x_136 = l_Lean_Elab_async;
x_137 = 0;
lean_inc_ref(x_116);
x_138 = l_Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1(x_116, x_136, x_137);
x_139 = l_Lean_diagnostics;
x_140 = l_Lean_Option_get___at___00Lean_Meta_evalExprCore_spec__2(x_138, x_139);
x_141 = l_Lean_Kernel_isDiagnosticsEnabled(x_128);
lean_dec_ref(x_128);
if (x_141 == 0)
{
if (x_140 == 0)
{
lean_inc_ref(x_127);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc_ref(x_115);
lean_inc_ref(x_114);
lean_dec_ref(x_102);
x_10 = x_134;
x_11 = x_101;
x_12 = x_138;
x_13 = x_135;
x_14 = x_97;
x_15 = x_100;
x_16 = x_140;
x_17 = x_114;
x_18 = x_115;
x_19 = x_117;
x_20 = x_118;
x_21 = x_119;
x_22 = x_120;
x_23 = x_121;
x_24 = x_122;
x_25 = x_123;
x_26 = x_124;
x_27 = x_125;
x_28 = x_126;
x_29 = x_127;
x_30 = x_103;
x_31 = lean_box(0);
goto block_40;
}
else
{
x_65 = x_134;
x_66 = x_101;
x_67 = x_138;
x_68 = x_102;
x_69 = lean_box(0);
x_70 = x_135;
x_71 = x_97;
x_72 = x_100;
x_73 = x_140;
x_74 = x_103;
x_75 = x_141;
goto block_95;
}
}
else
{
x_65 = x_134;
x_66 = x_101;
x_67 = x_138;
x_68 = x_102;
x_69 = lean_box(0);
x_70 = x_135;
x_71 = x_97;
x_72 = x_100;
x_73 = x_140;
x_74 = x_103;
x_75 = x_140;
goto block_95;
}
}
else
{
uint8_t x_142; 
lean_dec(x_106);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec(x_101);
lean_dec_ref(x_100);
lean_dec_ref(x_99);
lean_dec_ref(x_98);
lean_dec(x_97);
lean_dec(x_96);
x_142 = !lean_is_exclusive(x_112);
if (x_142 == 0)
{
return x_112;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_112, 0);
lean_inc(x_143);
lean_dec(x_112);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
return x_144;
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_106);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec(x_101);
lean_dec_ref(x_100);
lean_dec_ref(x_99);
lean_dec_ref(x_98);
lean_dec(x_97);
lean_dec(x_96);
x_145 = !lean_is_exclusive(x_107);
if (x_145 == 0)
{
return x_107;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_107, 0);
lean_inc(x_146);
lean_dec(x_107);
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec(x_101);
lean_dec_ref(x_100);
lean_dec_ref(x_99);
lean_dec_ref(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec_ref(x_2);
x_148 = !lean_is_exclusive(x_105);
if (x_148 == 0)
{
return x_105;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_105, 0);
lean_inc(x_149);
lean_dec(x_105);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
return x_150;
}
}
}
block_180:
{
lean_object* x_157; lean_object* x_158; 
x_157 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__5;
lean_inc(x_155);
lean_inc_ref(x_154);
x_158 = l_Lean_Core_mkFreshUserName(x_157, x_154, x_155);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
lean_dec_ref(x_158);
x_160 = l_Lean_instantiateMVars___at___00Lean_Meta_evalExprCore_spec__0___redArg(x_4, x_153);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
lean_dec_ref(x_160);
x_162 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__9;
lean_inc(x_161);
x_163 = l_Lean_collectLevelParams(x_162, x_161);
x_164 = lean_ctor_get(x_163, 2);
lean_inc_ref(x_164);
lean_dec_ref(x_163);
x_165 = lean_box(0);
x_166 = l_Lean_Expr_hasMVar(x_161);
if (x_166 == 0)
{
x_96 = x_165;
x_97 = x_159;
x_98 = x_161;
x_99 = x_164;
x_100 = x_152;
x_101 = x_153;
x_102 = x_154;
x_103 = x_155;
x_104 = lean_box(0);
goto block_151;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__11;
lean_inc(x_161);
x_168 = l_Lean_indentExpr(x_161);
x_169 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(x_169, x_152, x_153, x_154, x_155);
if (lean_obj_tag(x_170) == 0)
{
lean_dec_ref(x_170);
x_96 = x_165;
x_97 = x_159;
x_98 = x_161;
x_99 = x_164;
x_100 = x_152;
x_101 = x_153;
x_102 = x_154;
x_103 = x_155;
x_104 = lean_box(0);
goto block_151;
}
else
{
uint8_t x_171; 
lean_dec_ref(x_164);
lean_dec(x_161);
lean_dec(x_159);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec_ref(x_2);
x_171 = !lean_is_exclusive(x_170);
if (x_171 == 0)
{
return x_170;
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_172);
return x_173;
}
}
}
}
else
{
uint8_t x_174; 
lean_dec(x_159);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec_ref(x_2);
x_174 = !lean_is_exclusive(x_160);
if (x_174 == 0)
{
return x_160;
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_160, 0);
lean_inc(x_175);
lean_dec(x_160);
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_175);
return x_176;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_177 = !lean_is_exclusive(x_158);
if (x_177 == 0)
{
return x_158;
}
else
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_158, 0);
lean_inc(x_178);
lean_dec(x_158);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_178);
return x_179;
}
}
}
block_205:
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_190 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2;
x_191 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_181);
lean_ctor_set(x_191, 2, x_182);
lean_ctor_set(x_191, 3, x_183);
lean_ctor_set(x_191, 4, x_184);
lean_ctor_set(x_191, 5, x_190);
lean_ctor_set(x_191, 6, x_185);
lean_ctor_set(x_191, 7, x_186);
lean_ctor_set(x_191, 8, x_187);
x_192 = lean_st_ref_set(x_8, x_191);
x_193 = lean_st_ref_take(x_6);
x_194 = !lean_is_exclusive(x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_193, 1);
lean_dec(x_195);
x_196 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12;
lean_ctor_set(x_193, 1, x_196);
x_197 = lean_st_ref_set(x_6, x_193);
x_152 = x_5;
x_153 = x_6;
x_154 = x_7;
x_155 = x_8;
x_156 = lean_box(0);
goto block_180;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_198 = lean_ctor_get(x_193, 0);
x_199 = lean_ctor_get(x_193, 2);
x_200 = lean_ctor_get(x_193, 3);
x_201 = lean_ctor_get(x_193, 4);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_193);
x_202 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12;
x_203 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_203, 0, x_198);
lean_ctor_set(x_203, 1, x_202);
lean_ctor_set(x_203, 2, x_199);
lean_ctor_set(x_203, 3, x_200);
lean_ctor_set(x_203, 4, x_201);
x_204 = lean_st_ref_set(x_6, x_203);
x_152 = x_5;
x_153 = x_6;
x_154 = x_7;
x_155 = x_8;
x_156 = lean_box(0);
goto block_180;
}
}
block_218:
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_207 = lean_st_ref_take(x_8);
x_208 = lean_ctor_get(x_207, 0);
lean_inc_ref(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
x_210 = lean_ctor_get(x_207, 2);
lean_inc_ref(x_210);
x_211 = lean_ctor_get(x_207, 3);
lean_inc_ref(x_211);
x_212 = lean_ctor_get(x_207, 4);
lean_inc_ref(x_212);
x_213 = lean_ctor_get(x_207, 6);
lean_inc_ref(x_213);
x_214 = lean_ctor_get(x_207, 7);
lean_inc_ref(x_214);
x_215 = lean_ctor_get(x_207, 8);
lean_inc_ref(x_215);
lean_dec(x_207);
lean_inc_ref(x_208);
x_216 = l_Lean_Environment_importEnv_x3f(x_208);
if (lean_obj_tag(x_216) == 0)
{
x_181 = x_209;
x_182 = x_210;
x_183 = x_211;
x_184 = x_212;
x_185 = x_213;
x_186 = x_214;
x_187 = x_215;
x_188 = lean_box(0);
x_189 = x_208;
goto block_205;
}
else
{
lean_object* x_217; 
lean_dec_ref(x_208);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
lean_dec_ref(x_216);
x_181 = x_209;
x_182 = x_210;
x_183 = x_211;
x_184 = x_212;
x_185 = x_213;
x_186 = x_214;
x_187 = x_215;
x_188 = lean_box(0);
x_189 = x_217;
goto block_205;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_3);
x_12 = l_Lean_Meta_evalExprCore___redArg___lam__0(x_10, x_2, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_5, 5);
lean_dec(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2;
lean_ctor_set(x_5, 5, x_9);
lean_ctor_set(x_5, 0, x_1);
x_10 = lean_st_ref_set(x_3, x_5);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_11, 1);
lean_dec(x_13);
x_14 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12;
lean_ctor_set(x_11, 1, x_14);
x_15 = lean_st_ref_set(x_2, x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 2);
x_20 = lean_ctor_get(x_11, 3);
x_21 = lean_ctor_get(x_11, 4);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_22 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12;
x_23 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_21);
x_24 = lean_st_ref_set(x_2, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_27 = lean_ctor_get(x_5, 1);
x_28 = lean_ctor_get(x_5, 2);
x_29 = lean_ctor_get(x_5, 3);
x_30 = lean_ctor_get(x_5, 4);
x_31 = lean_ctor_get(x_5, 6);
x_32 = lean_ctor_get(x_5, 7);
x_33 = lean_ctor_get(x_5, 8);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_5);
x_34 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__2;
x_35 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_27);
lean_ctor_set(x_35, 2, x_28);
lean_ctor_set(x_35, 3, x_29);
lean_ctor_set(x_35, 4, x_30);
lean_ctor_set(x_35, 5, x_34);
lean_ctor_set(x_35, 6, x_31);
lean_ctor_set(x_35, 7, x_32);
lean_ctor_set(x_35, 8, x_33);
x_36 = lean_st_ref_set(x_3, x_35);
x_37 = lean_st_ref_take(x_2);
x_38 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_37, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 3);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_37, 4);
lean_inc_ref(x_41);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 x_42 = x_37;
} else {
 lean_dec_ref(x_37);
 x_42 = lean_box(0);
}
x_43 = l_Lean_Meta_evalExprCore___redArg___lam__0___closed__12;
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 5, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_39);
lean_ctor_set(x_44, 3, x_40);
lean_ctor_set(x_44, 4, x_41);
x_45 = lean_st_ref_set(x_2, x_44);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_17; lean_object* x_18; 
x_8 = lean_st_ref_get(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec(x_8);
x_17 = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(x_1, x_4, x_6);
lean_dec_ref(x_17);
lean_inc(x_6);
lean_inc(x_4);
x_18 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(x_9, x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_23; 
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_19);
return x_23;
}
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec_ref(x_18);
x_10 = x_24;
x_11 = lean_box(0);
goto block_16;
}
block_16:
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(x_9, x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_15; 
lean_dec(x_12);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_10);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_st_ref_get(x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = lean_box(x_4);
x_13 = lean_box(x_3);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_evalExprCore___redArg___lam__0___boxed), 9, 4);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_13);
lean_closure_set(x_14, 3, x_1);
x_15 = l_Lean_Environment_unlockAsync(x_11);
x_16 = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(x_15, x_14, x_5, x_6, x_7, x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_Meta_evalExprCore___redArg(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_evalExprCore___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_evalExprCore(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg();
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___redArg(x_1, x_3, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7_spec__11(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_withEnv___at___00Lean_Meta_evalExprCore_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
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
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_8 = l_Lean_Meta_whnfD(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Expr_isConstOf(x_10, x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_free_object(x_8);
x_12 = l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1;
x_13 = l_Lean_indentExpr(x_10);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(x_14, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_16 = lean_box(0);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
lean_dec(x_8);
x_18 = l_Lean_Expr_isConstOf(x_17, x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_Lean_Meta_evalExpr_x27___redArg___lam__0___closed__1;
x_20 = l_Lean_indentExpr(x_17);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(x_21, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
return x_8;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_8, 0);
lean_inc(x_26);
lean_dec(x_8);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_evalExpr_x27___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed), 7, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = l_Lean_Meta_evalExprCore___redArg(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_Meta_evalExpr_x27___redArg(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_evalExpr_x27___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_evalExpr_x27(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9);
return x_13;
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
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
lean_inc_ref(x_2);
x_8 = l_Lean_Meta_isExprDefEq(x_2, x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_free_object(x_8);
x_12 = lean_box(0);
x_13 = l_Lean_Meta_evalExpr___redArg___lam__0___closed__0;
x_14 = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(x_2, x_1, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Meta_evalExpr___redArg___lam__0___closed__2;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(x_17, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_22 = lean_box(0);
lean_ctor_set(x_8, 0, x_22);
return x_8;
}
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_8, 0);
lean_inc(x_23);
lean_dec(x_8);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_box(0);
x_26 = l_Lean_Meta_evalExpr___redArg___lam__0___closed__0;
x_27 = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(x_2, x_1, x_25, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = l_Lean_Meta_evalExpr___redArg___lam__0___closed__2;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_throwError___at___00Lean_Meta_evalExprCore_spec__5___redArg(x_30, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_33 = x_27;
} else {
 lean_dec_ref(x_27);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_37 = !lean_is_exclusive(x_8);
if (x_37 == 0)
{
return x_8;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_8, 0);
lean_inc(x_38);
lean_dec(x_8);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_evalExpr___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr___redArg___lam__0___boxed), 7, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = l_Lean_Meta_evalExprCore___redArg(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_Meta_evalExpr___redArg(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_evalExpr___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_evalExpr(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9);
return x_13;
}
}
lean_object* initialize_Lean_AddDecl(uint8_t builtin);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin);
lean_object* initialize_Lean_Util_CollectLevelParams(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Eval(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0 = _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_Meta_evalExprCore_spec__4_spec__6___redArg___closed__0);
l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__0 = _init_l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__0();
lean_mark_persistent(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__0);
l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__1 = _init_l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__1();
lean_mark_persistent(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_evalExprCore_spec__1_spec__1___closed__1);
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
