// Lean compiler output
// Module: Lean.Meta.Tactic.Rewrite
// Imports: Lean.Meta.AppBuilder Lean.Meta.MatchUtil Lean.Meta.KAbstract Lean.Meta.Check Lean.Meta.Tactic.Util Lean.Meta.Tactic.Apply Lean.Meta.BinderNameHint
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__11;
static lean_object* l_Lean_MVarId_rewrite___lambda__5___closed__1;
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at_Lean_MVarId_rewrite___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__2___closed__2;
static lean_object* l_Lean_MVarId_rewrite___lambda__18___closed__7;
static lean_object* l_Lean_MVarId_rewrite___lambda__18___closed__4;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__9___boxed(lean_object**);
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__24;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__5___boxed(lean_object**);
static lean_object* l_Lean_MVarId_rewrite___closed__2;
static lean_object* l_Lean_MVarId_rewrite___lambda__18___closed__10;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at_Lean_MVarId_rewrite___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__12___boxed(lean_object**);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__25;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__13___boxed(lean_object**);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__20;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__11___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__8___boxed(lean_object**);
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__10;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__6___boxed(lean_object**);
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__26;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__18___closed__2;
lean_object* l_Lean_Expr_resolveBinderNameHint(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Meta_postprocessAppMVars(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__17___boxed(lean_object**);
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__21;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__18___closed__3;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__15;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasBinderNameHint(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__3___boxed(lean_object**);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__23;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__8;
static lean_object* l_Lean_MVarId_rewrite___lambda__18___closed__1;
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__19;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__9;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__18(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_tactic_skipAssignedInstances;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__10___boxed(lean_object**);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__2___boxed(lean_object**);
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__16___boxed(lean_object**);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__18___closed__5;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_rewrite___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__18___closed__6;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__12;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__7___boxed(lean_object**);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__2___closed__3;
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__16;
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__18;
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__7;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_MVarId_rewrite___spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__18___closed__11;
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__14;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__4___boxed(lean_object**);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__4;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__15___boxed(lean_object**);
static lean_object* l_Lean_MVarId_rewrite___lambda__5___closed__2;
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__17;
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__4___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_MVarId_rewrite___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__18___closed__9;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__14___boxed(lean_object**);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_rewrite___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__18___closed__8;
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__22;
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__13;
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_rewrite___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Expr_mvarId_x21(x_5);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_MVarId_rewrite___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_name_eq(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
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
LEAN_EXPORT uint8_t l_Array_contains___at_Lean_MVarId_rewrite___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_anyMUnsafe_any___at_Lean_MVarId_rewrite___spec__3(x_2, x_1, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_Array_contains___at_Lean_MVarId_rewrite___spec__2(x_1, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
if (x_8 == 0)
{
lean_object* x_11; 
x_11 = lean_array_push(x_5, x_7);
x_3 = x_10;
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_10;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(x_11, x_5, x_6, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_array_push(x_4, x_11);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_2 = x_18;
x_4 = x_16;
x_9 = x_15;
goto _start;
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; 
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_2 = x_22;
x_9 = x_20;
goto _start;
}
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_9);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_Array_contains___at_Lean_MVarId_rewrite___spec__2(x_1, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
if (x_8 == 0)
{
lean_object* x_11; 
x_11 = lean_array_push(x_5, x_7);
x_3 = x_10;
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_10;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_Array_contains___at_Lean_MVarId_rewrite___spec__2(x_1, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
if (x_8 == 0)
{
lean_object* x_11; 
x_11 = lean_array_push(x_5, x_7);
x_3 = x_10;
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_10;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_Array_contains___at_Lean_MVarId_rewrite___spec__2(x_1, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
if (x_8 == 0)
{
lean_object* x_11; 
x_11 = lean_array_push(x_5, x_7);
x_3 = x_10;
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_10;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_expr_instantiate1(x_1, x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = lean_infer_type(x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_isExprDefEq(x_11, x_2, x_4, x_5, x_6, x_7, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congrArg", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_rewrite___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_tactic_skipAssignedInstances;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_1);
x_19 = l_Lean_Meta_getLevel(x_1, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_2);
x_22 = l_Lean_Meta_getLevel(x_2, x_14, x_15, x_16, x_17, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_MVarId_rewrite___lambda__2___closed__2;
x_29 = l_Lean_Expr_const___override(x_28, x_27);
x_30 = l_Lean_mkApp6(x_29, x_1, x_2, x_3, x_4, x_5, x_6);
x_99 = lean_ctor_get(x_16, 2);
lean_inc(x_99);
x_100 = l_Lean_MVarId_rewrite___lambda__2___closed__4;
x_101 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_99, x_100);
lean_dec(x_99);
if (x_101 == 0)
{
uint8_t x_102; 
x_102 = 1;
x_31 = x_102;
goto block_98;
}
else
{
uint8_t x_103; 
x_103 = 0;
x_31 = x_103;
goto block_98;
}
block_98:
{
uint8_t x_32; lean_object* x_33; 
x_32 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_33 = l_Lean_Meta_postprocessAppMVars(x_7, x_8, x_9, x_10, x_31, x_32, x_14, x_15, x_16, x_17, x_24);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_array_size(x_9);
x_36 = 0;
x_37 = l_Array_mapMUnsafe_map___at_Lean_MVarId_rewrite___spec__1(x_35, x_36, x_9);
x_38 = lean_array_get_size(x_37);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_nat_dec_lt(x_39, x_38);
if (x_40 == 0)
{
lean_object* x_86; 
lean_dec(x_38);
lean_dec(x_37);
x_86 = l_Lean_MVarId_rewrite___lambda__2___closed__3;
x_41 = x_86;
x_42 = x_34;
goto block_85;
}
else
{
uint8_t x_87; 
x_87 = lean_nat_dec_le(x_38, x_38);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_38);
lean_dec(x_37);
x_88 = l_Lean_MVarId_rewrite___lambda__2___closed__3;
x_41 = x_88;
x_42 = x_34;
goto block_85;
}
else
{
size_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_90 = l_Lean_MVarId_rewrite___lambda__2___closed__3;
x_91 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__5(x_37, x_36, x_89, x_90, x_14, x_15, x_16, x_17, x_34);
lean_dec(x_37);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_41 = x_92;
x_42 = x_93;
goto block_85;
}
}
block_85:
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_Meta_getMVarsNoDelayed(x_11, x_14, x_15, x_16, x_17, x_42);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_array_get_size(x_45);
x_47 = lean_nat_dec_lt(x_39, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_46);
lean_dec(x_45);
x_48 = l_Lean_MVarId_rewrite___lambda__2___closed__3;
x_49 = l_Array_append___rarg(x_41, x_48);
x_50 = lean_array_to_list(x_49);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_12);
lean_ctor_set(x_51, 1, x_30);
lean_ctor_set(x_51, 2, x_50);
lean_ctor_set(x_43, 0, x_51);
return x_43;
}
else
{
uint8_t x_52; 
x_52 = lean_nat_dec_le(x_46, x_46);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_46);
lean_dec(x_45);
x_53 = l_Lean_MVarId_rewrite___lambda__2___closed__3;
x_54 = l_Array_append___rarg(x_41, x_53);
x_55 = lean_array_to_list(x_54);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_12);
lean_ctor_set(x_56, 1, x_30);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set(x_43, 0, x_56);
return x_43;
}
else
{
size_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_58 = l_Lean_MVarId_rewrite___lambda__2___closed__3;
x_59 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__4(x_41, x_45, x_36, x_57, x_58);
lean_dec(x_45);
x_60 = l_Array_append___rarg(x_41, x_59);
lean_dec(x_59);
x_61 = lean_array_to_list(x_60);
x_62 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_62, 0, x_12);
lean_ctor_set(x_62, 1, x_30);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_43, 0, x_62);
return x_43;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_43, 0);
x_64 = lean_ctor_get(x_43, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_43);
x_65 = lean_array_get_size(x_63);
x_66 = lean_nat_dec_lt(x_39, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_65);
lean_dec(x_63);
x_67 = l_Lean_MVarId_rewrite___lambda__2___closed__3;
x_68 = l_Array_append___rarg(x_41, x_67);
x_69 = lean_array_to_list(x_68);
x_70 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_70, 0, x_12);
lean_ctor_set(x_70, 1, x_30);
lean_ctor_set(x_70, 2, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_64);
return x_71;
}
else
{
uint8_t x_72; 
x_72 = lean_nat_dec_le(x_65, x_65);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_65);
lean_dec(x_63);
x_73 = l_Lean_MVarId_rewrite___lambda__2___closed__3;
x_74 = l_Array_append___rarg(x_41, x_73);
x_75 = lean_array_to_list(x_74);
x_76 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_76, 0, x_12);
lean_ctor_set(x_76, 1, x_30);
lean_ctor_set(x_76, 2, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_64);
return x_77;
}
else
{
size_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_78 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_79 = l_Lean_MVarId_rewrite___lambda__2___closed__3;
x_80 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__4(x_41, x_63, x_36, x_78, x_79);
lean_dec(x_63);
x_81 = l_Array_append___rarg(x_41, x_80);
lean_dec(x_80);
x_82 = lean_array_to_list(x_81);
x_83 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_83, 0, x_12);
lean_ctor_set(x_83, 1, x_30);
lean_ctor_set(x_83, 2, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_64);
return x_84;
}
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_30);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
x_94 = !lean_is_exclusive(x_33);
if (x_94 == 0)
{
return x_33;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_33, 0);
x_96 = lean_ctor_get(x_33, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_33);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
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
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_22);
if (x_104 == 0)
{
return x_22;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_22, 0);
x_106 = lean_ctor_get(x_22, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_22);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
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
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_19);
if (x_108 == 0)
{
return x_19;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_19, 0);
x_110 = lean_ctor_get(x_19, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_19);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_a", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_rewrite___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("motive is dependent", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lambda__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("motive is not type correct:", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lambda__3___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nError: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lambda__3___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\nExplanation: The rewrite tactic rewrites an expression 'e' using an equality 'a = b' by the following process. First, it looks for all 'a' in 'e'. Second, it tries to abstract these occurrences of 'a' to create a function 'm := fun _a => ...', called the *motive*, with the property that 'm a' is definitionally equal to 'e'. Third, we observe that '", 352, 352);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lambda__3___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__13() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_rewrite___lambda__2___closed__2;
x_2 = 0;
x_3 = l_Lean_MessageData_ofConstName(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' implies that 'm a = m b', which can be used with lemmas such as '", 67, 67);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lambda__3___closed__14;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mpr", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_rewrite___lambda__3___closed__16;
x_2 = l_Lean_MVarId_rewrite___lambda__3___closed__17;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__19() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_rewrite___lambda__3___closed__18;
x_2 = 0;
x_3 = l_Lean_MessageData_ofConstName(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' to change the goal. However, if 'e' depends on specific properties of 'a', then the motive 'm' might not typecheck.\n\nPossible solutions: use rewrite's 'occs' configuration option to limit which occurrences are rewritten, or use 'simp' or 'conv' mode, which have strategies for certain kinds of dependencies (these tactics can handle proofs and '", 347, 347);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lambda__3___closed__20;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Decidable", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_rewrite___lambda__3___closed__22;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__24() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_rewrite___lambda__3___closed__23;
x_2 = 0;
x_3 = l_Lean_MessageData_ofConstName(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' instances whose types depend on the rewritten term, and 'simp' can apply user-defined '@[congr]' theorems as well).", 117, 117);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lambda__3___closed__25;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_18 = lean_infer_type(x_1, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_51; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_MVarId_rewrite___lambda__3___closed__2;
x_22 = 0;
lean_inc(x_3);
lean_inc(x_2);
x_23 = l_Lean_Expr_lam___override(x_21, x_2, x_3, x_22);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_23);
x_51 = l_Lean_Meta_check(x_23, x_13, x_14, x_15, x_16, x_20);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_24 = x_52;
goto block_50;
}
else
{
uint8_t x_53; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_51, 0);
x_55 = lean_ctor_get(x_51, 1);
x_56 = l_Lean_Exception_isInterrupt(x_54);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = l_Lean_Exception_isRuntime(x_54);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_free_object(x_51);
x_58 = l_Lean_MessageData_ofExpr(x_23);
x_59 = l_Lean_indentD(x_58);
x_60 = l_Lean_MVarId_rewrite___lambda__3___closed__8;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l_Lean_MVarId_rewrite___lambda__3___closed__10;
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_Exception_toMessageData(x_54);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_MVarId_rewrite___lambda__3___closed__12;
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_MVarId_rewrite___lambda__3___closed__13;
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_MVarId_rewrite___lambda__3___closed__15;
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_MVarId_rewrite___lambda__3___closed__19;
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_MVarId_rewrite___lambda__3___closed__21;
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_MVarId_rewrite___lambda__3___closed__24;
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_MVarId_rewrite___lambda__3___closed__26;
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_8, x_80, x_13, x_14, x_15, x_16, x_55);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
return x_81;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_81);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
else
{
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
return x_51;
}
}
else
{
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
return x_51;
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_ctor_get(x_51, 0);
x_87 = lean_ctor_get(x_51, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_51);
x_88 = l_Lean_Exception_isInterrupt(x_86);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = l_Lean_Exception_isRuntime(x_86);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_90 = l_Lean_MessageData_ofExpr(x_23);
x_91 = l_Lean_indentD(x_90);
x_92 = l_Lean_MVarId_rewrite___lambda__3___closed__8;
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = l_Lean_MVarId_rewrite___lambda__3___closed__10;
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_Exception_toMessageData(x_86);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_MVarId_rewrite___lambda__3___closed__12;
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_MVarId_rewrite___lambda__3___closed__13;
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_MVarId_rewrite___lambda__3___closed__15;
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_MVarId_rewrite___lambda__3___closed__19;
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_MVarId_rewrite___lambda__3___closed__21;
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Lean_MVarId_rewrite___lambda__3___closed__24;
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Lean_MVarId_rewrite___lambda__3___closed__26;
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_8, x_112, x_13, x_14, x_15, x_16, x_87);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
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
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
else
{
lean_object* x_118; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_86);
lean_ctor_set(x_118, 1, x_87);
return x_118;
}
}
else
{
lean_object* x_119; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_86);
lean_ctor_set(x_119, 1, x_87);
return x_119;
}
}
}
block_50:
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
lean_inc(x_19);
x_25 = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lambda__1___boxed), 8, 2);
lean_closure_set(x_25, 0, x_3);
lean_closure_set(x_25, 1, x_19);
x_26 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_2);
x_27 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__4___rarg(x_21, x_22, x_2, x_25, x_26, x_13, x_14, x_15, x_16, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l_Lean_MessageData_ofExpr(x_23);
x_32 = l_Lean_indentD(x_31);
x_33 = l_Lean_MVarId_rewrite___lambda__3___closed__4;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_8, x_37, x_13, x_14, x_15, x_16, x_30);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_27, 1);
lean_inc(x_43);
lean_dec(x_27);
x_44 = lean_box(0);
x_45 = l_Lean_MVarId_rewrite___lambda__2(x_2, x_19, x_4, x_5, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_44, x_13, x_14, x_15, x_16, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_27);
if (x_46 == 0)
{
return x_27;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_27, 0);
x_48 = lean_ctor_get(x_27, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_27);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
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
x_120 = !lean_is_exclusive(x_18);
if (x_120 == 0)
{
return x_18;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_18, 0);
x_122 = lean_ctor_get(x_18, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_18);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_expr_instantiate1(x_1, x_2);
x_19 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_18, x_13, x_14, x_15, x_16, x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Expr_hasBinderNameHint(x_2);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_Lean_MVarId_rewrite___lambda__3(x_3, x_4, x_1, x_5, x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_20, x_13, x_14, x_15, x_16, x_21);
return x_23;
}
else
{
lean_object* x_24; 
lean_inc(x_16);
lean_inc(x_15);
x_24 = l_Lean_Expr_resolveBinderNameHint(x_20, x_15, x_16, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_MVarId_rewrite___lambda__3(x_3, x_4, x_1, x_5, x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_25, x_13, x_14, x_15, x_16, x_26);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
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
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("did not find instance of the pattern in the target expression", 61, 61);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lambda__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_1, x_13, x_14, x_15, x_16, x_17);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 8);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_13, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_13, 3);
lean_inc(x_27);
x_28 = lean_ctor_get(x_13, 4);
lean_inc(x_28);
x_29 = lean_ctor_get(x_13, 5);
lean_inc(x_29);
x_30 = lean_ctor_get(x_13, 6);
lean_inc(x_30);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint64_t x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 9);
x_33 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 10);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_ctor_set_uint8(x_19, 8, x_34);
lean_ctor_set_uint8(x_19, 9, x_35);
x_36 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_19);
x_37 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_37, 0, x_19);
lean_ctor_set(x_37, 1, x_25);
lean_ctor_set(x_37, 2, x_26);
lean_ctor_set(x_37, 3, x_27);
lean_ctor_set(x_37, 4, x_28);
lean_ctor_set(x_37, 5, x_29);
lean_ctor_set(x_37, 6, x_30);
lean_ctor_set_uint64(x_37, sizeof(void*)*7, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*7 + 8, x_24);
lean_ctor_set_uint8(x_37, sizeof(void*)*7 + 9, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*7 + 10, x_33);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_3);
lean_inc(x_21);
x_38 = l_Lean_Meta_kabstract(x_21, x_3, x_23, x_37, x_14, x_15, x_16, x_22);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Expr_hasLooseBVars(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_39);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_42 = l_Lean_indentExpr(x_3);
x_43 = l_Lean_MVarId_rewrite___lambda__5___closed__2;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_42);
lean_ctor_set(x_18, 0, x_43);
x_44 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_18);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_8, x_46, x_13, x_14, x_15, x_16, x_40);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_free_object(x_18);
x_52 = lean_box(0);
x_53 = l_Lean_MVarId_rewrite___lambda__4(x_39, x_4, x_21, x_5, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_52, x_13, x_14, x_15, x_16, x_40);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_free_object(x_18);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_38);
if (x_54 == 0)
{
return x_38;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_38, 0);
x_56 = lean_ctor_get(x_38, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_38);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; lean_object* x_78; uint64_t x_79; lean_object* x_80; lean_object* x_81; 
x_58 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 9);
x_59 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 10);
x_60 = lean_ctor_get_uint8(x_19, 0);
x_61 = lean_ctor_get_uint8(x_19, 1);
x_62 = lean_ctor_get_uint8(x_19, 2);
x_63 = lean_ctor_get_uint8(x_19, 3);
x_64 = lean_ctor_get_uint8(x_19, 4);
x_65 = lean_ctor_get_uint8(x_19, 5);
x_66 = lean_ctor_get_uint8(x_19, 6);
x_67 = lean_ctor_get_uint8(x_19, 7);
x_68 = lean_ctor_get_uint8(x_19, 10);
x_69 = lean_ctor_get_uint8(x_19, 11);
x_70 = lean_ctor_get_uint8(x_19, 12);
x_71 = lean_ctor_get_uint8(x_19, 13);
x_72 = lean_ctor_get_uint8(x_19, 14);
x_73 = lean_ctor_get_uint8(x_19, 15);
x_74 = lean_ctor_get_uint8(x_19, 16);
x_75 = lean_ctor_get_uint8(x_19, 17);
lean_dec(x_19);
x_76 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_77 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_78 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_78, 0, x_60);
lean_ctor_set_uint8(x_78, 1, x_61);
lean_ctor_set_uint8(x_78, 2, x_62);
lean_ctor_set_uint8(x_78, 3, x_63);
lean_ctor_set_uint8(x_78, 4, x_64);
lean_ctor_set_uint8(x_78, 5, x_65);
lean_ctor_set_uint8(x_78, 6, x_66);
lean_ctor_set_uint8(x_78, 7, x_67);
lean_ctor_set_uint8(x_78, 8, x_76);
lean_ctor_set_uint8(x_78, 9, x_77);
lean_ctor_set_uint8(x_78, 10, x_68);
lean_ctor_set_uint8(x_78, 11, x_69);
lean_ctor_set_uint8(x_78, 12, x_70);
lean_ctor_set_uint8(x_78, 13, x_71);
lean_ctor_set_uint8(x_78, 14, x_72);
lean_ctor_set_uint8(x_78, 15, x_73);
lean_ctor_set_uint8(x_78, 16, x_74);
lean_ctor_set_uint8(x_78, 17, x_75);
x_79 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_78);
x_80 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_25);
lean_ctor_set(x_80, 2, x_26);
lean_ctor_set(x_80, 3, x_27);
lean_ctor_set(x_80, 4, x_28);
lean_ctor_set(x_80, 5, x_29);
lean_ctor_set(x_80, 6, x_30);
lean_ctor_set_uint64(x_80, sizeof(void*)*7, x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 8, x_24);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 9, x_58);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 10, x_59);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_3);
lean_inc(x_21);
x_81 = l_Lean_Meta_kabstract(x_21, x_3, x_23, x_80, x_14, x_15, x_16, x_22);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_Expr_hasLooseBVars(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_82);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_85 = l_Lean_indentExpr(x_3);
x_86 = l_Lean_MVarId_rewrite___lambda__5___closed__2;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_85);
lean_ctor_set(x_18, 0, x_86);
x_87 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_18);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_8, x_89, x_13, x_14, x_15, x_16, x_83);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_93 = x_90;
} else {
 lean_dec_ref(x_90);
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
else
{
lean_object* x_95; lean_object* x_96; 
lean_free_object(x_18);
x_95 = lean_box(0);
x_96 = l_Lean_MVarId_rewrite___lambda__4(x_82, x_4, x_21, x_5, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_95, x_13, x_14, x_15, x_16, x_83);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_free_object(x_18);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_97 = lean_ctor_get(x_81, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_81, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_99 = x_81;
} else {
 lean_dec_ref(x_81);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; lean_object* x_129; uint8_t x_130; uint8_t x_131; lean_object* x_132; uint64_t x_133; lean_object* x_134; lean_object* x_135; 
x_101 = lean_ctor_get(x_18, 0);
x_102 = lean_ctor_get(x_18, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_18);
x_103 = lean_ctor_get(x_2, 0);
x_104 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 8);
x_105 = lean_ctor_get(x_13, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_13, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_13, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_13, 4);
lean_inc(x_108);
x_109 = lean_ctor_get(x_13, 5);
lean_inc(x_109);
x_110 = lean_ctor_get(x_13, 6);
lean_inc(x_110);
x_111 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 9);
x_112 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 10);
x_113 = lean_ctor_get_uint8(x_19, 0);
x_114 = lean_ctor_get_uint8(x_19, 1);
x_115 = lean_ctor_get_uint8(x_19, 2);
x_116 = lean_ctor_get_uint8(x_19, 3);
x_117 = lean_ctor_get_uint8(x_19, 4);
x_118 = lean_ctor_get_uint8(x_19, 5);
x_119 = lean_ctor_get_uint8(x_19, 6);
x_120 = lean_ctor_get_uint8(x_19, 7);
x_121 = lean_ctor_get_uint8(x_19, 10);
x_122 = lean_ctor_get_uint8(x_19, 11);
x_123 = lean_ctor_get_uint8(x_19, 12);
x_124 = lean_ctor_get_uint8(x_19, 13);
x_125 = lean_ctor_get_uint8(x_19, 14);
x_126 = lean_ctor_get_uint8(x_19, 15);
x_127 = lean_ctor_get_uint8(x_19, 16);
x_128 = lean_ctor_get_uint8(x_19, 17);
if (lean_is_exclusive(x_19)) {
 x_129 = x_19;
} else {
 lean_dec_ref(x_19);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_131 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (lean_is_scalar(x_129)) {
 x_132 = lean_alloc_ctor(0, 0, 18);
} else {
 x_132 = x_129;
}
lean_ctor_set_uint8(x_132, 0, x_113);
lean_ctor_set_uint8(x_132, 1, x_114);
lean_ctor_set_uint8(x_132, 2, x_115);
lean_ctor_set_uint8(x_132, 3, x_116);
lean_ctor_set_uint8(x_132, 4, x_117);
lean_ctor_set_uint8(x_132, 5, x_118);
lean_ctor_set_uint8(x_132, 6, x_119);
lean_ctor_set_uint8(x_132, 7, x_120);
lean_ctor_set_uint8(x_132, 8, x_130);
lean_ctor_set_uint8(x_132, 9, x_131);
lean_ctor_set_uint8(x_132, 10, x_121);
lean_ctor_set_uint8(x_132, 11, x_122);
lean_ctor_set_uint8(x_132, 12, x_123);
lean_ctor_set_uint8(x_132, 13, x_124);
lean_ctor_set_uint8(x_132, 14, x_125);
lean_ctor_set_uint8(x_132, 15, x_126);
lean_ctor_set_uint8(x_132, 16, x_127);
lean_ctor_set_uint8(x_132, 17, x_128);
x_133 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_132);
x_134 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_105);
lean_ctor_set(x_134, 2, x_106);
lean_ctor_set(x_134, 3, x_107);
lean_ctor_set(x_134, 4, x_108);
lean_ctor_set(x_134, 5, x_109);
lean_ctor_set(x_134, 6, x_110);
lean_ctor_set_uint64(x_134, sizeof(void*)*7, x_133);
lean_ctor_set_uint8(x_134, sizeof(void*)*7 + 8, x_104);
lean_ctor_set_uint8(x_134, sizeof(void*)*7 + 9, x_111);
lean_ctor_set_uint8(x_134, sizeof(void*)*7 + 10, x_112);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_3);
lean_inc(x_101);
x_135 = l_Lean_Meta_kabstract(x_101, x_3, x_103, x_134, x_14, x_15, x_16, x_102);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Lean_Expr_hasLooseBVars(x_136);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_136);
lean_dec(x_101);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_139 = l_Lean_indentExpr(x_3);
x_140 = l_Lean_MVarId_rewrite___lambda__5___closed__2;
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
x_145 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_8, x_144, x_13, x_14, x_15, x_16, x_137);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_148 = x_145;
} else {
 lean_dec_ref(x_145);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_box(0);
x_151 = l_Lean_MVarId_rewrite___lambda__4(x_136, x_4, x_101, x_5, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_150, x_13, x_14, x_15, x_16, x_137);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_101);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_152 = lean_ctor_get(x_135, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_135, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_154 = x_135;
} else {
 lean_dec_ref(x_135);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_1);
x_19 = l_Lean_Meta_getLevel(x_1, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_2);
x_22 = l_Lean_Meta_getLevel(x_2, x_14, x_15, x_16, x_17, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_MVarId_rewrite___lambda__2___closed__2;
x_29 = l_Lean_Expr_const___override(x_28, x_27);
x_30 = l_Lean_mkApp6(x_29, x_1, x_2, x_3, x_4, x_5, x_6);
x_99 = lean_ctor_get(x_16, 2);
lean_inc(x_99);
x_100 = l_Lean_MVarId_rewrite___lambda__2___closed__4;
x_101 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_99, x_100);
lean_dec(x_99);
if (x_101 == 0)
{
uint8_t x_102; 
x_102 = 1;
x_31 = x_102;
goto block_98;
}
else
{
uint8_t x_103; 
x_103 = 0;
x_31 = x_103;
goto block_98;
}
block_98:
{
uint8_t x_32; lean_object* x_33; 
x_32 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_33 = l_Lean_Meta_postprocessAppMVars(x_7, x_8, x_9, x_10, x_31, x_32, x_14, x_15, x_16, x_17, x_24);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_array_size(x_9);
x_36 = 0;
x_37 = l_Array_mapMUnsafe_map___at_Lean_MVarId_rewrite___spec__1(x_35, x_36, x_9);
x_38 = lean_array_get_size(x_37);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_nat_dec_lt(x_39, x_38);
if (x_40 == 0)
{
lean_object* x_86; 
lean_dec(x_38);
lean_dec(x_37);
x_86 = l_Lean_MVarId_rewrite___lambda__2___closed__3;
x_41 = x_86;
x_42 = x_34;
goto block_85;
}
else
{
uint8_t x_87; 
x_87 = lean_nat_dec_le(x_38, x_38);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_38);
lean_dec(x_37);
x_88 = l_Lean_MVarId_rewrite___lambda__2___closed__3;
x_41 = x_88;
x_42 = x_34;
goto block_85;
}
else
{
size_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_90 = l_Lean_MVarId_rewrite___lambda__2___closed__3;
x_91 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__5(x_37, x_36, x_89, x_90, x_14, x_15, x_16, x_17, x_34);
lean_dec(x_37);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_41 = x_92;
x_42 = x_93;
goto block_85;
}
}
block_85:
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_Meta_getMVarsNoDelayed(x_11, x_14, x_15, x_16, x_17, x_42);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_array_get_size(x_45);
x_47 = lean_nat_dec_lt(x_39, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_46);
lean_dec(x_45);
x_48 = l_Lean_MVarId_rewrite___lambda__2___closed__3;
x_49 = l_Array_append___rarg(x_41, x_48);
x_50 = lean_array_to_list(x_49);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_12);
lean_ctor_set(x_51, 1, x_30);
lean_ctor_set(x_51, 2, x_50);
lean_ctor_set(x_43, 0, x_51);
return x_43;
}
else
{
uint8_t x_52; 
x_52 = lean_nat_dec_le(x_46, x_46);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_46);
lean_dec(x_45);
x_53 = l_Lean_MVarId_rewrite___lambda__2___closed__3;
x_54 = l_Array_append___rarg(x_41, x_53);
x_55 = lean_array_to_list(x_54);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_12);
lean_ctor_set(x_56, 1, x_30);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set(x_43, 0, x_56);
return x_43;
}
else
{
size_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_58 = l_Lean_MVarId_rewrite___lambda__2___closed__3;
x_59 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__6(x_41, x_45, x_36, x_57, x_58);
lean_dec(x_45);
x_60 = l_Array_append___rarg(x_41, x_59);
lean_dec(x_59);
x_61 = lean_array_to_list(x_60);
x_62 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_62, 0, x_12);
lean_ctor_set(x_62, 1, x_30);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_43, 0, x_62);
return x_43;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_43, 0);
x_64 = lean_ctor_get(x_43, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_43);
x_65 = lean_array_get_size(x_63);
x_66 = lean_nat_dec_lt(x_39, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_65);
lean_dec(x_63);
x_67 = l_Lean_MVarId_rewrite___lambda__2___closed__3;
x_68 = l_Array_append___rarg(x_41, x_67);
x_69 = lean_array_to_list(x_68);
x_70 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_70, 0, x_12);
lean_ctor_set(x_70, 1, x_30);
lean_ctor_set(x_70, 2, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_64);
return x_71;
}
else
{
uint8_t x_72; 
x_72 = lean_nat_dec_le(x_65, x_65);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_65);
lean_dec(x_63);
x_73 = l_Lean_MVarId_rewrite___lambda__2___closed__3;
x_74 = l_Array_append___rarg(x_41, x_73);
x_75 = lean_array_to_list(x_74);
x_76 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_76, 0, x_12);
lean_ctor_set(x_76, 1, x_30);
lean_ctor_set(x_76, 2, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_64);
return x_77;
}
else
{
size_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_78 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_79 = l_Lean_MVarId_rewrite___lambda__2___closed__3;
x_80 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__6(x_41, x_63, x_36, x_78, x_79);
lean_dec(x_63);
x_81 = l_Array_append___rarg(x_41, x_80);
lean_dec(x_80);
x_82 = lean_array_to_list(x_81);
x_83 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_83, 0, x_12);
lean_ctor_set(x_83, 1, x_30);
lean_ctor_set(x_83, 2, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_64);
return x_84;
}
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_30);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
x_94 = !lean_is_exclusive(x_33);
if (x_94 == 0)
{
return x_33;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_33, 0);
x_96 = lean_ctor_get(x_33, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_33);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
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
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_22);
if (x_104 == 0)
{
return x_22;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_22, 0);
x_106 = lean_ctor_get(x_22, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_22);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
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
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_19);
if (x_108 == 0)
{
return x_19;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_19, 0);
x_110 = lean_ctor_get(x_19, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_19);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_18 = lean_infer_type(x_1, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_51; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_MVarId_rewrite___lambda__3___closed__2;
x_22 = 0;
lean_inc(x_3);
lean_inc(x_2);
x_23 = l_Lean_Expr_lam___override(x_21, x_2, x_3, x_22);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_23);
x_51 = l_Lean_Meta_check(x_23, x_13, x_14, x_15, x_16, x_20);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_24 = x_52;
goto block_50;
}
else
{
uint8_t x_53; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_51, 0);
x_55 = lean_ctor_get(x_51, 1);
x_56 = l_Lean_Exception_isInterrupt(x_54);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = l_Lean_Exception_isRuntime(x_54);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_free_object(x_51);
x_58 = l_Lean_MessageData_ofExpr(x_23);
x_59 = l_Lean_indentD(x_58);
x_60 = l_Lean_MVarId_rewrite___lambda__3___closed__8;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l_Lean_MVarId_rewrite___lambda__3___closed__10;
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_Exception_toMessageData(x_54);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_MVarId_rewrite___lambda__3___closed__12;
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_MVarId_rewrite___lambda__3___closed__13;
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_MVarId_rewrite___lambda__3___closed__15;
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_MVarId_rewrite___lambda__3___closed__19;
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_MVarId_rewrite___lambda__3___closed__21;
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_MVarId_rewrite___lambda__3___closed__24;
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_MVarId_rewrite___lambda__3___closed__26;
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_8, x_80, x_13, x_14, x_15, x_16, x_55);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
return x_81;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_81);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
else
{
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
return x_51;
}
}
else
{
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
return x_51;
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_ctor_get(x_51, 0);
x_87 = lean_ctor_get(x_51, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_51);
x_88 = l_Lean_Exception_isInterrupt(x_86);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = l_Lean_Exception_isRuntime(x_86);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_90 = l_Lean_MessageData_ofExpr(x_23);
x_91 = l_Lean_indentD(x_90);
x_92 = l_Lean_MVarId_rewrite___lambda__3___closed__8;
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = l_Lean_MVarId_rewrite___lambda__3___closed__10;
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_Exception_toMessageData(x_86);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_MVarId_rewrite___lambda__3___closed__12;
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_MVarId_rewrite___lambda__3___closed__13;
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_MVarId_rewrite___lambda__3___closed__15;
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_MVarId_rewrite___lambda__3___closed__19;
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_MVarId_rewrite___lambda__3___closed__21;
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Lean_MVarId_rewrite___lambda__3___closed__24;
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Lean_MVarId_rewrite___lambda__3___closed__26;
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_8, x_112, x_13, x_14, x_15, x_16, x_87);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
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
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
else
{
lean_object* x_118; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_86);
lean_ctor_set(x_118, 1, x_87);
return x_118;
}
}
else
{
lean_object* x_119; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_86);
lean_ctor_set(x_119, 1, x_87);
return x_119;
}
}
}
block_50:
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
lean_inc(x_19);
x_25 = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lambda__1___boxed), 8, 2);
lean_closure_set(x_25, 0, x_3);
lean_closure_set(x_25, 1, x_19);
x_26 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_2);
x_27 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__4___rarg(x_21, x_22, x_2, x_25, x_26, x_13, x_14, x_15, x_16, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l_Lean_MessageData_ofExpr(x_23);
x_32 = l_Lean_indentD(x_31);
x_33 = l_Lean_MVarId_rewrite___lambda__3___closed__4;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_8, x_37, x_13, x_14, x_15, x_16, x_30);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_27, 1);
lean_inc(x_43);
lean_dec(x_27);
x_44 = lean_box(0);
x_45 = l_Lean_MVarId_rewrite___lambda__6(x_2, x_19, x_4, x_5, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_44, x_13, x_14, x_15, x_16, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_27);
if (x_46 == 0)
{
return x_27;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_27, 0);
x_48 = lean_ctor_get(x_27, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_27);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
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
x_120 = !lean_is_exclusive(x_18);
if (x_120 == 0)
{
return x_18;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_18, 0);
x_122 = lean_ctor_get(x_18, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_18);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_expr_instantiate1(x_1, x_2);
x_19 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_18, x_13, x_14, x_15, x_16, x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Expr_hasBinderNameHint(x_2);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_Lean_MVarId_rewrite___lambda__7(x_3, x_4, x_1, x_5, x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_20, x_13, x_14, x_15, x_16, x_21);
return x_23;
}
else
{
lean_object* x_24; 
lean_inc(x_16);
lean_inc(x_15);
x_24 = l_Lean_Expr_resolveBinderNameHint(x_20, x_15, x_16, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_MVarId_rewrite___lambda__7(x_3, x_4, x_1, x_5, x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_25, x_13, x_14, x_15, x_16, x_26);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
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
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_1, x_13, x_14, x_15, x_16, x_17);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 8);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_13, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_13, 3);
lean_inc(x_27);
x_28 = lean_ctor_get(x_13, 4);
lean_inc(x_28);
x_29 = lean_ctor_get(x_13, 5);
lean_inc(x_29);
x_30 = lean_ctor_get(x_13, 6);
lean_inc(x_30);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint64_t x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 9);
x_33 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 10);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_ctor_set_uint8(x_19, 8, x_34);
lean_ctor_set_uint8(x_19, 9, x_35);
x_36 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_19);
x_37 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_37, 0, x_19);
lean_ctor_set(x_37, 1, x_25);
lean_ctor_set(x_37, 2, x_26);
lean_ctor_set(x_37, 3, x_27);
lean_ctor_set(x_37, 4, x_28);
lean_ctor_set(x_37, 5, x_29);
lean_ctor_set(x_37, 6, x_30);
lean_ctor_set_uint64(x_37, sizeof(void*)*7, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*7 + 8, x_24);
lean_ctor_set_uint8(x_37, sizeof(void*)*7 + 9, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*7 + 10, x_33);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_3);
lean_inc(x_21);
x_38 = l_Lean_Meta_kabstract(x_21, x_3, x_23, x_37, x_14, x_15, x_16, x_22);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Expr_hasLooseBVars(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_39);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_42 = l_Lean_indentExpr(x_3);
x_43 = l_Lean_MVarId_rewrite___lambda__5___closed__2;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_42);
lean_ctor_set(x_18, 0, x_43);
x_44 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_18);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_8, x_46, x_13, x_14, x_15, x_16, x_40);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_free_object(x_18);
x_52 = lean_box(0);
x_53 = l_Lean_MVarId_rewrite___lambda__8(x_39, x_4, x_21, x_5, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_52, x_13, x_14, x_15, x_16, x_40);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_free_object(x_18);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_38);
if (x_54 == 0)
{
return x_38;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_38, 0);
x_56 = lean_ctor_get(x_38, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_38);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; lean_object* x_78; uint64_t x_79; lean_object* x_80; lean_object* x_81; 
x_58 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 9);
x_59 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 10);
x_60 = lean_ctor_get_uint8(x_19, 0);
x_61 = lean_ctor_get_uint8(x_19, 1);
x_62 = lean_ctor_get_uint8(x_19, 2);
x_63 = lean_ctor_get_uint8(x_19, 3);
x_64 = lean_ctor_get_uint8(x_19, 4);
x_65 = lean_ctor_get_uint8(x_19, 5);
x_66 = lean_ctor_get_uint8(x_19, 6);
x_67 = lean_ctor_get_uint8(x_19, 7);
x_68 = lean_ctor_get_uint8(x_19, 10);
x_69 = lean_ctor_get_uint8(x_19, 11);
x_70 = lean_ctor_get_uint8(x_19, 12);
x_71 = lean_ctor_get_uint8(x_19, 13);
x_72 = lean_ctor_get_uint8(x_19, 14);
x_73 = lean_ctor_get_uint8(x_19, 15);
x_74 = lean_ctor_get_uint8(x_19, 16);
x_75 = lean_ctor_get_uint8(x_19, 17);
lean_dec(x_19);
x_76 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_77 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_78 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_78, 0, x_60);
lean_ctor_set_uint8(x_78, 1, x_61);
lean_ctor_set_uint8(x_78, 2, x_62);
lean_ctor_set_uint8(x_78, 3, x_63);
lean_ctor_set_uint8(x_78, 4, x_64);
lean_ctor_set_uint8(x_78, 5, x_65);
lean_ctor_set_uint8(x_78, 6, x_66);
lean_ctor_set_uint8(x_78, 7, x_67);
lean_ctor_set_uint8(x_78, 8, x_76);
lean_ctor_set_uint8(x_78, 9, x_77);
lean_ctor_set_uint8(x_78, 10, x_68);
lean_ctor_set_uint8(x_78, 11, x_69);
lean_ctor_set_uint8(x_78, 12, x_70);
lean_ctor_set_uint8(x_78, 13, x_71);
lean_ctor_set_uint8(x_78, 14, x_72);
lean_ctor_set_uint8(x_78, 15, x_73);
lean_ctor_set_uint8(x_78, 16, x_74);
lean_ctor_set_uint8(x_78, 17, x_75);
x_79 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_78);
x_80 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_25);
lean_ctor_set(x_80, 2, x_26);
lean_ctor_set(x_80, 3, x_27);
lean_ctor_set(x_80, 4, x_28);
lean_ctor_set(x_80, 5, x_29);
lean_ctor_set(x_80, 6, x_30);
lean_ctor_set_uint64(x_80, sizeof(void*)*7, x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 8, x_24);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 9, x_58);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 10, x_59);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_3);
lean_inc(x_21);
x_81 = l_Lean_Meta_kabstract(x_21, x_3, x_23, x_80, x_14, x_15, x_16, x_22);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_Expr_hasLooseBVars(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_82);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_85 = l_Lean_indentExpr(x_3);
x_86 = l_Lean_MVarId_rewrite___lambda__5___closed__2;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_85);
lean_ctor_set(x_18, 0, x_86);
x_87 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_18);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_8, x_89, x_13, x_14, x_15, x_16, x_83);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_93 = x_90;
} else {
 lean_dec_ref(x_90);
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
else
{
lean_object* x_95; lean_object* x_96; 
lean_free_object(x_18);
x_95 = lean_box(0);
x_96 = l_Lean_MVarId_rewrite___lambda__8(x_82, x_4, x_21, x_5, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_95, x_13, x_14, x_15, x_16, x_83);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_free_object(x_18);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_97 = lean_ctor_get(x_81, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_81, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_99 = x_81;
} else {
 lean_dec_ref(x_81);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; lean_object* x_129; uint8_t x_130; uint8_t x_131; lean_object* x_132; uint64_t x_133; lean_object* x_134; lean_object* x_135; 
x_101 = lean_ctor_get(x_18, 0);
x_102 = lean_ctor_get(x_18, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_18);
x_103 = lean_ctor_get(x_2, 0);
x_104 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 8);
x_105 = lean_ctor_get(x_13, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_13, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_13, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_13, 4);
lean_inc(x_108);
x_109 = lean_ctor_get(x_13, 5);
lean_inc(x_109);
x_110 = lean_ctor_get(x_13, 6);
lean_inc(x_110);
x_111 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 9);
x_112 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 10);
x_113 = lean_ctor_get_uint8(x_19, 0);
x_114 = lean_ctor_get_uint8(x_19, 1);
x_115 = lean_ctor_get_uint8(x_19, 2);
x_116 = lean_ctor_get_uint8(x_19, 3);
x_117 = lean_ctor_get_uint8(x_19, 4);
x_118 = lean_ctor_get_uint8(x_19, 5);
x_119 = lean_ctor_get_uint8(x_19, 6);
x_120 = lean_ctor_get_uint8(x_19, 7);
x_121 = lean_ctor_get_uint8(x_19, 10);
x_122 = lean_ctor_get_uint8(x_19, 11);
x_123 = lean_ctor_get_uint8(x_19, 12);
x_124 = lean_ctor_get_uint8(x_19, 13);
x_125 = lean_ctor_get_uint8(x_19, 14);
x_126 = lean_ctor_get_uint8(x_19, 15);
x_127 = lean_ctor_get_uint8(x_19, 16);
x_128 = lean_ctor_get_uint8(x_19, 17);
if (lean_is_exclusive(x_19)) {
 x_129 = x_19;
} else {
 lean_dec_ref(x_19);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_131 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (lean_is_scalar(x_129)) {
 x_132 = lean_alloc_ctor(0, 0, 18);
} else {
 x_132 = x_129;
}
lean_ctor_set_uint8(x_132, 0, x_113);
lean_ctor_set_uint8(x_132, 1, x_114);
lean_ctor_set_uint8(x_132, 2, x_115);
lean_ctor_set_uint8(x_132, 3, x_116);
lean_ctor_set_uint8(x_132, 4, x_117);
lean_ctor_set_uint8(x_132, 5, x_118);
lean_ctor_set_uint8(x_132, 6, x_119);
lean_ctor_set_uint8(x_132, 7, x_120);
lean_ctor_set_uint8(x_132, 8, x_130);
lean_ctor_set_uint8(x_132, 9, x_131);
lean_ctor_set_uint8(x_132, 10, x_121);
lean_ctor_set_uint8(x_132, 11, x_122);
lean_ctor_set_uint8(x_132, 12, x_123);
lean_ctor_set_uint8(x_132, 13, x_124);
lean_ctor_set_uint8(x_132, 14, x_125);
lean_ctor_set_uint8(x_132, 15, x_126);
lean_ctor_set_uint8(x_132, 16, x_127);
lean_ctor_set_uint8(x_132, 17, x_128);
x_133 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_132);
x_134 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_105);
lean_ctor_set(x_134, 2, x_106);
lean_ctor_set(x_134, 3, x_107);
lean_ctor_set(x_134, 4, x_108);
lean_ctor_set(x_134, 5, x_109);
lean_ctor_set(x_134, 6, x_110);
lean_ctor_set_uint64(x_134, sizeof(void*)*7, x_133);
lean_ctor_set_uint8(x_134, sizeof(void*)*7 + 8, x_104);
lean_ctor_set_uint8(x_134, sizeof(void*)*7 + 9, x_111);
lean_ctor_set_uint8(x_134, sizeof(void*)*7 + 10, x_112);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_3);
lean_inc(x_101);
x_135 = l_Lean_Meta_kabstract(x_101, x_3, x_103, x_134, x_14, x_15, x_16, x_102);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Lean_Expr_hasLooseBVars(x_136);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_136);
lean_dec(x_101);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_139 = l_Lean_indentExpr(x_3);
x_140 = l_Lean_MVarId_rewrite___lambda__5___closed__2;
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
x_145 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_8, x_144, x_13, x_14, x_15, x_16, x_137);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_148 = x_145;
} else {
 lean_dec_ref(x_145);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_box(0);
x_151 = l_Lean_MVarId_rewrite___lambda__8(x_136, x_4, x_101, x_5, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_150, x_13, x_14, x_15, x_16, x_137);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_101);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_152 = lean_ctor_get(x_135, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_135, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_154 = x_135;
} else {
 lean_dec_ref(x_135);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_1);
x_20 = l_Lean_Meta_getLevel(x_1, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_2);
x_23 = l_Lean_Meta_getLevel(x_2, x_15, x_16, x_17, x_18, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_3);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_3);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_MVarId_rewrite___lambda__2___closed__2;
x_29 = l_Lean_Expr_const___override(x_28, x_27);
x_30 = l_Lean_mkApp6(x_29, x_1, x_2, x_4, x_5, x_6, x_7);
x_91 = lean_ctor_get(x_17, 2);
lean_inc(x_91);
x_92 = l_Lean_MVarId_rewrite___lambda__2___closed__4;
x_93 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_91, x_92);
lean_dec(x_91);
if (x_93 == 0)
{
uint8_t x_94; 
x_94 = 1;
x_31 = x_94;
goto block_90;
}
else
{
uint8_t x_95; 
x_95 = 0;
x_31 = x_95;
goto block_90;
}
block_90:
{
uint8_t x_32; lean_object* x_33; 
x_32 = 0;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_33 = l_Lean_Meta_postprocessAppMVars(x_8, x_9, x_10, x_11, x_31, x_32, x_15, x_16, x_17, x_18, x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_array_size(x_10);
x_36 = 0;
x_37 = l_Array_mapMUnsafe_map___at_Lean_MVarId_rewrite___spec__1(x_35, x_36, x_10);
x_38 = lean_array_get_size(x_37);
x_39 = lean_array_mk(x_3);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_lt(x_40, x_38);
if (x_41 == 0)
{
lean_dec(x_38);
lean_dec(x_37);
lean_inc(x_39);
x_42 = x_39;
x_43 = x_34;
goto block_80;
}
else
{
uint8_t x_81; 
x_81 = lean_nat_dec_le(x_38, x_38);
if (x_81 == 0)
{
lean_dec(x_38);
lean_dec(x_37);
lean_inc(x_39);
x_42 = x_39;
x_43 = x_34;
goto block_80;
}
else
{
size_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_usize_of_nat(x_38);
lean_dec(x_38);
lean_inc(x_39);
x_83 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__5(x_37, x_36, x_82, x_39, x_15, x_16, x_17, x_18, x_34);
lean_dec(x_37);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_42 = x_84;
x_43 = x_85;
goto block_80;
}
}
block_80:
{
lean_object* x_44; uint8_t x_45; 
x_44 = l_Lean_Meta_getMVarsNoDelayed(x_12, x_15, x_16, x_17, x_18, x_43);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_array_get_size(x_46);
x_48 = lean_nat_dec_lt(x_40, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_47);
lean_dec(x_46);
x_49 = l_Array_append___rarg(x_42, x_39);
lean_dec(x_39);
x_50 = lean_array_to_list(x_49);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_13);
lean_ctor_set(x_51, 1, x_30);
lean_ctor_set(x_51, 2, x_50);
lean_ctor_set(x_44, 0, x_51);
return x_44;
}
else
{
uint8_t x_52; 
x_52 = lean_nat_dec_le(x_47, x_47);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_47);
lean_dec(x_46);
x_53 = l_Array_append___rarg(x_42, x_39);
lean_dec(x_39);
x_54 = lean_array_to_list(x_53);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_13);
lean_ctor_set(x_55, 1, x_30);
lean_ctor_set(x_55, 2, x_54);
lean_ctor_set(x_44, 0, x_55);
return x_44;
}
else
{
size_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_57 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__7(x_42, x_46, x_36, x_56, x_39);
lean_dec(x_46);
x_58 = l_Array_append___rarg(x_42, x_57);
lean_dec(x_57);
x_59 = lean_array_to_list(x_58);
x_60 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_60, 0, x_13);
lean_ctor_set(x_60, 1, x_30);
lean_ctor_set(x_60, 2, x_59);
lean_ctor_set(x_44, 0, x_60);
return x_44;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_44, 0);
x_62 = lean_ctor_get(x_44, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_44);
x_63 = lean_array_get_size(x_61);
x_64 = lean_nat_dec_lt(x_40, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_63);
lean_dec(x_61);
x_65 = l_Array_append___rarg(x_42, x_39);
lean_dec(x_39);
x_66 = lean_array_to_list(x_65);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_13);
lean_ctor_set(x_67, 1, x_30);
lean_ctor_set(x_67, 2, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_62);
return x_68;
}
else
{
uint8_t x_69; 
x_69 = lean_nat_dec_le(x_63, x_63);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_63);
lean_dec(x_61);
x_70 = l_Array_append___rarg(x_42, x_39);
lean_dec(x_39);
x_71 = lean_array_to_list(x_70);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_13);
lean_ctor_set(x_72, 1, x_30);
lean_ctor_set(x_72, 2, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_62);
return x_73;
}
else
{
size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_usize_of_nat(x_63);
lean_dec(x_63);
x_75 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__7(x_42, x_61, x_36, x_74, x_39);
lean_dec(x_61);
x_76 = l_Array_append___rarg(x_42, x_75);
lean_dec(x_75);
x_77 = lean_array_to_list(x_76);
x_78 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_78, 0, x_13);
lean_ctor_set(x_78, 1, x_30);
lean_ctor_set(x_78, 2, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_62);
return x_79;
}
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_30);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_3);
x_86 = !lean_is_exclusive(x_33);
if (x_86 == 0)
{
return x_33;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_33, 0);
x_88 = lean_ctor_get(x_33, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_33);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
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
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_23);
if (x_96 == 0)
{
return x_23;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_23, 0);
x_98 = lean_ctor_get(x_23, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_23);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
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
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_20);
if (x_100 == 0)
{
return x_20;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_20, 0);
x_102 = lean_ctor_get(x_20, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_20);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_19 = lean_infer_type(x_1, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_52; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_MVarId_rewrite___lambda__3___closed__2;
x_23 = 0;
lean_inc(x_3);
lean_inc(x_2);
x_24 = l_Lean_Expr_lam___override(x_22, x_2, x_3, x_23);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_24);
x_52 = l_Lean_Meta_check(x_24, x_14, x_15, x_16, x_17, x_21);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_25 = x_53;
goto block_51;
}
else
{
uint8_t x_54; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_52, 0);
x_56 = lean_ctor_get(x_52, 1);
x_57 = l_Lean_Exception_isInterrupt(x_55);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = l_Lean_Exception_isRuntime(x_55);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_free_object(x_52);
x_59 = l_Lean_MessageData_ofExpr(x_24);
x_60 = l_Lean_indentD(x_59);
x_61 = l_Lean_MVarId_rewrite___lambda__3___closed__8;
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l_Lean_MVarId_rewrite___lambda__3___closed__10;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_Exception_toMessageData(x_55);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_MVarId_rewrite___lambda__3___closed__12;
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_MVarId_rewrite___lambda__3___closed__13;
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_MVarId_rewrite___lambda__3___closed__15;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_MVarId_rewrite___lambda__3___closed__19;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_MVarId_rewrite___lambda__3___closed__21;
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_MVarId_rewrite___lambda__3___closed__24;
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_MVarId_rewrite___lambda__3___closed__26;
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_9, x_81, x_14, x_15, x_16, x_17, x_56);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
return x_82;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_82, 0);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_82);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
else
{
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
return x_52;
}
}
else
{
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
return x_52;
}
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_52, 0);
x_88 = lean_ctor_get(x_52, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_52);
x_89 = l_Lean_Exception_isInterrupt(x_87);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = l_Lean_Exception_isRuntime(x_87);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_91 = l_Lean_MessageData_ofExpr(x_24);
x_92 = l_Lean_indentD(x_91);
x_93 = l_Lean_MVarId_rewrite___lambda__3___closed__8;
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = l_Lean_MVarId_rewrite___lambda__3___closed__10;
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_Exception_toMessageData(x_87);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_MVarId_rewrite___lambda__3___closed__12;
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_MVarId_rewrite___lambda__3___closed__13;
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_MVarId_rewrite___lambda__3___closed__15;
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_MVarId_rewrite___lambda__3___closed__19;
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_MVarId_rewrite___lambda__3___closed__21;
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_MVarId_rewrite___lambda__3___closed__24;
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_MVarId_rewrite___lambda__3___closed__26;
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_9, x_113, x_14, x_15, x_16, x_17, x_88);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_117 = x_114;
} else {
 lean_dec_ref(x_114);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
else
{
lean_object* x_119; 
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_87);
lean_ctor_set(x_119, 1, x_88);
return x_119;
}
}
else
{
lean_object* x_120; 
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_87);
lean_ctor_set(x_120, 1, x_88);
return x_120;
}
}
}
block_51:
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
lean_inc(x_20);
x_26 = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lambda__1___boxed), 8, 2);
lean_closure_set(x_26, 0, x_3);
lean_closure_set(x_26, 1, x_20);
x_27 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_2);
x_28 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__4___rarg(x_22, x_23, x_2, x_26, x_27, x_14, x_15, x_16, x_17, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_MessageData_ofExpr(x_24);
x_33 = l_Lean_indentD(x_32);
x_34 = l_Lean_MVarId_rewrite___lambda__3___closed__4;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_9, x_38, x_14, x_15, x_16, x_17, x_31);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
return x_39;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_39);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_28, 1);
lean_inc(x_44);
lean_dec(x_28);
x_45 = lean_box(0);
x_46 = l_Lean_MVarId_rewrite___lambda__10(x_2, x_20, x_4, x_5, x_6, x_24, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_45, x_14, x_15, x_16, x_17, x_44);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_28);
if (x_47 == 0)
{
return x_28;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_28, 0);
x_49 = lean_ctor_get(x_28, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_28);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
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
x_121 = !lean_is_exclusive(x_19);
if (x_121 == 0)
{
return x_19;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_19, 0);
x_123 = lean_ctor_get(x_19, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_19);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_expr_instantiate1(x_1, x_2);
x_20 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_19, x_14, x_15, x_16, x_17, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Expr_hasBinderNameHint(x_2);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = l_Lean_MVarId_rewrite___lambda__11(x_3, x_4, x_1, x_5, x_6, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_21, x_14, x_15, x_16, x_17, x_22);
return x_24;
}
else
{
lean_object* x_25; 
lean_inc(x_17);
lean_inc(x_16);
x_25 = l_Lean_Expr_resolveBinderNameHint(x_21, x_16, x_17, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_MVarId_rewrite___lambda__11(x_3, x_4, x_1, x_5, x_6, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_26, x_14, x_15, x_16, x_17, x_27);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
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
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_1, x_14, x_15, x_16, x_17, x_18);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 8);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_14, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_14, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_14, 4);
lean_inc(x_29);
x_30 = lean_ctor_get(x_14, 5);
lean_inc(x_30);
x_31 = lean_ctor_get(x_14, 6);
lean_inc(x_31);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint64_t x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 9);
x_34 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 10);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_ctor_set_uint8(x_20, 8, x_35);
lean_ctor_set_uint8(x_20, 9, x_36);
x_37 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_20);
x_38 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_38, 0, x_20);
lean_ctor_set(x_38, 1, x_26);
lean_ctor_set(x_38, 2, x_27);
lean_ctor_set(x_38, 3, x_28);
lean_ctor_set(x_38, 4, x_29);
lean_ctor_set(x_38, 5, x_30);
lean_ctor_set(x_38, 6, x_31);
lean_ctor_set_uint64(x_38, sizeof(void*)*7, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*7 + 8, x_25);
lean_ctor_set_uint8(x_38, sizeof(void*)*7 + 9, x_33);
lean_ctor_set_uint8(x_38, sizeof(void*)*7 + 10, x_34);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_3);
lean_inc(x_22);
x_39 = l_Lean_Meta_kabstract(x_22, x_3, x_24, x_38, x_15, x_16, x_17, x_23);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Expr_hasLooseBVars(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_40);
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_43 = l_Lean_indentExpr(x_3);
x_44 = l_Lean_MVarId_rewrite___lambda__5___closed__2;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_43);
lean_ctor_set(x_19, 0, x_44);
x_45 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_19);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_9, x_47, x_14, x_15, x_16, x_17, x_41);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
return x_48;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_48);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_free_object(x_19);
x_53 = lean_box(0);
x_54 = l_Lean_MVarId_rewrite___lambda__12(x_40, x_4, x_22, x_5, x_6, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_53, x_14, x_15, x_16, x_17, x_41);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_free_object(x_19);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_39);
if (x_55 == 0)
{
return x_39;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_39, 0);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_39);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; lean_object* x_79; uint64_t x_80; lean_object* x_81; lean_object* x_82; 
x_59 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 9);
x_60 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 10);
x_61 = lean_ctor_get_uint8(x_20, 0);
x_62 = lean_ctor_get_uint8(x_20, 1);
x_63 = lean_ctor_get_uint8(x_20, 2);
x_64 = lean_ctor_get_uint8(x_20, 3);
x_65 = lean_ctor_get_uint8(x_20, 4);
x_66 = lean_ctor_get_uint8(x_20, 5);
x_67 = lean_ctor_get_uint8(x_20, 6);
x_68 = lean_ctor_get_uint8(x_20, 7);
x_69 = lean_ctor_get_uint8(x_20, 10);
x_70 = lean_ctor_get_uint8(x_20, 11);
x_71 = lean_ctor_get_uint8(x_20, 12);
x_72 = lean_ctor_get_uint8(x_20, 13);
x_73 = lean_ctor_get_uint8(x_20, 14);
x_74 = lean_ctor_get_uint8(x_20, 15);
x_75 = lean_ctor_get_uint8(x_20, 16);
x_76 = lean_ctor_get_uint8(x_20, 17);
lean_dec(x_20);
x_77 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_78 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_79 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_79, 0, x_61);
lean_ctor_set_uint8(x_79, 1, x_62);
lean_ctor_set_uint8(x_79, 2, x_63);
lean_ctor_set_uint8(x_79, 3, x_64);
lean_ctor_set_uint8(x_79, 4, x_65);
lean_ctor_set_uint8(x_79, 5, x_66);
lean_ctor_set_uint8(x_79, 6, x_67);
lean_ctor_set_uint8(x_79, 7, x_68);
lean_ctor_set_uint8(x_79, 8, x_77);
lean_ctor_set_uint8(x_79, 9, x_78);
lean_ctor_set_uint8(x_79, 10, x_69);
lean_ctor_set_uint8(x_79, 11, x_70);
lean_ctor_set_uint8(x_79, 12, x_71);
lean_ctor_set_uint8(x_79, 13, x_72);
lean_ctor_set_uint8(x_79, 14, x_73);
lean_ctor_set_uint8(x_79, 15, x_74);
lean_ctor_set_uint8(x_79, 16, x_75);
lean_ctor_set_uint8(x_79, 17, x_76);
x_80 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_79);
x_81 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_26);
lean_ctor_set(x_81, 2, x_27);
lean_ctor_set(x_81, 3, x_28);
lean_ctor_set(x_81, 4, x_29);
lean_ctor_set(x_81, 5, x_30);
lean_ctor_set(x_81, 6, x_31);
lean_ctor_set_uint64(x_81, sizeof(void*)*7, x_80);
lean_ctor_set_uint8(x_81, sizeof(void*)*7 + 8, x_25);
lean_ctor_set_uint8(x_81, sizeof(void*)*7 + 9, x_59);
lean_ctor_set_uint8(x_81, sizeof(void*)*7 + 10, x_60);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_3);
lean_inc(x_22);
x_82 = l_Lean_Meta_kabstract(x_22, x_3, x_24, x_81, x_15, x_16, x_17, x_23);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Expr_hasLooseBVars(x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_83);
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_86 = l_Lean_indentExpr(x_3);
x_87 = l_Lean_MVarId_rewrite___lambda__5___closed__2;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_86);
lean_ctor_set(x_19, 0, x_87);
x_88 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_19);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_9, x_90, x_14, x_15, x_16, x_17, x_84);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
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
else
{
lean_object* x_96; lean_object* x_97; 
lean_free_object(x_19);
x_96 = lean_box(0);
x_97 = l_Lean_MVarId_rewrite___lambda__12(x_83, x_4, x_22, x_5, x_6, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_96, x_14, x_15, x_16, x_17, x_84);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_free_object(x_19);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_98 = lean_ctor_get(x_82, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_82, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_100 = x_82;
} else {
 lean_dec_ref(x_82);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; lean_object* x_130; uint8_t x_131; uint8_t x_132; lean_object* x_133; uint64_t x_134; lean_object* x_135; lean_object* x_136; 
x_102 = lean_ctor_get(x_19, 0);
x_103 = lean_ctor_get(x_19, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_19);
x_104 = lean_ctor_get(x_2, 0);
x_105 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 8);
x_106 = lean_ctor_get(x_14, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_14, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_14, 3);
lean_inc(x_108);
x_109 = lean_ctor_get(x_14, 4);
lean_inc(x_109);
x_110 = lean_ctor_get(x_14, 5);
lean_inc(x_110);
x_111 = lean_ctor_get(x_14, 6);
lean_inc(x_111);
x_112 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 9);
x_113 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 10);
x_114 = lean_ctor_get_uint8(x_20, 0);
x_115 = lean_ctor_get_uint8(x_20, 1);
x_116 = lean_ctor_get_uint8(x_20, 2);
x_117 = lean_ctor_get_uint8(x_20, 3);
x_118 = lean_ctor_get_uint8(x_20, 4);
x_119 = lean_ctor_get_uint8(x_20, 5);
x_120 = lean_ctor_get_uint8(x_20, 6);
x_121 = lean_ctor_get_uint8(x_20, 7);
x_122 = lean_ctor_get_uint8(x_20, 10);
x_123 = lean_ctor_get_uint8(x_20, 11);
x_124 = lean_ctor_get_uint8(x_20, 12);
x_125 = lean_ctor_get_uint8(x_20, 13);
x_126 = lean_ctor_get_uint8(x_20, 14);
x_127 = lean_ctor_get_uint8(x_20, 15);
x_128 = lean_ctor_get_uint8(x_20, 16);
x_129 = lean_ctor_get_uint8(x_20, 17);
if (lean_is_exclusive(x_20)) {
 x_130 = x_20;
} else {
 lean_dec_ref(x_20);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_132 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (lean_is_scalar(x_130)) {
 x_133 = lean_alloc_ctor(0, 0, 18);
} else {
 x_133 = x_130;
}
lean_ctor_set_uint8(x_133, 0, x_114);
lean_ctor_set_uint8(x_133, 1, x_115);
lean_ctor_set_uint8(x_133, 2, x_116);
lean_ctor_set_uint8(x_133, 3, x_117);
lean_ctor_set_uint8(x_133, 4, x_118);
lean_ctor_set_uint8(x_133, 5, x_119);
lean_ctor_set_uint8(x_133, 6, x_120);
lean_ctor_set_uint8(x_133, 7, x_121);
lean_ctor_set_uint8(x_133, 8, x_131);
lean_ctor_set_uint8(x_133, 9, x_132);
lean_ctor_set_uint8(x_133, 10, x_122);
lean_ctor_set_uint8(x_133, 11, x_123);
lean_ctor_set_uint8(x_133, 12, x_124);
lean_ctor_set_uint8(x_133, 13, x_125);
lean_ctor_set_uint8(x_133, 14, x_126);
lean_ctor_set_uint8(x_133, 15, x_127);
lean_ctor_set_uint8(x_133, 16, x_128);
lean_ctor_set_uint8(x_133, 17, x_129);
x_134 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_133);
x_135 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_106);
lean_ctor_set(x_135, 2, x_107);
lean_ctor_set(x_135, 3, x_108);
lean_ctor_set(x_135, 4, x_109);
lean_ctor_set(x_135, 5, x_110);
lean_ctor_set(x_135, 6, x_111);
lean_ctor_set_uint64(x_135, sizeof(void*)*7, x_134);
lean_ctor_set_uint8(x_135, sizeof(void*)*7 + 8, x_105);
lean_ctor_set_uint8(x_135, sizeof(void*)*7 + 9, x_112);
lean_ctor_set_uint8(x_135, sizeof(void*)*7 + 10, x_113);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_3);
lean_inc(x_102);
x_136 = l_Lean_Meta_kabstract(x_102, x_3, x_104, x_135, x_15, x_16, x_17, x_103);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = l_Lean_Expr_hasLooseBVars(x_137);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_137);
lean_dec(x_102);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_140 = l_Lean_indentExpr(x_3);
x_141 = l_Lean_MVarId_rewrite___lambda__5___closed__2;
x_142 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
x_143 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
x_146 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_9, x_145, x_14, x_15, x_16, x_17, x_138);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_149 = x_146;
} else {
 lean_dec_ref(x_146);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_box(0);
x_152 = l_Lean_MVarId_rewrite___lambda__12(x_137, x_4, x_102, x_5, x_6, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_151, x_14, x_15, x_16, x_17, x_138);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_102);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_153 = lean_ctor_get(x_136, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_136, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_155 = x_136;
} else {
 lean_dec_ref(x_136);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_1);
x_20 = l_Lean_Meta_getLevel(x_1, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_2);
x_23 = l_Lean_Meta_getLevel(x_2, x_15, x_16, x_17, x_18, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_3);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_3);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_MVarId_rewrite___lambda__2___closed__2;
x_29 = l_Lean_Expr_const___override(x_28, x_27);
x_30 = l_Lean_mkApp6(x_29, x_1, x_2, x_4, x_5, x_6, x_7);
x_91 = lean_ctor_get(x_17, 2);
lean_inc(x_91);
x_92 = l_Lean_MVarId_rewrite___lambda__2___closed__4;
x_93 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_91, x_92);
lean_dec(x_91);
if (x_93 == 0)
{
uint8_t x_94; 
x_94 = 1;
x_31 = x_94;
goto block_90;
}
else
{
uint8_t x_95; 
x_95 = 0;
x_31 = x_95;
goto block_90;
}
block_90:
{
uint8_t x_32; lean_object* x_33; 
x_32 = 0;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_33 = l_Lean_Meta_postprocessAppMVars(x_8, x_9, x_10, x_11, x_31, x_32, x_15, x_16, x_17, x_18, x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_array_size(x_10);
x_36 = 0;
x_37 = l_Array_mapMUnsafe_map___at_Lean_MVarId_rewrite___spec__1(x_35, x_36, x_10);
x_38 = lean_array_get_size(x_37);
x_39 = lean_array_mk(x_3);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_lt(x_40, x_38);
if (x_41 == 0)
{
lean_dec(x_38);
lean_dec(x_37);
lean_inc(x_39);
x_42 = x_39;
x_43 = x_34;
goto block_80;
}
else
{
uint8_t x_81; 
x_81 = lean_nat_dec_le(x_38, x_38);
if (x_81 == 0)
{
lean_dec(x_38);
lean_dec(x_37);
lean_inc(x_39);
x_42 = x_39;
x_43 = x_34;
goto block_80;
}
else
{
size_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_usize_of_nat(x_38);
lean_dec(x_38);
lean_inc(x_39);
x_83 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__5(x_37, x_36, x_82, x_39, x_15, x_16, x_17, x_18, x_34);
lean_dec(x_37);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_42 = x_84;
x_43 = x_85;
goto block_80;
}
}
block_80:
{
lean_object* x_44; uint8_t x_45; 
x_44 = l_Lean_Meta_getMVarsNoDelayed(x_12, x_15, x_16, x_17, x_18, x_43);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_array_get_size(x_46);
x_48 = lean_nat_dec_lt(x_40, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_47);
lean_dec(x_46);
x_49 = l_Array_append___rarg(x_42, x_39);
lean_dec(x_39);
x_50 = lean_array_to_list(x_49);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_13);
lean_ctor_set(x_51, 1, x_30);
lean_ctor_set(x_51, 2, x_50);
lean_ctor_set(x_44, 0, x_51);
return x_44;
}
else
{
uint8_t x_52; 
x_52 = lean_nat_dec_le(x_47, x_47);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_47);
lean_dec(x_46);
x_53 = l_Array_append___rarg(x_42, x_39);
lean_dec(x_39);
x_54 = lean_array_to_list(x_53);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_13);
lean_ctor_set(x_55, 1, x_30);
lean_ctor_set(x_55, 2, x_54);
lean_ctor_set(x_44, 0, x_55);
return x_44;
}
else
{
size_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_57 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__8(x_42, x_46, x_36, x_56, x_39);
lean_dec(x_46);
x_58 = l_Array_append___rarg(x_42, x_57);
lean_dec(x_57);
x_59 = lean_array_to_list(x_58);
x_60 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_60, 0, x_13);
lean_ctor_set(x_60, 1, x_30);
lean_ctor_set(x_60, 2, x_59);
lean_ctor_set(x_44, 0, x_60);
return x_44;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_44, 0);
x_62 = lean_ctor_get(x_44, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_44);
x_63 = lean_array_get_size(x_61);
x_64 = lean_nat_dec_lt(x_40, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_63);
lean_dec(x_61);
x_65 = l_Array_append___rarg(x_42, x_39);
lean_dec(x_39);
x_66 = lean_array_to_list(x_65);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_13);
lean_ctor_set(x_67, 1, x_30);
lean_ctor_set(x_67, 2, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_62);
return x_68;
}
else
{
uint8_t x_69; 
x_69 = lean_nat_dec_le(x_63, x_63);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_63);
lean_dec(x_61);
x_70 = l_Array_append___rarg(x_42, x_39);
lean_dec(x_39);
x_71 = lean_array_to_list(x_70);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_13);
lean_ctor_set(x_72, 1, x_30);
lean_ctor_set(x_72, 2, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_62);
return x_73;
}
else
{
size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_usize_of_nat(x_63);
lean_dec(x_63);
x_75 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__8(x_42, x_61, x_36, x_74, x_39);
lean_dec(x_61);
x_76 = l_Array_append___rarg(x_42, x_75);
lean_dec(x_75);
x_77 = lean_array_to_list(x_76);
x_78 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_78, 0, x_13);
lean_ctor_set(x_78, 1, x_30);
lean_ctor_set(x_78, 2, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_62);
return x_79;
}
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_30);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_3);
x_86 = !lean_is_exclusive(x_33);
if (x_86 == 0)
{
return x_33;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_33, 0);
x_88 = lean_ctor_get(x_33, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_33);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
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
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_23);
if (x_96 == 0)
{
return x_23;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_23, 0);
x_98 = lean_ctor_get(x_23, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_23);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
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
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_20);
if (x_100 == 0)
{
return x_20;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_20, 0);
x_102 = lean_ctor_get(x_20, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_20);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_19 = lean_infer_type(x_1, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_52; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_MVarId_rewrite___lambda__3___closed__2;
x_23 = 0;
lean_inc(x_3);
lean_inc(x_2);
x_24 = l_Lean_Expr_lam___override(x_22, x_2, x_3, x_23);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_24);
x_52 = l_Lean_Meta_check(x_24, x_14, x_15, x_16, x_17, x_21);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_25 = x_53;
goto block_51;
}
else
{
uint8_t x_54; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_52, 0);
x_56 = lean_ctor_get(x_52, 1);
x_57 = l_Lean_Exception_isInterrupt(x_55);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = l_Lean_Exception_isRuntime(x_55);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_free_object(x_52);
x_59 = l_Lean_MessageData_ofExpr(x_24);
x_60 = l_Lean_indentD(x_59);
x_61 = l_Lean_MVarId_rewrite___lambda__3___closed__8;
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l_Lean_MVarId_rewrite___lambda__3___closed__10;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_Exception_toMessageData(x_55);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_MVarId_rewrite___lambda__3___closed__12;
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_MVarId_rewrite___lambda__3___closed__13;
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_MVarId_rewrite___lambda__3___closed__15;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_MVarId_rewrite___lambda__3___closed__19;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_MVarId_rewrite___lambda__3___closed__21;
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_MVarId_rewrite___lambda__3___closed__24;
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_MVarId_rewrite___lambda__3___closed__26;
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_9, x_81, x_14, x_15, x_16, x_17, x_56);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
return x_82;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_82, 0);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_82);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
else
{
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
return x_52;
}
}
else
{
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
return x_52;
}
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_52, 0);
x_88 = lean_ctor_get(x_52, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_52);
x_89 = l_Lean_Exception_isInterrupt(x_87);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = l_Lean_Exception_isRuntime(x_87);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_91 = l_Lean_MessageData_ofExpr(x_24);
x_92 = l_Lean_indentD(x_91);
x_93 = l_Lean_MVarId_rewrite___lambda__3___closed__8;
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = l_Lean_MVarId_rewrite___lambda__3___closed__10;
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_Exception_toMessageData(x_87);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_MVarId_rewrite___lambda__3___closed__12;
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_MVarId_rewrite___lambda__3___closed__13;
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_MVarId_rewrite___lambda__3___closed__15;
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_MVarId_rewrite___lambda__3___closed__19;
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_MVarId_rewrite___lambda__3___closed__21;
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_MVarId_rewrite___lambda__3___closed__24;
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_MVarId_rewrite___lambda__3___closed__26;
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_9, x_113, x_14, x_15, x_16, x_17, x_88);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_117 = x_114;
} else {
 lean_dec_ref(x_114);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
else
{
lean_object* x_119; 
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_87);
lean_ctor_set(x_119, 1, x_88);
return x_119;
}
}
else
{
lean_object* x_120; 
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_87);
lean_ctor_set(x_120, 1, x_88);
return x_120;
}
}
}
block_51:
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
lean_inc(x_20);
x_26 = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lambda__1___boxed), 8, 2);
lean_closure_set(x_26, 0, x_3);
lean_closure_set(x_26, 1, x_20);
x_27 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_2);
x_28 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__4___rarg(x_22, x_23, x_2, x_26, x_27, x_14, x_15, x_16, x_17, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_MessageData_ofExpr(x_24);
x_33 = l_Lean_indentD(x_32);
x_34 = l_Lean_MVarId_rewrite___lambda__3___closed__4;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_9, x_38, x_14, x_15, x_16, x_17, x_31);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
return x_39;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_39);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_28, 1);
lean_inc(x_44);
lean_dec(x_28);
x_45 = lean_box(0);
x_46 = l_Lean_MVarId_rewrite___lambda__14(x_2, x_20, x_4, x_5, x_6, x_24, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_45, x_14, x_15, x_16, x_17, x_44);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_28);
if (x_47 == 0)
{
return x_28;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_28, 0);
x_49 = lean_ctor_get(x_28, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_28);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
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
x_121 = !lean_is_exclusive(x_19);
if (x_121 == 0)
{
return x_19;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_19, 0);
x_123 = lean_ctor_get(x_19, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_19);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_expr_instantiate1(x_1, x_2);
x_20 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_19, x_14, x_15, x_16, x_17, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Expr_hasBinderNameHint(x_2);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = l_Lean_MVarId_rewrite___lambda__15(x_3, x_4, x_1, x_5, x_6, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_21, x_14, x_15, x_16, x_17, x_22);
return x_24;
}
else
{
lean_object* x_25; 
lean_inc(x_17);
lean_inc(x_16);
x_25 = l_Lean_Expr_resolveBinderNameHint(x_21, x_16, x_17, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_MVarId_rewrite___lambda__15(x_3, x_4, x_1, x_5, x_6, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_26, x_14, x_15, x_16, x_17, x_27);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
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
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_1, x_14, x_15, x_16, x_17, x_18);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 8);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_14, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_14, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_14, 4);
lean_inc(x_29);
x_30 = lean_ctor_get(x_14, 5);
lean_inc(x_30);
x_31 = lean_ctor_get(x_14, 6);
lean_inc(x_31);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint64_t x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 9);
x_34 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 10);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_ctor_set_uint8(x_20, 8, x_35);
lean_ctor_set_uint8(x_20, 9, x_36);
x_37 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_20);
x_38 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_38, 0, x_20);
lean_ctor_set(x_38, 1, x_26);
lean_ctor_set(x_38, 2, x_27);
lean_ctor_set(x_38, 3, x_28);
lean_ctor_set(x_38, 4, x_29);
lean_ctor_set(x_38, 5, x_30);
lean_ctor_set(x_38, 6, x_31);
lean_ctor_set_uint64(x_38, sizeof(void*)*7, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*7 + 8, x_25);
lean_ctor_set_uint8(x_38, sizeof(void*)*7 + 9, x_33);
lean_ctor_set_uint8(x_38, sizeof(void*)*7 + 10, x_34);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_3);
lean_inc(x_22);
x_39 = l_Lean_Meta_kabstract(x_22, x_3, x_24, x_38, x_15, x_16, x_17, x_23);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Expr_hasLooseBVars(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_40);
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_43 = l_Lean_indentExpr(x_3);
x_44 = l_Lean_MVarId_rewrite___lambda__5___closed__2;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_43);
lean_ctor_set(x_19, 0, x_44);
x_45 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_19);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_9, x_47, x_14, x_15, x_16, x_17, x_41);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
return x_48;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_48);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_free_object(x_19);
x_53 = lean_box(0);
x_54 = l_Lean_MVarId_rewrite___lambda__16(x_40, x_4, x_22, x_5, x_6, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_53, x_14, x_15, x_16, x_17, x_41);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_free_object(x_19);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_39);
if (x_55 == 0)
{
return x_39;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_39, 0);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_39);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; lean_object* x_79; uint64_t x_80; lean_object* x_81; lean_object* x_82; 
x_59 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 9);
x_60 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 10);
x_61 = lean_ctor_get_uint8(x_20, 0);
x_62 = lean_ctor_get_uint8(x_20, 1);
x_63 = lean_ctor_get_uint8(x_20, 2);
x_64 = lean_ctor_get_uint8(x_20, 3);
x_65 = lean_ctor_get_uint8(x_20, 4);
x_66 = lean_ctor_get_uint8(x_20, 5);
x_67 = lean_ctor_get_uint8(x_20, 6);
x_68 = lean_ctor_get_uint8(x_20, 7);
x_69 = lean_ctor_get_uint8(x_20, 10);
x_70 = lean_ctor_get_uint8(x_20, 11);
x_71 = lean_ctor_get_uint8(x_20, 12);
x_72 = lean_ctor_get_uint8(x_20, 13);
x_73 = lean_ctor_get_uint8(x_20, 14);
x_74 = lean_ctor_get_uint8(x_20, 15);
x_75 = lean_ctor_get_uint8(x_20, 16);
x_76 = lean_ctor_get_uint8(x_20, 17);
lean_dec(x_20);
x_77 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_78 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_79 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_79, 0, x_61);
lean_ctor_set_uint8(x_79, 1, x_62);
lean_ctor_set_uint8(x_79, 2, x_63);
lean_ctor_set_uint8(x_79, 3, x_64);
lean_ctor_set_uint8(x_79, 4, x_65);
lean_ctor_set_uint8(x_79, 5, x_66);
lean_ctor_set_uint8(x_79, 6, x_67);
lean_ctor_set_uint8(x_79, 7, x_68);
lean_ctor_set_uint8(x_79, 8, x_77);
lean_ctor_set_uint8(x_79, 9, x_78);
lean_ctor_set_uint8(x_79, 10, x_69);
lean_ctor_set_uint8(x_79, 11, x_70);
lean_ctor_set_uint8(x_79, 12, x_71);
lean_ctor_set_uint8(x_79, 13, x_72);
lean_ctor_set_uint8(x_79, 14, x_73);
lean_ctor_set_uint8(x_79, 15, x_74);
lean_ctor_set_uint8(x_79, 16, x_75);
lean_ctor_set_uint8(x_79, 17, x_76);
x_80 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_79);
x_81 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_26);
lean_ctor_set(x_81, 2, x_27);
lean_ctor_set(x_81, 3, x_28);
lean_ctor_set(x_81, 4, x_29);
lean_ctor_set(x_81, 5, x_30);
lean_ctor_set(x_81, 6, x_31);
lean_ctor_set_uint64(x_81, sizeof(void*)*7, x_80);
lean_ctor_set_uint8(x_81, sizeof(void*)*7 + 8, x_25);
lean_ctor_set_uint8(x_81, sizeof(void*)*7 + 9, x_59);
lean_ctor_set_uint8(x_81, sizeof(void*)*7 + 10, x_60);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_3);
lean_inc(x_22);
x_82 = l_Lean_Meta_kabstract(x_22, x_3, x_24, x_81, x_15, x_16, x_17, x_23);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Expr_hasLooseBVars(x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_83);
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_86 = l_Lean_indentExpr(x_3);
x_87 = l_Lean_MVarId_rewrite___lambda__5___closed__2;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_86);
lean_ctor_set(x_19, 0, x_87);
x_88 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_19);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_9, x_90, x_14, x_15, x_16, x_17, x_84);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
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
else
{
lean_object* x_96; lean_object* x_97; 
lean_free_object(x_19);
x_96 = lean_box(0);
x_97 = l_Lean_MVarId_rewrite___lambda__16(x_83, x_4, x_22, x_5, x_6, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_96, x_14, x_15, x_16, x_17, x_84);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_free_object(x_19);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_98 = lean_ctor_get(x_82, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_82, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_100 = x_82;
} else {
 lean_dec_ref(x_82);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; lean_object* x_130; uint8_t x_131; uint8_t x_132; lean_object* x_133; uint64_t x_134; lean_object* x_135; lean_object* x_136; 
x_102 = lean_ctor_get(x_19, 0);
x_103 = lean_ctor_get(x_19, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_19);
x_104 = lean_ctor_get(x_2, 0);
x_105 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 8);
x_106 = lean_ctor_get(x_14, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_14, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_14, 3);
lean_inc(x_108);
x_109 = lean_ctor_get(x_14, 4);
lean_inc(x_109);
x_110 = lean_ctor_get(x_14, 5);
lean_inc(x_110);
x_111 = lean_ctor_get(x_14, 6);
lean_inc(x_111);
x_112 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 9);
x_113 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 10);
x_114 = lean_ctor_get_uint8(x_20, 0);
x_115 = lean_ctor_get_uint8(x_20, 1);
x_116 = lean_ctor_get_uint8(x_20, 2);
x_117 = lean_ctor_get_uint8(x_20, 3);
x_118 = lean_ctor_get_uint8(x_20, 4);
x_119 = lean_ctor_get_uint8(x_20, 5);
x_120 = lean_ctor_get_uint8(x_20, 6);
x_121 = lean_ctor_get_uint8(x_20, 7);
x_122 = lean_ctor_get_uint8(x_20, 10);
x_123 = lean_ctor_get_uint8(x_20, 11);
x_124 = lean_ctor_get_uint8(x_20, 12);
x_125 = lean_ctor_get_uint8(x_20, 13);
x_126 = lean_ctor_get_uint8(x_20, 14);
x_127 = lean_ctor_get_uint8(x_20, 15);
x_128 = lean_ctor_get_uint8(x_20, 16);
x_129 = lean_ctor_get_uint8(x_20, 17);
if (lean_is_exclusive(x_20)) {
 x_130 = x_20;
} else {
 lean_dec_ref(x_20);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_132 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (lean_is_scalar(x_130)) {
 x_133 = lean_alloc_ctor(0, 0, 18);
} else {
 x_133 = x_130;
}
lean_ctor_set_uint8(x_133, 0, x_114);
lean_ctor_set_uint8(x_133, 1, x_115);
lean_ctor_set_uint8(x_133, 2, x_116);
lean_ctor_set_uint8(x_133, 3, x_117);
lean_ctor_set_uint8(x_133, 4, x_118);
lean_ctor_set_uint8(x_133, 5, x_119);
lean_ctor_set_uint8(x_133, 6, x_120);
lean_ctor_set_uint8(x_133, 7, x_121);
lean_ctor_set_uint8(x_133, 8, x_131);
lean_ctor_set_uint8(x_133, 9, x_132);
lean_ctor_set_uint8(x_133, 10, x_122);
lean_ctor_set_uint8(x_133, 11, x_123);
lean_ctor_set_uint8(x_133, 12, x_124);
lean_ctor_set_uint8(x_133, 13, x_125);
lean_ctor_set_uint8(x_133, 14, x_126);
lean_ctor_set_uint8(x_133, 15, x_127);
lean_ctor_set_uint8(x_133, 16, x_128);
lean_ctor_set_uint8(x_133, 17, x_129);
x_134 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_133);
x_135 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_106);
lean_ctor_set(x_135, 2, x_107);
lean_ctor_set(x_135, 3, x_108);
lean_ctor_set(x_135, 4, x_109);
lean_ctor_set(x_135, 5, x_110);
lean_ctor_set(x_135, 6, x_111);
lean_ctor_set_uint64(x_135, sizeof(void*)*7, x_134);
lean_ctor_set_uint8(x_135, sizeof(void*)*7 + 8, x_105);
lean_ctor_set_uint8(x_135, sizeof(void*)*7 + 9, x_112);
lean_ctor_set_uint8(x_135, sizeof(void*)*7 + 10, x_113);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_3);
lean_inc(x_102);
x_136 = l_Lean_Meta_kabstract(x_102, x_3, x_104, x_135, x_15, x_16, x_17, x_103);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = l_Lean_Expr_hasLooseBVars(x_137);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_137);
lean_dec(x_102);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_140 = l_Lean_indentExpr(x_3);
x_141 = l_Lean_MVarId_rewrite___lambda__5___closed__2;
x_142 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
x_143 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
x_146 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_9, x_145, x_14, x_15, x_16, x_17, x_138);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_149 = x_146;
} else {
 lean_dec_ref(x_146);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_box(0);
x_152 = l_Lean_MVarId_rewrite___lambda__16(x_137, x_4, x_102, x_5, x_6, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_151, x_14, x_15, x_16, x_17, x_138);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_102);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_153 = lean_ctor_get(x_136, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_136, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_155 = x_136;
} else {
 lean_dec_ref(x_136);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__18___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Iff", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__18___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_rewrite___lambda__18___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__18___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("equality or iff proof expected", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__18___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lambda__18___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__18___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pattern is a metavariable", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__18___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lambda__18___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__18___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nfrom equation", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__18___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lambda__18___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__18___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("propext", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__18___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_rewrite___lambda__18___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__18___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_rewrite___lambda__18___closed__10;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_14 = lean_infer_type(x_3, x_7, x_8, x_9, x_10, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_15, x_7, x_8, x_9, x_10, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = 1;
x_22 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_23 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_18, x_21, x_20, x_22, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_3);
x_33 = l_Lean_mkAppN(x_3, x_28);
x_34 = l_Lean_MVarId_rewrite___lambda__18___closed__2;
x_35 = lean_unsigned_to_nat(2u);
x_36 = l_Lean_Expr_isAppOfArity(x_32, x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_32);
x_37 = l_Lean_Meta_matchEq_x3f(x_32, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_indentExpr(x_32);
x_41 = l_Lean_MVarId_rewrite___lambda__18___closed__4;
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_40);
lean_ctor_set(x_25, 0, x_41);
x_42 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_42);
lean_ctor_set(x_24, 0, x_25);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_24);
x_44 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_43, x_7, x_8, x_9, x_10, x_39);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_44;
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_38, 0);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (x_4 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_37, 1);
lean_inc(x_48);
lean_dec(x_37);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get(x_46, 1);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_47, 0);
x_54 = lean_ctor_get(x_47, 1);
x_55 = l_Lean_Expr_getAppFn(x_53);
x_56 = l_Lean_Expr_isMVar(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_free_object(x_47);
lean_free_object(x_46);
lean_free_object(x_38);
lean_free_object(x_25);
lean_dec(x_32);
lean_free_object(x_24);
x_57 = lean_box(0);
x_58 = l_Lean_MVarId_rewrite___lambda__5(x_5, x_6, x_53, x_54, x_50, x_33, x_2, x_1, x_28, x_31, x_3, x_57, x_7, x_8, x_9, x_10, x_48);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
x_59 = l_Lean_indentExpr(x_53);
x_60 = l_Lean_MVarId_rewrite___lambda__18___closed__6;
lean_ctor_set_tag(x_47, 7);
lean_ctor_set(x_47, 1, x_59);
lean_ctor_set(x_47, 0, x_60);
x_61 = l_Lean_MVarId_rewrite___lambda__18___closed__8;
lean_ctor_set_tag(x_46, 7);
lean_ctor_set(x_46, 1, x_61);
lean_ctor_set(x_46, 0, x_47);
x_62 = l_Lean_indentExpr(x_32);
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_62);
lean_ctor_set(x_25, 0, x_46);
x_63 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_63);
lean_ctor_set(x_24, 0, x_25);
lean_ctor_set(x_38, 0, x_24);
x_64 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_38, x_7, x_8, x_9, x_10, x_48);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
return x_64;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_64);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_47, 0);
x_70 = lean_ctor_get(x_47, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_47);
x_71 = l_Lean_Expr_getAppFn(x_69);
x_72 = l_Lean_Expr_isMVar(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_free_object(x_46);
lean_free_object(x_38);
lean_free_object(x_25);
lean_dec(x_32);
lean_free_object(x_24);
x_73 = lean_box(0);
x_74 = l_Lean_MVarId_rewrite___lambda__5(x_5, x_6, x_69, x_70, x_50, x_33, x_2, x_1, x_28, x_31, x_3, x_73, x_7, x_8, x_9, x_10, x_48);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_70);
lean_dec(x_50);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
x_75 = l_Lean_indentExpr(x_69);
x_76 = l_Lean_MVarId_rewrite___lambda__18___closed__6;
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lean_MVarId_rewrite___lambda__18___closed__8;
lean_ctor_set_tag(x_46, 7);
lean_ctor_set(x_46, 1, x_78);
lean_ctor_set(x_46, 0, x_77);
x_79 = l_Lean_indentExpr(x_32);
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_79);
lean_ctor_set(x_25, 0, x_46);
x_80 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_80);
lean_ctor_set(x_24, 0, x_25);
lean_ctor_set(x_38, 0, x_24);
x_81 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_38, x_7, x_8, x_9, x_10, x_48);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_86 = lean_ctor_get(x_46, 0);
lean_inc(x_86);
lean_dec(x_46);
x_87 = lean_ctor_get(x_47, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_47, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_89 = x_47;
} else {
 lean_dec_ref(x_47);
 x_89 = lean_box(0);
}
x_90 = l_Lean_Expr_getAppFn(x_87);
x_91 = l_Lean_Expr_isMVar(x_90);
lean_dec(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_89);
lean_free_object(x_38);
lean_free_object(x_25);
lean_dec(x_32);
lean_free_object(x_24);
x_92 = lean_box(0);
x_93 = l_Lean_MVarId_rewrite___lambda__5(x_5, x_6, x_87, x_88, x_86, x_33, x_2, x_1, x_28, x_31, x_3, x_92, x_7, x_8, x_9, x_10, x_48);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
x_94 = l_Lean_indentExpr(x_87);
x_95 = l_Lean_MVarId_rewrite___lambda__18___closed__6;
if (lean_is_scalar(x_89)) {
 x_96 = lean_alloc_ctor(7, 2, 0);
} else {
 x_96 = x_89;
 lean_ctor_set_tag(x_96, 7);
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = l_Lean_MVarId_rewrite___lambda__18___closed__8;
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_indentExpr(x_32);
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_99);
lean_ctor_set(x_25, 0, x_98);
x_100 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_100);
lean_ctor_set(x_24, 0, x_25);
lean_ctor_set(x_38, 0, x_24);
x_101 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_38, x_7, x_8, x_9, x_10, x_48);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
else
{
lean_object* x_106; uint8_t x_107; 
lean_dec(x_32);
x_106 = lean_ctor_get(x_37, 1);
lean_inc(x_106);
lean_dec(x_37);
x_107 = !lean_is_exclusive(x_46);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_108 = lean_ctor_get(x_46, 0);
x_109 = lean_ctor_get(x_46, 1);
lean_dec(x_109);
x_110 = !lean_is_exclusive(x_47);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_47, 0);
x_112 = lean_ctor_get(x_47, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_113 = l_Lean_Meta_mkEqSymm(x_33, x_7, x_8, x_9, x_10, x_106);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_111);
lean_inc(x_112);
x_116 = l_Lean_Meta_mkEq(x_112, x_111, x_7, x_8, x_9, x_10, x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l_Lean_Expr_getAppFn(x_112);
x_120 = l_Lean_Expr_isMVar(x_119);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_117);
lean_free_object(x_47);
lean_free_object(x_46);
lean_free_object(x_38);
lean_free_object(x_25);
lean_free_object(x_24);
x_121 = lean_box(0);
x_122 = l_Lean_MVarId_rewrite___lambda__9(x_5, x_6, x_112, x_111, x_108, x_114, x_2, x_1, x_28, x_31, x_3, x_121, x_7, x_8, x_9, x_10, x_118);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
lean_dec(x_114);
lean_dec(x_111);
lean_dec(x_108);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
x_123 = l_Lean_indentExpr(x_112);
x_124 = l_Lean_MVarId_rewrite___lambda__18___closed__6;
lean_ctor_set_tag(x_47, 7);
lean_ctor_set(x_47, 1, x_123);
lean_ctor_set(x_47, 0, x_124);
x_125 = l_Lean_MVarId_rewrite___lambda__18___closed__8;
lean_ctor_set_tag(x_46, 7);
lean_ctor_set(x_46, 1, x_125);
lean_ctor_set(x_46, 0, x_47);
x_126 = l_Lean_indentExpr(x_117);
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_126);
lean_ctor_set(x_25, 0, x_46);
x_127 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_127);
lean_ctor_set(x_24, 0, x_25);
lean_ctor_set(x_38, 0, x_24);
x_128 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_38, x_7, x_8, x_9, x_10, x_118);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
return x_128;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_128, 0);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_128);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_114);
lean_free_object(x_47);
lean_dec(x_112);
lean_dec(x_111);
lean_free_object(x_46);
lean_dec(x_108);
lean_free_object(x_38);
lean_free_object(x_25);
lean_dec(x_31);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_116);
if (x_133 == 0)
{
return x_116;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_116, 0);
x_135 = lean_ctor_get(x_116, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_116);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
uint8_t x_137; 
lean_free_object(x_47);
lean_dec(x_112);
lean_dec(x_111);
lean_free_object(x_46);
lean_dec(x_108);
lean_free_object(x_38);
lean_free_object(x_25);
lean_dec(x_31);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_113);
if (x_137 == 0)
{
return x_113;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_113, 0);
x_139 = lean_ctor_get(x_113, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_113);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_47, 0);
x_142 = lean_ctor_get(x_47, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_47);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_143 = l_Lean_Meta_mkEqSymm(x_33, x_7, x_8, x_9, x_10, x_106);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_141);
lean_inc(x_142);
x_146 = l_Lean_Meta_mkEq(x_142, x_141, x_7, x_8, x_9, x_10, x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = l_Lean_Expr_getAppFn(x_142);
x_150 = l_Lean_Expr_isMVar(x_149);
lean_dec(x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_147);
lean_free_object(x_46);
lean_free_object(x_38);
lean_free_object(x_25);
lean_free_object(x_24);
x_151 = lean_box(0);
x_152 = l_Lean_MVarId_rewrite___lambda__9(x_5, x_6, x_142, x_141, x_108, x_144, x_2, x_1, x_28, x_31, x_3, x_151, x_7, x_8, x_9, x_10, x_148);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_144);
lean_dec(x_141);
lean_dec(x_108);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
x_153 = l_Lean_indentExpr(x_142);
x_154 = l_Lean_MVarId_rewrite___lambda__18___closed__6;
x_155 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_153);
x_156 = l_Lean_MVarId_rewrite___lambda__18___closed__8;
lean_ctor_set_tag(x_46, 7);
lean_ctor_set(x_46, 1, x_156);
lean_ctor_set(x_46, 0, x_155);
x_157 = l_Lean_indentExpr(x_147);
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_157);
lean_ctor_set(x_25, 0, x_46);
x_158 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_158);
lean_ctor_set(x_24, 0, x_25);
lean_ctor_set(x_38, 0, x_24);
x_159 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_38, x_7, x_8, x_9, x_10, x_148);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_162 = x_159;
} else {
 lean_dec_ref(x_159);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_141);
lean_free_object(x_46);
lean_dec(x_108);
lean_free_object(x_38);
lean_free_object(x_25);
lean_dec(x_31);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_164 = lean_ctor_get(x_146, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_146, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_166 = x_146;
} else {
 lean_dec_ref(x_146);
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
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_142);
lean_dec(x_141);
lean_free_object(x_46);
lean_dec(x_108);
lean_free_object(x_38);
lean_free_object(x_25);
lean_dec(x_31);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_168 = lean_ctor_get(x_143, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_143, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_170 = x_143;
} else {
 lean_dec_ref(x_143);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_172 = lean_ctor_get(x_46, 0);
lean_inc(x_172);
lean_dec(x_46);
x_173 = lean_ctor_get(x_47, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_47, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_175 = x_47;
} else {
 lean_dec_ref(x_47);
 x_175 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_176 = l_Lean_Meta_mkEqSymm(x_33, x_7, x_8, x_9, x_10, x_106);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_173);
lean_inc(x_174);
x_179 = l_Lean_Meta_mkEq(x_174, x_173, x_7, x_8, x_9, x_10, x_178);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = l_Lean_Expr_getAppFn(x_174);
x_183 = l_Lean_Expr_isMVar(x_182);
lean_dec(x_182);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_180);
lean_dec(x_175);
lean_free_object(x_38);
lean_free_object(x_25);
lean_free_object(x_24);
x_184 = lean_box(0);
x_185 = l_Lean_MVarId_rewrite___lambda__9(x_5, x_6, x_174, x_173, x_172, x_177, x_2, x_1, x_28, x_31, x_3, x_184, x_7, x_8, x_9, x_10, x_181);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_177);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
x_186 = l_Lean_indentExpr(x_174);
x_187 = l_Lean_MVarId_rewrite___lambda__18___closed__6;
if (lean_is_scalar(x_175)) {
 x_188 = lean_alloc_ctor(7, 2, 0);
} else {
 x_188 = x_175;
 lean_ctor_set_tag(x_188, 7);
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_186);
x_189 = l_Lean_MVarId_rewrite___lambda__18___closed__8;
x_190 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = l_Lean_indentExpr(x_180);
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_191);
lean_ctor_set(x_25, 0, x_190);
x_192 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_192);
lean_ctor_set(x_24, 0, x_25);
lean_ctor_set(x_38, 0, x_24);
x_193 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_38, x_7, x_8, x_9, x_10, x_181);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_196 = x_193;
} else {
 lean_dec_ref(x_193);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_177);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_free_object(x_38);
lean_free_object(x_25);
lean_dec(x_31);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_198 = lean_ctor_get(x_179, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_179, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_200 = x_179;
} else {
 lean_dec_ref(x_179);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_free_object(x_38);
lean_free_object(x_25);
lean_dec(x_31);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_202 = lean_ctor_get(x_176, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_176, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_204 = x_176;
} else {
 lean_dec_ref(x_176);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
}
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_38, 0);
lean_inc(x_206);
lean_dec(x_38);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
if (x_4 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_208 = lean_ctor_get(x_37, 1);
lean_inc(x_208);
lean_dec(x_37);
x_209 = lean_ctor_get(x_206, 0);
lean_inc(x_209);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_210 = x_206;
} else {
 lean_dec_ref(x_206);
 x_210 = lean_box(0);
}
x_211 = lean_ctor_get(x_207, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_207, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_213 = x_207;
} else {
 lean_dec_ref(x_207);
 x_213 = lean_box(0);
}
x_214 = l_Lean_Expr_getAppFn(x_211);
x_215 = l_Lean_Expr_isMVar(x_214);
lean_dec(x_214);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_213);
lean_dec(x_210);
lean_free_object(x_25);
lean_dec(x_32);
lean_free_object(x_24);
x_216 = lean_box(0);
x_217 = l_Lean_MVarId_rewrite___lambda__5(x_5, x_6, x_211, x_212, x_209, x_33, x_2, x_1, x_28, x_31, x_3, x_216, x_7, x_8, x_9, x_10, x_208);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_212);
lean_dec(x_209);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
x_218 = l_Lean_indentExpr(x_211);
x_219 = l_Lean_MVarId_rewrite___lambda__18___closed__6;
if (lean_is_scalar(x_213)) {
 x_220 = lean_alloc_ctor(7, 2, 0);
} else {
 x_220 = x_213;
 lean_ctor_set_tag(x_220, 7);
}
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_218);
x_221 = l_Lean_MVarId_rewrite___lambda__18___closed__8;
if (lean_is_scalar(x_210)) {
 x_222 = lean_alloc_ctor(7, 2, 0);
} else {
 x_222 = x_210;
 lean_ctor_set_tag(x_222, 7);
}
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
x_223 = l_Lean_indentExpr(x_32);
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_223);
lean_ctor_set(x_25, 0, x_222);
x_224 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_224);
lean_ctor_set(x_24, 0, x_25);
x_225 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_225, 0, x_24);
x_226 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_225, x_7, x_8, x_9, x_10, x_208);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_229 = x_226;
} else {
 lean_dec_ref(x_226);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_32);
x_231 = lean_ctor_get(x_37, 1);
lean_inc(x_231);
lean_dec(x_37);
x_232 = lean_ctor_get(x_206, 0);
lean_inc(x_232);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_233 = x_206;
} else {
 lean_dec_ref(x_206);
 x_233 = lean_box(0);
}
x_234 = lean_ctor_get(x_207, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_207, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_236 = x_207;
} else {
 lean_dec_ref(x_207);
 x_236 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_237 = l_Lean_Meta_mkEqSymm(x_33, x_7, x_8, x_9, x_10, x_231);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_234);
lean_inc(x_235);
x_240 = l_Lean_Meta_mkEq(x_235, x_234, x_7, x_8, x_9, x_10, x_239);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
x_243 = l_Lean_Expr_getAppFn(x_235);
x_244 = l_Lean_Expr_isMVar(x_243);
lean_dec(x_243);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; 
lean_dec(x_241);
lean_dec(x_236);
lean_dec(x_233);
lean_free_object(x_25);
lean_free_object(x_24);
x_245 = lean_box(0);
x_246 = l_Lean_MVarId_rewrite___lambda__9(x_5, x_6, x_235, x_234, x_232, x_238, x_2, x_1, x_28, x_31, x_3, x_245, x_7, x_8, x_9, x_10, x_242);
return x_246;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_238);
lean_dec(x_234);
lean_dec(x_232);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
x_247 = l_Lean_indentExpr(x_235);
x_248 = l_Lean_MVarId_rewrite___lambda__18___closed__6;
if (lean_is_scalar(x_236)) {
 x_249 = lean_alloc_ctor(7, 2, 0);
} else {
 x_249 = x_236;
 lean_ctor_set_tag(x_249, 7);
}
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_247);
x_250 = l_Lean_MVarId_rewrite___lambda__18___closed__8;
if (lean_is_scalar(x_233)) {
 x_251 = lean_alloc_ctor(7, 2, 0);
} else {
 x_251 = x_233;
 lean_ctor_set_tag(x_251, 7);
}
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
x_252 = l_Lean_indentExpr(x_241);
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_252);
lean_ctor_set(x_25, 0, x_251);
x_253 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_253);
lean_ctor_set(x_24, 0, x_25);
x_254 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_254, 0, x_24);
x_255 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_254, x_7, x_8, x_9, x_10, x_242);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_258 = x_255;
} else {
 lean_dec_ref(x_255);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(1, 2, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_238);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_free_object(x_25);
lean_dec(x_31);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_260 = lean_ctor_get(x_240, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_240, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_262 = x_240;
} else {
 lean_dec_ref(x_240);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_free_object(x_25);
lean_dec(x_31);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_264 = lean_ctor_get(x_237, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_237, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_266 = x_237;
} else {
 lean_dec_ref(x_237);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
}
}
}
else
{
uint8_t x_268; 
lean_dec(x_33);
lean_free_object(x_25);
lean_dec(x_32);
lean_dec(x_31);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_268 = !lean_is_exclusive(x_37);
if (x_268 == 0)
{
return x_37;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_37, 0);
x_270 = lean_ctor_get(x_37, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_37);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
return x_271;
}
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_272 = l_Lean_Expr_appFn_x21(x_32);
x_273 = l_Lean_Expr_appArg_x21(x_272);
lean_dec(x_272);
x_274 = l_Lean_Expr_appArg_x21(x_32);
lean_dec(x_32);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_274);
lean_inc(x_273);
x_275 = l_Lean_Meta_mkEq(x_273, x_274, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec(x_275);
x_278 = lean_box(0);
x_279 = l_Lean_MVarId_rewrite___lambda__18___closed__11;
x_280 = l_Lean_mkApp3(x_279, x_273, x_274, x_33);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_276);
x_281 = l_Lean_Meta_matchEq_x3f(x_276, x_7, x_8, x_9, x_10, x_277);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_280);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_284 = l_Lean_indentExpr(x_276);
x_285 = l_Lean_MVarId_rewrite___lambda__18___closed__4;
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_284);
lean_ctor_set(x_25, 0, x_285);
x_286 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_286);
lean_ctor_set(x_24, 0, x_25);
x_287 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_287, 0, x_24);
x_288 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_287, x_7, x_8, x_9, x_10, x_283);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_288;
}
else
{
uint8_t x_289; 
x_289 = !lean_is_exclusive(x_282);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_282, 0);
x_291 = lean_ctor_get(x_290, 1);
lean_inc(x_291);
if (x_4 == 0)
{
lean_object* x_292; uint8_t x_293; 
x_292 = lean_ctor_get(x_281, 1);
lean_inc(x_292);
lean_dec(x_281);
x_293 = !lean_is_exclusive(x_290);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; 
x_294 = lean_ctor_get(x_290, 0);
x_295 = lean_ctor_get(x_290, 1);
lean_dec(x_295);
x_296 = !lean_is_exclusive(x_291);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; 
x_297 = lean_ctor_get(x_291, 0);
x_298 = lean_ctor_get(x_291, 1);
x_299 = l_Lean_Expr_getAppFn(x_297);
x_300 = l_Lean_Expr_isMVar(x_299);
lean_dec(x_299);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; 
lean_free_object(x_291);
lean_free_object(x_290);
lean_free_object(x_282);
lean_dec(x_276);
lean_free_object(x_25);
lean_free_object(x_24);
x_301 = lean_box(0);
x_302 = l_Lean_MVarId_rewrite___lambda__13(x_5, x_6, x_297, x_298, x_294, x_278, x_280, x_2, x_1, x_28, x_31, x_3, x_301, x_7, x_8, x_9, x_10, x_292);
return x_302;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
lean_dec(x_298);
lean_dec(x_294);
lean_dec(x_280);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
x_303 = l_Lean_indentExpr(x_297);
x_304 = l_Lean_MVarId_rewrite___lambda__18___closed__6;
lean_ctor_set_tag(x_291, 7);
lean_ctor_set(x_291, 1, x_303);
lean_ctor_set(x_291, 0, x_304);
x_305 = l_Lean_MVarId_rewrite___lambda__18___closed__8;
lean_ctor_set_tag(x_290, 7);
lean_ctor_set(x_290, 1, x_305);
lean_ctor_set(x_290, 0, x_291);
x_306 = l_Lean_indentExpr(x_276);
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_306);
lean_ctor_set(x_25, 0, x_290);
x_307 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_307);
lean_ctor_set(x_24, 0, x_25);
lean_ctor_set(x_282, 0, x_24);
x_308 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_282, x_7, x_8, x_9, x_10, x_292);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_309 = !lean_is_exclusive(x_308);
if (x_309 == 0)
{
return x_308;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_ctor_get(x_308, 0);
x_311 = lean_ctor_get(x_308, 1);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_308);
x_312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
return x_312;
}
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_313 = lean_ctor_get(x_291, 0);
x_314 = lean_ctor_get(x_291, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_291);
x_315 = l_Lean_Expr_getAppFn(x_313);
x_316 = l_Lean_Expr_isMVar(x_315);
lean_dec(x_315);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; 
lean_free_object(x_290);
lean_free_object(x_282);
lean_dec(x_276);
lean_free_object(x_25);
lean_free_object(x_24);
x_317 = lean_box(0);
x_318 = l_Lean_MVarId_rewrite___lambda__13(x_5, x_6, x_313, x_314, x_294, x_278, x_280, x_2, x_1, x_28, x_31, x_3, x_317, x_7, x_8, x_9, x_10, x_292);
return x_318;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_314);
lean_dec(x_294);
lean_dec(x_280);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
x_319 = l_Lean_indentExpr(x_313);
x_320 = l_Lean_MVarId_rewrite___lambda__18___closed__6;
x_321 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_319);
x_322 = l_Lean_MVarId_rewrite___lambda__18___closed__8;
lean_ctor_set_tag(x_290, 7);
lean_ctor_set(x_290, 1, x_322);
lean_ctor_set(x_290, 0, x_321);
x_323 = l_Lean_indentExpr(x_276);
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_323);
lean_ctor_set(x_25, 0, x_290);
x_324 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_324);
lean_ctor_set(x_24, 0, x_25);
lean_ctor_set(x_282, 0, x_24);
x_325 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_282, x_7, x_8, x_9, x_10, x_292);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_328 = x_325;
} else {
 lean_dec_ref(x_325);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(1, 2, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_326);
lean_ctor_set(x_329, 1, x_327);
return x_329;
}
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; 
x_330 = lean_ctor_get(x_290, 0);
lean_inc(x_330);
lean_dec(x_290);
x_331 = lean_ctor_get(x_291, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_291, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_333 = x_291;
} else {
 lean_dec_ref(x_291);
 x_333 = lean_box(0);
}
x_334 = l_Lean_Expr_getAppFn(x_331);
x_335 = l_Lean_Expr_isMVar(x_334);
lean_dec(x_334);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; 
lean_dec(x_333);
lean_free_object(x_282);
lean_dec(x_276);
lean_free_object(x_25);
lean_free_object(x_24);
x_336 = lean_box(0);
x_337 = l_Lean_MVarId_rewrite___lambda__13(x_5, x_6, x_331, x_332, x_330, x_278, x_280, x_2, x_1, x_28, x_31, x_3, x_336, x_7, x_8, x_9, x_10, x_292);
return x_337;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
lean_dec(x_332);
lean_dec(x_330);
lean_dec(x_280);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
x_338 = l_Lean_indentExpr(x_331);
x_339 = l_Lean_MVarId_rewrite___lambda__18___closed__6;
if (lean_is_scalar(x_333)) {
 x_340 = lean_alloc_ctor(7, 2, 0);
} else {
 x_340 = x_333;
 lean_ctor_set_tag(x_340, 7);
}
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_338);
x_341 = l_Lean_MVarId_rewrite___lambda__18___closed__8;
x_342 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
x_343 = l_Lean_indentExpr(x_276);
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_343);
lean_ctor_set(x_25, 0, x_342);
x_344 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_344);
lean_ctor_set(x_24, 0, x_25);
lean_ctor_set(x_282, 0, x_24);
x_345 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_282, x_7, x_8, x_9, x_10, x_292);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_348 = x_345;
} else {
 lean_dec_ref(x_345);
 x_348 = lean_box(0);
}
if (lean_is_scalar(x_348)) {
 x_349 = lean_alloc_ctor(1, 2, 0);
} else {
 x_349 = x_348;
}
lean_ctor_set(x_349, 0, x_346);
lean_ctor_set(x_349, 1, x_347);
return x_349;
}
}
}
else
{
lean_object* x_350; uint8_t x_351; 
lean_dec(x_276);
x_350 = lean_ctor_get(x_281, 1);
lean_inc(x_350);
lean_dec(x_281);
x_351 = !lean_is_exclusive(x_290);
if (x_351 == 0)
{
lean_object* x_352; lean_object* x_353; uint8_t x_354; 
x_352 = lean_ctor_get(x_290, 0);
x_353 = lean_ctor_get(x_290, 1);
lean_dec(x_353);
x_354 = !lean_is_exclusive(x_291);
if (x_354 == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_355 = lean_ctor_get(x_291, 0);
x_356 = lean_ctor_get(x_291, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_357 = l_Lean_Meta_mkEqSymm(x_280, x_7, x_8, x_9, x_10, x_350);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
lean_dec(x_357);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_355);
lean_inc(x_356);
x_360 = l_Lean_Meta_mkEq(x_356, x_355, x_7, x_8, x_9, x_10, x_359);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
x_363 = l_Lean_Expr_getAppFn(x_356);
x_364 = l_Lean_Expr_isMVar(x_363);
lean_dec(x_363);
if (x_364 == 0)
{
lean_object* x_365; lean_object* x_366; 
lean_dec(x_361);
lean_free_object(x_291);
lean_free_object(x_290);
lean_free_object(x_282);
lean_free_object(x_25);
lean_free_object(x_24);
x_365 = lean_box(0);
x_366 = l_Lean_MVarId_rewrite___lambda__17(x_5, x_6, x_356, x_355, x_352, x_278, x_358, x_2, x_1, x_28, x_31, x_3, x_365, x_7, x_8, x_9, x_10, x_362);
return x_366;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; 
lean_dec(x_358);
lean_dec(x_355);
lean_dec(x_352);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
x_367 = l_Lean_indentExpr(x_356);
x_368 = l_Lean_MVarId_rewrite___lambda__18___closed__6;
lean_ctor_set_tag(x_291, 7);
lean_ctor_set(x_291, 1, x_367);
lean_ctor_set(x_291, 0, x_368);
x_369 = l_Lean_MVarId_rewrite___lambda__18___closed__8;
lean_ctor_set_tag(x_290, 7);
lean_ctor_set(x_290, 1, x_369);
lean_ctor_set(x_290, 0, x_291);
x_370 = l_Lean_indentExpr(x_361);
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_370);
lean_ctor_set(x_25, 0, x_290);
x_371 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_371);
lean_ctor_set(x_24, 0, x_25);
lean_ctor_set(x_282, 0, x_24);
x_372 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_282, x_7, x_8, x_9, x_10, x_362);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_373 = !lean_is_exclusive(x_372);
if (x_373 == 0)
{
return x_372;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_374 = lean_ctor_get(x_372, 0);
x_375 = lean_ctor_get(x_372, 1);
lean_inc(x_375);
lean_inc(x_374);
lean_dec(x_372);
x_376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_376, 0, x_374);
lean_ctor_set(x_376, 1, x_375);
return x_376;
}
}
}
else
{
uint8_t x_377; 
lean_dec(x_358);
lean_free_object(x_291);
lean_dec(x_356);
lean_dec(x_355);
lean_free_object(x_290);
lean_dec(x_352);
lean_free_object(x_282);
lean_free_object(x_25);
lean_dec(x_31);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_377 = !lean_is_exclusive(x_360);
if (x_377 == 0)
{
return x_360;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_ctor_get(x_360, 0);
x_379 = lean_ctor_get(x_360, 1);
lean_inc(x_379);
lean_inc(x_378);
lean_dec(x_360);
x_380 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_379);
return x_380;
}
}
}
else
{
uint8_t x_381; 
lean_free_object(x_291);
lean_dec(x_356);
lean_dec(x_355);
lean_free_object(x_290);
lean_dec(x_352);
lean_free_object(x_282);
lean_free_object(x_25);
lean_dec(x_31);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_381 = !lean_is_exclusive(x_357);
if (x_381 == 0)
{
return x_357;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_357, 0);
x_383 = lean_ctor_get(x_357, 1);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_357);
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
return x_384;
}
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_385 = lean_ctor_get(x_291, 0);
x_386 = lean_ctor_get(x_291, 1);
lean_inc(x_386);
lean_inc(x_385);
lean_dec(x_291);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_387 = l_Lean_Meta_mkEqSymm(x_280, x_7, x_8, x_9, x_10, x_350);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
lean_dec(x_387);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_385);
lean_inc(x_386);
x_390 = l_Lean_Meta_mkEq(x_386, x_385, x_7, x_8, x_9, x_10, x_389);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec(x_390);
x_393 = l_Lean_Expr_getAppFn(x_386);
x_394 = l_Lean_Expr_isMVar(x_393);
lean_dec(x_393);
if (x_394 == 0)
{
lean_object* x_395; lean_object* x_396; 
lean_dec(x_391);
lean_free_object(x_290);
lean_free_object(x_282);
lean_free_object(x_25);
lean_free_object(x_24);
x_395 = lean_box(0);
x_396 = l_Lean_MVarId_rewrite___lambda__17(x_5, x_6, x_386, x_385, x_352, x_278, x_388, x_2, x_1, x_28, x_31, x_3, x_395, x_7, x_8, x_9, x_10, x_392);
return x_396;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
lean_dec(x_388);
lean_dec(x_385);
lean_dec(x_352);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
x_397 = l_Lean_indentExpr(x_386);
x_398 = l_Lean_MVarId_rewrite___lambda__18___closed__6;
x_399 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_399, 0, x_398);
lean_ctor_set(x_399, 1, x_397);
x_400 = l_Lean_MVarId_rewrite___lambda__18___closed__8;
lean_ctor_set_tag(x_290, 7);
lean_ctor_set(x_290, 1, x_400);
lean_ctor_set(x_290, 0, x_399);
x_401 = l_Lean_indentExpr(x_391);
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_401);
lean_ctor_set(x_25, 0, x_290);
x_402 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_402);
lean_ctor_set(x_24, 0, x_25);
lean_ctor_set(x_282, 0, x_24);
x_403 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_282, x_7, x_8, x_9, x_10, x_392);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 x_406 = x_403;
} else {
 lean_dec_ref(x_403);
 x_406 = lean_box(0);
}
if (lean_is_scalar(x_406)) {
 x_407 = lean_alloc_ctor(1, 2, 0);
} else {
 x_407 = x_406;
}
lean_ctor_set(x_407, 0, x_404);
lean_ctor_set(x_407, 1, x_405);
return x_407;
}
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_388);
lean_dec(x_386);
lean_dec(x_385);
lean_free_object(x_290);
lean_dec(x_352);
lean_free_object(x_282);
lean_free_object(x_25);
lean_dec(x_31);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_408 = lean_ctor_get(x_390, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_390, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 x_410 = x_390;
} else {
 lean_dec_ref(x_390);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_410)) {
 x_411 = lean_alloc_ctor(1, 2, 0);
} else {
 x_411 = x_410;
}
lean_ctor_set(x_411, 0, x_408);
lean_ctor_set(x_411, 1, x_409);
return x_411;
}
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
lean_dec(x_386);
lean_dec(x_385);
lean_free_object(x_290);
lean_dec(x_352);
lean_free_object(x_282);
lean_free_object(x_25);
lean_dec(x_31);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_412 = lean_ctor_get(x_387, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_387, 1);
lean_inc(x_413);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_414 = x_387;
} else {
 lean_dec_ref(x_387);
 x_414 = lean_box(0);
}
if (lean_is_scalar(x_414)) {
 x_415 = lean_alloc_ctor(1, 2, 0);
} else {
 x_415 = x_414;
}
lean_ctor_set(x_415, 0, x_412);
lean_ctor_set(x_415, 1, x_413);
return x_415;
}
}
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_416 = lean_ctor_get(x_290, 0);
lean_inc(x_416);
lean_dec(x_290);
x_417 = lean_ctor_get(x_291, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_291, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_419 = x_291;
} else {
 lean_dec_ref(x_291);
 x_419 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_420 = l_Lean_Meta_mkEqSymm(x_280, x_7, x_8, x_9, x_10, x_350);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_417);
lean_inc(x_418);
x_423 = l_Lean_Meta_mkEq(x_418, x_417, x_7, x_8, x_9, x_10, x_422);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; 
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_423, 1);
lean_inc(x_425);
lean_dec(x_423);
x_426 = l_Lean_Expr_getAppFn(x_418);
x_427 = l_Lean_Expr_isMVar(x_426);
lean_dec(x_426);
if (x_427 == 0)
{
lean_object* x_428; lean_object* x_429; 
lean_dec(x_424);
lean_dec(x_419);
lean_free_object(x_282);
lean_free_object(x_25);
lean_free_object(x_24);
x_428 = lean_box(0);
x_429 = l_Lean_MVarId_rewrite___lambda__17(x_5, x_6, x_418, x_417, x_416, x_278, x_421, x_2, x_1, x_28, x_31, x_3, x_428, x_7, x_8, x_9, x_10, x_425);
return x_429;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_421);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
x_430 = l_Lean_indentExpr(x_418);
x_431 = l_Lean_MVarId_rewrite___lambda__18___closed__6;
if (lean_is_scalar(x_419)) {
 x_432 = lean_alloc_ctor(7, 2, 0);
} else {
 x_432 = x_419;
 lean_ctor_set_tag(x_432, 7);
}
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_430);
x_433 = l_Lean_MVarId_rewrite___lambda__18___closed__8;
x_434 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_434, 0, x_432);
lean_ctor_set(x_434, 1, x_433);
x_435 = l_Lean_indentExpr(x_424);
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_435);
lean_ctor_set(x_25, 0, x_434);
x_436 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_436);
lean_ctor_set(x_24, 0, x_25);
lean_ctor_set(x_282, 0, x_24);
x_437 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_282, x_7, x_8, x_9, x_10, x_425);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_437, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 lean_ctor_release(x_437, 1);
 x_440 = x_437;
} else {
 lean_dec_ref(x_437);
 x_440 = lean_box(0);
}
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(1, 2, 0);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_438);
lean_ctor_set(x_441, 1, x_439);
return x_441;
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_421);
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_free_object(x_282);
lean_free_object(x_25);
lean_dec(x_31);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_442 = lean_ctor_get(x_423, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_423, 1);
lean_inc(x_443);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 x_444 = x_423;
} else {
 lean_dec_ref(x_423);
 x_444 = lean_box(0);
}
if (lean_is_scalar(x_444)) {
 x_445 = lean_alloc_ctor(1, 2, 0);
} else {
 x_445 = x_444;
}
lean_ctor_set(x_445, 0, x_442);
lean_ctor_set(x_445, 1, x_443);
return x_445;
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_free_object(x_282);
lean_free_object(x_25);
lean_dec(x_31);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_446 = lean_ctor_get(x_420, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_420, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 x_448 = x_420;
} else {
 lean_dec_ref(x_420);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(1, 2, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_446);
lean_ctor_set(x_449, 1, x_447);
return x_449;
}
}
}
}
else
{
lean_object* x_450; lean_object* x_451; 
x_450 = lean_ctor_get(x_282, 0);
lean_inc(x_450);
lean_dec(x_282);
x_451 = lean_ctor_get(x_450, 1);
lean_inc(x_451);
if (x_4 == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; 
x_452 = lean_ctor_get(x_281, 1);
lean_inc(x_452);
lean_dec(x_281);
x_453 = lean_ctor_get(x_450, 0);
lean_inc(x_453);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_454 = x_450;
} else {
 lean_dec_ref(x_450);
 x_454 = lean_box(0);
}
x_455 = lean_ctor_get(x_451, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_451, 1);
lean_inc(x_456);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 x_457 = x_451;
} else {
 lean_dec_ref(x_451);
 x_457 = lean_box(0);
}
x_458 = l_Lean_Expr_getAppFn(x_455);
x_459 = l_Lean_Expr_isMVar(x_458);
lean_dec(x_458);
if (x_459 == 0)
{
lean_object* x_460; lean_object* x_461; 
lean_dec(x_457);
lean_dec(x_454);
lean_dec(x_276);
lean_free_object(x_25);
lean_free_object(x_24);
x_460 = lean_box(0);
x_461 = l_Lean_MVarId_rewrite___lambda__13(x_5, x_6, x_455, x_456, x_453, x_278, x_280, x_2, x_1, x_28, x_31, x_3, x_460, x_7, x_8, x_9, x_10, x_452);
return x_461;
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec(x_456);
lean_dec(x_453);
lean_dec(x_280);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
x_462 = l_Lean_indentExpr(x_455);
x_463 = l_Lean_MVarId_rewrite___lambda__18___closed__6;
if (lean_is_scalar(x_457)) {
 x_464 = lean_alloc_ctor(7, 2, 0);
} else {
 x_464 = x_457;
 lean_ctor_set_tag(x_464, 7);
}
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_462);
x_465 = l_Lean_MVarId_rewrite___lambda__18___closed__8;
if (lean_is_scalar(x_454)) {
 x_466 = lean_alloc_ctor(7, 2, 0);
} else {
 x_466 = x_454;
 lean_ctor_set_tag(x_466, 7);
}
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
x_467 = l_Lean_indentExpr(x_276);
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_467);
lean_ctor_set(x_25, 0, x_466);
x_468 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_468);
lean_ctor_set(x_24, 0, x_25);
x_469 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_469, 0, x_24);
x_470 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_469, x_7, x_8, x_9, x_10, x_452);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_473 = x_470;
} else {
 lean_dec_ref(x_470);
 x_473 = lean_box(0);
}
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(1, 2, 0);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_471);
lean_ctor_set(x_474, 1, x_472);
return x_474;
}
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
lean_dec(x_276);
x_475 = lean_ctor_get(x_281, 1);
lean_inc(x_475);
lean_dec(x_281);
x_476 = lean_ctor_get(x_450, 0);
lean_inc(x_476);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_477 = x_450;
} else {
 lean_dec_ref(x_450);
 x_477 = lean_box(0);
}
x_478 = lean_ctor_get(x_451, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_451, 1);
lean_inc(x_479);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 x_480 = x_451;
} else {
 lean_dec_ref(x_451);
 x_480 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_481 = l_Lean_Meta_mkEqSymm(x_280, x_7, x_8, x_9, x_10, x_475);
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_481, 1);
lean_inc(x_483);
lean_dec(x_481);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_478);
lean_inc(x_479);
x_484 = l_Lean_Meta_mkEq(x_479, x_478, x_7, x_8, x_9, x_10, x_483);
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; uint8_t x_488; 
x_485 = lean_ctor_get(x_484, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_484, 1);
lean_inc(x_486);
lean_dec(x_484);
x_487 = l_Lean_Expr_getAppFn(x_479);
x_488 = l_Lean_Expr_isMVar(x_487);
lean_dec(x_487);
if (x_488 == 0)
{
lean_object* x_489; lean_object* x_490; 
lean_dec(x_485);
lean_dec(x_480);
lean_dec(x_477);
lean_free_object(x_25);
lean_free_object(x_24);
x_489 = lean_box(0);
x_490 = l_Lean_MVarId_rewrite___lambda__17(x_5, x_6, x_479, x_478, x_476, x_278, x_482, x_2, x_1, x_28, x_31, x_3, x_489, x_7, x_8, x_9, x_10, x_486);
return x_490;
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
lean_dec(x_482);
lean_dec(x_478);
lean_dec(x_476);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
x_491 = l_Lean_indentExpr(x_479);
x_492 = l_Lean_MVarId_rewrite___lambda__18___closed__6;
if (lean_is_scalar(x_480)) {
 x_493 = lean_alloc_ctor(7, 2, 0);
} else {
 x_493 = x_480;
 lean_ctor_set_tag(x_493, 7);
}
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_491);
x_494 = l_Lean_MVarId_rewrite___lambda__18___closed__8;
if (lean_is_scalar(x_477)) {
 x_495 = lean_alloc_ctor(7, 2, 0);
} else {
 x_495 = x_477;
 lean_ctor_set_tag(x_495, 7);
}
lean_ctor_set(x_495, 0, x_493);
lean_ctor_set(x_495, 1, x_494);
x_496 = l_Lean_indentExpr(x_485);
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_496);
lean_ctor_set(x_25, 0, x_495);
x_497 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_497);
lean_ctor_set(x_24, 0, x_25);
x_498 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_498, 0, x_24);
x_499 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_498, x_7, x_8, x_9, x_10, x_486);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_500 = lean_ctor_get(x_499, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_499, 1);
lean_inc(x_501);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 lean_ctor_release(x_499, 1);
 x_502 = x_499;
} else {
 lean_dec_ref(x_499);
 x_502 = lean_box(0);
}
if (lean_is_scalar(x_502)) {
 x_503 = lean_alloc_ctor(1, 2, 0);
} else {
 x_503 = x_502;
}
lean_ctor_set(x_503, 0, x_500);
lean_ctor_set(x_503, 1, x_501);
return x_503;
}
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_482);
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_478);
lean_dec(x_477);
lean_dec(x_476);
lean_free_object(x_25);
lean_dec(x_31);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_504 = lean_ctor_get(x_484, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_484, 1);
lean_inc(x_505);
if (lean_is_exclusive(x_484)) {
 lean_ctor_release(x_484, 0);
 lean_ctor_release(x_484, 1);
 x_506 = x_484;
} else {
 lean_dec_ref(x_484);
 x_506 = lean_box(0);
}
if (lean_is_scalar(x_506)) {
 x_507 = lean_alloc_ctor(1, 2, 0);
} else {
 x_507 = x_506;
}
lean_ctor_set(x_507, 0, x_504);
lean_ctor_set(x_507, 1, x_505);
return x_507;
}
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_478);
lean_dec(x_477);
lean_dec(x_476);
lean_free_object(x_25);
lean_dec(x_31);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_508 = lean_ctor_get(x_481, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_481, 1);
lean_inc(x_509);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 x_510 = x_481;
} else {
 lean_dec_ref(x_481);
 x_510 = lean_box(0);
}
if (lean_is_scalar(x_510)) {
 x_511 = lean_alloc_ctor(1, 2, 0);
} else {
 x_511 = x_510;
}
lean_ctor_set(x_511, 0, x_508);
lean_ctor_set(x_511, 1, x_509);
return x_511;
}
}
}
}
}
else
{
uint8_t x_512; 
lean_dec(x_280);
lean_dec(x_276);
lean_free_object(x_25);
lean_dec(x_31);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_512 = !lean_is_exclusive(x_281);
if (x_512 == 0)
{
return x_281;
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_513 = lean_ctor_get(x_281, 0);
x_514 = lean_ctor_get(x_281, 1);
lean_inc(x_514);
lean_inc(x_513);
lean_dec(x_281);
x_515 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_515, 0, x_513);
lean_ctor_set(x_515, 1, x_514);
return x_515;
}
}
}
else
{
uint8_t x_516; 
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_33);
lean_free_object(x_25);
lean_dec(x_31);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_516 = !lean_is_exclusive(x_275);
if (x_516 == 0)
{
return x_275;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_517 = lean_ctor_get(x_275, 0);
x_518 = lean_ctor_get(x_275, 1);
lean_inc(x_518);
lean_inc(x_517);
lean_dec(x_275);
x_519 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_519, 0, x_517);
lean_ctor_set(x_519, 1, x_518);
return x_519;
}
}
}
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; uint8_t x_525; 
x_520 = lean_ctor_get(x_25, 0);
x_521 = lean_ctor_get(x_25, 1);
lean_inc(x_521);
lean_inc(x_520);
lean_dec(x_25);
lean_inc(x_3);
x_522 = l_Lean_mkAppN(x_3, x_28);
x_523 = l_Lean_MVarId_rewrite___lambda__18___closed__2;
x_524 = lean_unsigned_to_nat(2u);
x_525 = l_Lean_Expr_isAppOfArity(x_521, x_523, x_524);
if (x_525 == 0)
{
lean_object* x_526; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_521);
x_526 = l_Lean_Meta_matchEq_x3f(x_521, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_526) == 0)
{
lean_object* x_527; 
x_527 = lean_ctor_get(x_526, 0);
lean_inc(x_527);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
lean_dec(x_522);
lean_dec(x_520);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
x_528 = lean_ctor_get(x_526, 1);
lean_inc(x_528);
lean_dec(x_526);
x_529 = l_Lean_indentExpr(x_521);
x_530 = l_Lean_MVarId_rewrite___lambda__18___closed__4;
x_531 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_531, 0, x_530);
lean_ctor_set(x_531, 1, x_529);
x_532 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_532);
lean_ctor_set(x_24, 0, x_531);
x_533 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_533, 0, x_24);
x_534 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_533, x_7, x_8, x_9, x_10, x_528);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_534;
}
else
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_535 = lean_ctor_get(x_527, 0);
lean_inc(x_535);
if (lean_is_exclusive(x_527)) {
 lean_ctor_release(x_527, 0);
 x_536 = x_527;
} else {
 lean_dec_ref(x_527);
 x_536 = lean_box(0);
}
x_537 = lean_ctor_get(x_535, 1);
lean_inc(x_537);
if (x_4 == 0)
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; uint8_t x_545; 
x_538 = lean_ctor_get(x_526, 1);
lean_inc(x_538);
lean_dec(x_526);
x_539 = lean_ctor_get(x_535, 0);
lean_inc(x_539);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 lean_ctor_release(x_535, 1);
 x_540 = x_535;
} else {
 lean_dec_ref(x_535);
 x_540 = lean_box(0);
}
x_541 = lean_ctor_get(x_537, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_537, 1);
lean_inc(x_542);
if (lean_is_exclusive(x_537)) {
 lean_ctor_release(x_537, 0);
 lean_ctor_release(x_537, 1);
 x_543 = x_537;
} else {
 lean_dec_ref(x_537);
 x_543 = lean_box(0);
}
x_544 = l_Lean_Expr_getAppFn(x_541);
x_545 = l_Lean_Expr_isMVar(x_544);
lean_dec(x_544);
if (x_545 == 0)
{
lean_object* x_546; lean_object* x_547; 
lean_dec(x_543);
lean_dec(x_540);
lean_dec(x_536);
lean_dec(x_521);
lean_free_object(x_24);
x_546 = lean_box(0);
x_547 = l_Lean_MVarId_rewrite___lambda__5(x_5, x_6, x_541, x_542, x_539, x_522, x_2, x_1, x_28, x_520, x_3, x_546, x_7, x_8, x_9, x_10, x_538);
return x_547;
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
lean_dec(x_542);
lean_dec(x_539);
lean_dec(x_522);
lean_dec(x_520);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
x_548 = l_Lean_indentExpr(x_541);
x_549 = l_Lean_MVarId_rewrite___lambda__18___closed__6;
if (lean_is_scalar(x_543)) {
 x_550 = lean_alloc_ctor(7, 2, 0);
} else {
 x_550 = x_543;
 lean_ctor_set_tag(x_550, 7);
}
lean_ctor_set(x_550, 0, x_549);
lean_ctor_set(x_550, 1, x_548);
x_551 = l_Lean_MVarId_rewrite___lambda__18___closed__8;
if (lean_is_scalar(x_540)) {
 x_552 = lean_alloc_ctor(7, 2, 0);
} else {
 x_552 = x_540;
 lean_ctor_set_tag(x_552, 7);
}
lean_ctor_set(x_552, 0, x_550);
lean_ctor_set(x_552, 1, x_551);
x_553 = l_Lean_indentExpr(x_521);
x_554 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_554, 0, x_552);
lean_ctor_set(x_554, 1, x_553);
x_555 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_555);
lean_ctor_set(x_24, 0, x_554);
if (lean_is_scalar(x_536)) {
 x_556 = lean_alloc_ctor(1, 1, 0);
} else {
 x_556 = x_536;
}
lean_ctor_set(x_556, 0, x_24);
x_557 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_556, x_7, x_8, x_9, x_10, x_538);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_557, 1);
lean_inc(x_559);
if (lean_is_exclusive(x_557)) {
 lean_ctor_release(x_557, 0);
 lean_ctor_release(x_557, 1);
 x_560 = x_557;
} else {
 lean_dec_ref(x_557);
 x_560 = lean_box(0);
}
if (lean_is_scalar(x_560)) {
 x_561 = lean_alloc_ctor(1, 2, 0);
} else {
 x_561 = x_560;
}
lean_ctor_set(x_561, 0, x_558);
lean_ctor_set(x_561, 1, x_559);
return x_561;
}
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; 
lean_dec(x_521);
x_562 = lean_ctor_get(x_526, 1);
lean_inc(x_562);
lean_dec(x_526);
x_563 = lean_ctor_get(x_535, 0);
lean_inc(x_563);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 lean_ctor_release(x_535, 1);
 x_564 = x_535;
} else {
 lean_dec_ref(x_535);
 x_564 = lean_box(0);
}
x_565 = lean_ctor_get(x_537, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_537, 1);
lean_inc(x_566);
if (lean_is_exclusive(x_537)) {
 lean_ctor_release(x_537, 0);
 lean_ctor_release(x_537, 1);
 x_567 = x_537;
} else {
 lean_dec_ref(x_537);
 x_567 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_568 = l_Lean_Meta_mkEqSymm(x_522, x_7, x_8, x_9, x_10, x_562);
if (lean_obj_tag(x_568) == 0)
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_569 = lean_ctor_get(x_568, 0);
lean_inc(x_569);
x_570 = lean_ctor_get(x_568, 1);
lean_inc(x_570);
lean_dec(x_568);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_565);
lean_inc(x_566);
x_571 = l_Lean_Meta_mkEq(x_566, x_565, x_7, x_8, x_9, x_10, x_570);
if (lean_obj_tag(x_571) == 0)
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; uint8_t x_575; 
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
x_573 = lean_ctor_get(x_571, 1);
lean_inc(x_573);
lean_dec(x_571);
x_574 = l_Lean_Expr_getAppFn(x_566);
x_575 = l_Lean_Expr_isMVar(x_574);
lean_dec(x_574);
if (x_575 == 0)
{
lean_object* x_576; lean_object* x_577; 
lean_dec(x_572);
lean_dec(x_567);
lean_dec(x_564);
lean_dec(x_536);
lean_free_object(x_24);
x_576 = lean_box(0);
x_577 = l_Lean_MVarId_rewrite___lambda__9(x_5, x_6, x_566, x_565, x_563, x_569, x_2, x_1, x_28, x_520, x_3, x_576, x_7, x_8, x_9, x_10, x_573);
return x_577;
}
else
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
lean_dec(x_569);
lean_dec(x_565);
lean_dec(x_563);
lean_dec(x_520);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
x_578 = l_Lean_indentExpr(x_566);
x_579 = l_Lean_MVarId_rewrite___lambda__18___closed__6;
if (lean_is_scalar(x_567)) {
 x_580 = lean_alloc_ctor(7, 2, 0);
} else {
 x_580 = x_567;
 lean_ctor_set_tag(x_580, 7);
}
lean_ctor_set(x_580, 0, x_579);
lean_ctor_set(x_580, 1, x_578);
x_581 = l_Lean_MVarId_rewrite___lambda__18___closed__8;
if (lean_is_scalar(x_564)) {
 x_582 = lean_alloc_ctor(7, 2, 0);
} else {
 x_582 = x_564;
 lean_ctor_set_tag(x_582, 7);
}
lean_ctor_set(x_582, 0, x_580);
lean_ctor_set(x_582, 1, x_581);
x_583 = l_Lean_indentExpr(x_572);
x_584 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_584, 0, x_582);
lean_ctor_set(x_584, 1, x_583);
x_585 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_585);
lean_ctor_set(x_24, 0, x_584);
if (lean_is_scalar(x_536)) {
 x_586 = lean_alloc_ctor(1, 1, 0);
} else {
 x_586 = x_536;
}
lean_ctor_set(x_586, 0, x_24);
x_587 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_586, x_7, x_8, x_9, x_10, x_573);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_588 = lean_ctor_get(x_587, 0);
lean_inc(x_588);
x_589 = lean_ctor_get(x_587, 1);
lean_inc(x_589);
if (lean_is_exclusive(x_587)) {
 lean_ctor_release(x_587, 0);
 lean_ctor_release(x_587, 1);
 x_590 = x_587;
} else {
 lean_dec_ref(x_587);
 x_590 = lean_box(0);
}
if (lean_is_scalar(x_590)) {
 x_591 = lean_alloc_ctor(1, 2, 0);
} else {
 x_591 = x_590;
}
lean_ctor_set(x_591, 0, x_588);
lean_ctor_set(x_591, 1, x_589);
return x_591;
}
}
else
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
lean_dec(x_569);
lean_dec(x_567);
lean_dec(x_566);
lean_dec(x_565);
lean_dec(x_564);
lean_dec(x_563);
lean_dec(x_536);
lean_dec(x_520);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_592 = lean_ctor_get(x_571, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_571, 1);
lean_inc(x_593);
if (lean_is_exclusive(x_571)) {
 lean_ctor_release(x_571, 0);
 lean_ctor_release(x_571, 1);
 x_594 = x_571;
} else {
 lean_dec_ref(x_571);
 x_594 = lean_box(0);
}
if (lean_is_scalar(x_594)) {
 x_595 = lean_alloc_ctor(1, 2, 0);
} else {
 x_595 = x_594;
}
lean_ctor_set(x_595, 0, x_592);
lean_ctor_set(x_595, 1, x_593);
return x_595;
}
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
lean_dec(x_567);
lean_dec(x_566);
lean_dec(x_565);
lean_dec(x_564);
lean_dec(x_563);
lean_dec(x_536);
lean_dec(x_520);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_596 = lean_ctor_get(x_568, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_568, 1);
lean_inc(x_597);
if (lean_is_exclusive(x_568)) {
 lean_ctor_release(x_568, 0);
 lean_ctor_release(x_568, 1);
 x_598 = x_568;
} else {
 lean_dec_ref(x_568);
 x_598 = lean_box(0);
}
if (lean_is_scalar(x_598)) {
 x_599 = lean_alloc_ctor(1, 2, 0);
} else {
 x_599 = x_598;
}
lean_ctor_set(x_599, 0, x_596);
lean_ctor_set(x_599, 1, x_597);
return x_599;
}
}
}
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
lean_dec(x_522);
lean_dec(x_521);
lean_dec(x_520);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_600 = lean_ctor_get(x_526, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_526, 1);
lean_inc(x_601);
if (lean_is_exclusive(x_526)) {
 lean_ctor_release(x_526, 0);
 lean_ctor_release(x_526, 1);
 x_602 = x_526;
} else {
 lean_dec_ref(x_526);
 x_602 = lean_box(0);
}
if (lean_is_scalar(x_602)) {
 x_603 = lean_alloc_ctor(1, 2, 0);
} else {
 x_603 = x_602;
}
lean_ctor_set(x_603, 0, x_600);
lean_ctor_set(x_603, 1, x_601);
return x_603;
}
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; 
x_604 = l_Lean_Expr_appFn_x21(x_521);
x_605 = l_Lean_Expr_appArg_x21(x_604);
lean_dec(x_604);
x_606 = l_Lean_Expr_appArg_x21(x_521);
lean_dec(x_521);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_606);
lean_inc(x_605);
x_607 = l_Lean_Meta_mkEq(x_605, x_606, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_607) == 0)
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_608 = lean_ctor_get(x_607, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_607, 1);
lean_inc(x_609);
lean_dec(x_607);
x_610 = lean_box(0);
x_611 = l_Lean_MVarId_rewrite___lambda__18___closed__11;
x_612 = l_Lean_mkApp3(x_611, x_605, x_606, x_522);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_608);
x_613 = l_Lean_Meta_matchEq_x3f(x_608, x_7, x_8, x_9, x_10, x_609);
if (lean_obj_tag(x_613) == 0)
{
lean_object* x_614; 
x_614 = lean_ctor_get(x_613, 0);
lean_inc(x_614);
if (lean_obj_tag(x_614) == 0)
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
lean_dec(x_612);
lean_dec(x_520);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
x_615 = lean_ctor_get(x_613, 1);
lean_inc(x_615);
lean_dec(x_613);
x_616 = l_Lean_indentExpr(x_608);
x_617 = l_Lean_MVarId_rewrite___lambda__18___closed__4;
x_618 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_618, 0, x_617);
lean_ctor_set(x_618, 1, x_616);
x_619 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_619);
lean_ctor_set(x_24, 0, x_618);
x_620 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_620, 0, x_24);
x_621 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_620, x_7, x_8, x_9, x_10, x_615);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_621;
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_622 = lean_ctor_get(x_614, 0);
lean_inc(x_622);
if (lean_is_exclusive(x_614)) {
 lean_ctor_release(x_614, 0);
 x_623 = x_614;
} else {
 lean_dec_ref(x_614);
 x_623 = lean_box(0);
}
x_624 = lean_ctor_get(x_622, 1);
lean_inc(x_624);
if (x_4 == 0)
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; uint8_t x_632; 
x_625 = lean_ctor_get(x_613, 1);
lean_inc(x_625);
lean_dec(x_613);
x_626 = lean_ctor_get(x_622, 0);
lean_inc(x_626);
if (lean_is_exclusive(x_622)) {
 lean_ctor_release(x_622, 0);
 lean_ctor_release(x_622, 1);
 x_627 = x_622;
} else {
 lean_dec_ref(x_622);
 x_627 = lean_box(0);
}
x_628 = lean_ctor_get(x_624, 0);
lean_inc(x_628);
x_629 = lean_ctor_get(x_624, 1);
lean_inc(x_629);
if (lean_is_exclusive(x_624)) {
 lean_ctor_release(x_624, 0);
 lean_ctor_release(x_624, 1);
 x_630 = x_624;
} else {
 lean_dec_ref(x_624);
 x_630 = lean_box(0);
}
x_631 = l_Lean_Expr_getAppFn(x_628);
x_632 = l_Lean_Expr_isMVar(x_631);
lean_dec(x_631);
if (x_632 == 0)
{
lean_object* x_633; lean_object* x_634; 
lean_dec(x_630);
lean_dec(x_627);
lean_dec(x_623);
lean_dec(x_608);
lean_free_object(x_24);
x_633 = lean_box(0);
x_634 = l_Lean_MVarId_rewrite___lambda__13(x_5, x_6, x_628, x_629, x_626, x_610, x_612, x_2, x_1, x_28, x_520, x_3, x_633, x_7, x_8, x_9, x_10, x_625);
return x_634;
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
lean_dec(x_629);
lean_dec(x_626);
lean_dec(x_612);
lean_dec(x_520);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
x_635 = l_Lean_indentExpr(x_628);
x_636 = l_Lean_MVarId_rewrite___lambda__18___closed__6;
if (lean_is_scalar(x_630)) {
 x_637 = lean_alloc_ctor(7, 2, 0);
} else {
 x_637 = x_630;
 lean_ctor_set_tag(x_637, 7);
}
lean_ctor_set(x_637, 0, x_636);
lean_ctor_set(x_637, 1, x_635);
x_638 = l_Lean_MVarId_rewrite___lambda__18___closed__8;
if (lean_is_scalar(x_627)) {
 x_639 = lean_alloc_ctor(7, 2, 0);
} else {
 x_639 = x_627;
 lean_ctor_set_tag(x_639, 7);
}
lean_ctor_set(x_639, 0, x_637);
lean_ctor_set(x_639, 1, x_638);
x_640 = l_Lean_indentExpr(x_608);
x_641 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_641, 0, x_639);
lean_ctor_set(x_641, 1, x_640);
x_642 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_642);
lean_ctor_set(x_24, 0, x_641);
if (lean_is_scalar(x_623)) {
 x_643 = lean_alloc_ctor(1, 1, 0);
} else {
 x_643 = x_623;
}
lean_ctor_set(x_643, 0, x_24);
x_644 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_643, x_7, x_8, x_9, x_10, x_625);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_645 = lean_ctor_get(x_644, 0);
lean_inc(x_645);
x_646 = lean_ctor_get(x_644, 1);
lean_inc(x_646);
if (lean_is_exclusive(x_644)) {
 lean_ctor_release(x_644, 0);
 lean_ctor_release(x_644, 1);
 x_647 = x_644;
} else {
 lean_dec_ref(x_644);
 x_647 = lean_box(0);
}
if (lean_is_scalar(x_647)) {
 x_648 = lean_alloc_ctor(1, 2, 0);
} else {
 x_648 = x_647;
}
lean_ctor_set(x_648, 0, x_645);
lean_ctor_set(x_648, 1, x_646);
return x_648;
}
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; 
lean_dec(x_608);
x_649 = lean_ctor_get(x_613, 1);
lean_inc(x_649);
lean_dec(x_613);
x_650 = lean_ctor_get(x_622, 0);
lean_inc(x_650);
if (lean_is_exclusive(x_622)) {
 lean_ctor_release(x_622, 0);
 lean_ctor_release(x_622, 1);
 x_651 = x_622;
} else {
 lean_dec_ref(x_622);
 x_651 = lean_box(0);
}
x_652 = lean_ctor_get(x_624, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_624, 1);
lean_inc(x_653);
if (lean_is_exclusive(x_624)) {
 lean_ctor_release(x_624, 0);
 lean_ctor_release(x_624, 1);
 x_654 = x_624;
} else {
 lean_dec_ref(x_624);
 x_654 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_655 = l_Lean_Meta_mkEqSymm(x_612, x_7, x_8, x_9, x_10, x_649);
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; 
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_655, 1);
lean_inc(x_657);
lean_dec(x_655);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_652);
lean_inc(x_653);
x_658 = l_Lean_Meta_mkEq(x_653, x_652, x_7, x_8, x_9, x_10, x_657);
if (lean_obj_tag(x_658) == 0)
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; uint8_t x_662; 
x_659 = lean_ctor_get(x_658, 0);
lean_inc(x_659);
x_660 = lean_ctor_get(x_658, 1);
lean_inc(x_660);
lean_dec(x_658);
x_661 = l_Lean_Expr_getAppFn(x_653);
x_662 = l_Lean_Expr_isMVar(x_661);
lean_dec(x_661);
if (x_662 == 0)
{
lean_object* x_663; lean_object* x_664; 
lean_dec(x_659);
lean_dec(x_654);
lean_dec(x_651);
lean_dec(x_623);
lean_free_object(x_24);
x_663 = lean_box(0);
x_664 = l_Lean_MVarId_rewrite___lambda__17(x_5, x_6, x_653, x_652, x_650, x_610, x_656, x_2, x_1, x_28, x_520, x_3, x_663, x_7, x_8, x_9, x_10, x_660);
return x_664;
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; 
lean_dec(x_656);
lean_dec(x_652);
lean_dec(x_650);
lean_dec(x_520);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
x_665 = l_Lean_indentExpr(x_653);
x_666 = l_Lean_MVarId_rewrite___lambda__18___closed__6;
if (lean_is_scalar(x_654)) {
 x_667 = lean_alloc_ctor(7, 2, 0);
} else {
 x_667 = x_654;
 lean_ctor_set_tag(x_667, 7);
}
lean_ctor_set(x_667, 0, x_666);
lean_ctor_set(x_667, 1, x_665);
x_668 = l_Lean_MVarId_rewrite___lambda__18___closed__8;
if (lean_is_scalar(x_651)) {
 x_669 = lean_alloc_ctor(7, 2, 0);
} else {
 x_669 = x_651;
 lean_ctor_set_tag(x_669, 7);
}
lean_ctor_set(x_669, 0, x_667);
lean_ctor_set(x_669, 1, x_668);
x_670 = l_Lean_indentExpr(x_659);
x_671 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_671, 0, x_669);
lean_ctor_set(x_671, 1, x_670);
x_672 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_672);
lean_ctor_set(x_24, 0, x_671);
if (lean_is_scalar(x_623)) {
 x_673 = lean_alloc_ctor(1, 1, 0);
} else {
 x_673 = x_623;
}
lean_ctor_set(x_673, 0, x_24);
x_674 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_673, x_7, x_8, x_9, x_10, x_660);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_674, 1);
lean_inc(x_676);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 x_677 = x_674;
} else {
 lean_dec_ref(x_674);
 x_677 = lean_box(0);
}
if (lean_is_scalar(x_677)) {
 x_678 = lean_alloc_ctor(1, 2, 0);
} else {
 x_678 = x_677;
}
lean_ctor_set(x_678, 0, x_675);
lean_ctor_set(x_678, 1, x_676);
return x_678;
}
}
else
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; 
lean_dec(x_656);
lean_dec(x_654);
lean_dec(x_653);
lean_dec(x_652);
lean_dec(x_651);
lean_dec(x_650);
lean_dec(x_623);
lean_dec(x_520);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_679 = lean_ctor_get(x_658, 0);
lean_inc(x_679);
x_680 = lean_ctor_get(x_658, 1);
lean_inc(x_680);
if (lean_is_exclusive(x_658)) {
 lean_ctor_release(x_658, 0);
 lean_ctor_release(x_658, 1);
 x_681 = x_658;
} else {
 lean_dec_ref(x_658);
 x_681 = lean_box(0);
}
if (lean_is_scalar(x_681)) {
 x_682 = lean_alloc_ctor(1, 2, 0);
} else {
 x_682 = x_681;
}
lean_ctor_set(x_682, 0, x_679);
lean_ctor_set(x_682, 1, x_680);
return x_682;
}
}
else
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; 
lean_dec(x_654);
lean_dec(x_653);
lean_dec(x_652);
lean_dec(x_651);
lean_dec(x_650);
lean_dec(x_623);
lean_dec(x_520);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_683 = lean_ctor_get(x_655, 0);
lean_inc(x_683);
x_684 = lean_ctor_get(x_655, 1);
lean_inc(x_684);
if (lean_is_exclusive(x_655)) {
 lean_ctor_release(x_655, 0);
 lean_ctor_release(x_655, 1);
 x_685 = x_655;
} else {
 lean_dec_ref(x_655);
 x_685 = lean_box(0);
}
if (lean_is_scalar(x_685)) {
 x_686 = lean_alloc_ctor(1, 2, 0);
} else {
 x_686 = x_685;
}
lean_ctor_set(x_686, 0, x_683);
lean_ctor_set(x_686, 1, x_684);
return x_686;
}
}
}
}
else
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
lean_dec(x_612);
lean_dec(x_608);
lean_dec(x_520);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_687 = lean_ctor_get(x_613, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_613, 1);
lean_inc(x_688);
if (lean_is_exclusive(x_613)) {
 lean_ctor_release(x_613, 0);
 lean_ctor_release(x_613, 1);
 x_689 = x_613;
} else {
 lean_dec_ref(x_613);
 x_689 = lean_box(0);
}
if (lean_is_scalar(x_689)) {
 x_690 = lean_alloc_ctor(1, 2, 0);
} else {
 x_690 = x_689;
}
lean_ctor_set(x_690, 0, x_687);
lean_ctor_set(x_690, 1, x_688);
return x_690;
}
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; 
lean_dec(x_606);
lean_dec(x_605);
lean_dec(x_522);
lean_dec(x_520);
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_691 = lean_ctor_get(x_607, 0);
lean_inc(x_691);
x_692 = lean_ctor_get(x_607, 1);
lean_inc(x_692);
if (lean_is_exclusive(x_607)) {
 lean_ctor_release(x_607, 0);
 lean_ctor_release(x_607, 1);
 x_693 = x_607;
} else {
 lean_dec_ref(x_607);
 x_693 = lean_box(0);
}
if (lean_is_scalar(x_693)) {
 x_694 = lean_alloc_ctor(1, 2, 0);
} else {
 x_694 = x_693;
}
lean_ctor_set(x_694, 0, x_691);
lean_ctor_set(x_694, 1, x_692);
return x_694;
}
}
}
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; uint8_t x_702; 
x_695 = lean_ctor_get(x_24, 0);
lean_inc(x_695);
lean_dec(x_24);
x_696 = lean_ctor_get(x_25, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_25, 1);
lean_inc(x_697);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_698 = x_25;
} else {
 lean_dec_ref(x_25);
 x_698 = lean_box(0);
}
lean_inc(x_3);
x_699 = l_Lean_mkAppN(x_3, x_695);
x_700 = l_Lean_MVarId_rewrite___lambda__18___closed__2;
x_701 = lean_unsigned_to_nat(2u);
x_702 = l_Lean_Expr_isAppOfArity(x_697, x_700, x_701);
if (x_702 == 0)
{
lean_object* x_703; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_697);
x_703 = l_Lean_Meta_matchEq_x3f(x_697, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_703) == 0)
{
lean_object* x_704; 
x_704 = lean_ctor_get(x_703, 0);
lean_inc(x_704);
if (lean_obj_tag(x_704) == 0)
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; 
lean_dec(x_699);
lean_dec(x_696);
lean_dec(x_695);
lean_dec(x_5);
lean_dec(x_3);
x_705 = lean_ctor_get(x_703, 1);
lean_inc(x_705);
lean_dec(x_703);
x_706 = l_Lean_indentExpr(x_697);
x_707 = l_Lean_MVarId_rewrite___lambda__18___closed__4;
if (lean_is_scalar(x_698)) {
 x_708 = lean_alloc_ctor(7, 2, 0);
} else {
 x_708 = x_698;
 lean_ctor_set_tag(x_708, 7);
}
lean_ctor_set(x_708, 0, x_707);
lean_ctor_set(x_708, 1, x_706);
x_709 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
x_710 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_710, 0, x_708);
lean_ctor_set(x_710, 1, x_709);
x_711 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_711, 0, x_710);
x_712 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_711, x_7, x_8, x_9, x_10, x_705);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_712;
}
else
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_713 = lean_ctor_get(x_704, 0);
lean_inc(x_713);
if (lean_is_exclusive(x_704)) {
 lean_ctor_release(x_704, 0);
 x_714 = x_704;
} else {
 lean_dec_ref(x_704);
 x_714 = lean_box(0);
}
x_715 = lean_ctor_get(x_713, 1);
lean_inc(x_715);
if (x_4 == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; uint8_t x_723; 
x_716 = lean_ctor_get(x_703, 1);
lean_inc(x_716);
lean_dec(x_703);
x_717 = lean_ctor_get(x_713, 0);
lean_inc(x_717);
if (lean_is_exclusive(x_713)) {
 lean_ctor_release(x_713, 0);
 lean_ctor_release(x_713, 1);
 x_718 = x_713;
} else {
 lean_dec_ref(x_713);
 x_718 = lean_box(0);
}
x_719 = lean_ctor_get(x_715, 0);
lean_inc(x_719);
x_720 = lean_ctor_get(x_715, 1);
lean_inc(x_720);
if (lean_is_exclusive(x_715)) {
 lean_ctor_release(x_715, 0);
 lean_ctor_release(x_715, 1);
 x_721 = x_715;
} else {
 lean_dec_ref(x_715);
 x_721 = lean_box(0);
}
x_722 = l_Lean_Expr_getAppFn(x_719);
x_723 = l_Lean_Expr_isMVar(x_722);
lean_dec(x_722);
if (x_723 == 0)
{
lean_object* x_724; lean_object* x_725; 
lean_dec(x_721);
lean_dec(x_718);
lean_dec(x_714);
lean_dec(x_698);
lean_dec(x_697);
x_724 = lean_box(0);
x_725 = l_Lean_MVarId_rewrite___lambda__5(x_5, x_6, x_719, x_720, x_717, x_699, x_2, x_1, x_695, x_696, x_3, x_724, x_7, x_8, x_9, x_10, x_716);
return x_725;
}
else
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
lean_dec(x_720);
lean_dec(x_717);
lean_dec(x_699);
lean_dec(x_696);
lean_dec(x_695);
lean_dec(x_5);
lean_dec(x_3);
x_726 = l_Lean_indentExpr(x_719);
x_727 = l_Lean_MVarId_rewrite___lambda__18___closed__6;
if (lean_is_scalar(x_721)) {
 x_728 = lean_alloc_ctor(7, 2, 0);
} else {
 x_728 = x_721;
 lean_ctor_set_tag(x_728, 7);
}
lean_ctor_set(x_728, 0, x_727);
lean_ctor_set(x_728, 1, x_726);
x_729 = l_Lean_MVarId_rewrite___lambda__18___closed__8;
if (lean_is_scalar(x_718)) {
 x_730 = lean_alloc_ctor(7, 2, 0);
} else {
 x_730 = x_718;
 lean_ctor_set_tag(x_730, 7);
}
lean_ctor_set(x_730, 0, x_728);
lean_ctor_set(x_730, 1, x_729);
x_731 = l_Lean_indentExpr(x_697);
if (lean_is_scalar(x_698)) {
 x_732 = lean_alloc_ctor(7, 2, 0);
} else {
 x_732 = x_698;
 lean_ctor_set_tag(x_732, 7);
}
lean_ctor_set(x_732, 0, x_730);
lean_ctor_set(x_732, 1, x_731);
x_733 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
x_734 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_734, 0, x_732);
lean_ctor_set(x_734, 1, x_733);
if (lean_is_scalar(x_714)) {
 x_735 = lean_alloc_ctor(1, 1, 0);
} else {
 x_735 = x_714;
}
lean_ctor_set(x_735, 0, x_734);
x_736 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_735, x_7, x_8, x_9, x_10, x_716);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_737 = lean_ctor_get(x_736, 0);
lean_inc(x_737);
x_738 = lean_ctor_get(x_736, 1);
lean_inc(x_738);
if (lean_is_exclusive(x_736)) {
 lean_ctor_release(x_736, 0);
 lean_ctor_release(x_736, 1);
 x_739 = x_736;
} else {
 lean_dec_ref(x_736);
 x_739 = lean_box(0);
}
if (lean_is_scalar(x_739)) {
 x_740 = lean_alloc_ctor(1, 2, 0);
} else {
 x_740 = x_739;
}
lean_ctor_set(x_740, 0, x_737);
lean_ctor_set(x_740, 1, x_738);
return x_740;
}
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; 
lean_dec(x_697);
x_741 = lean_ctor_get(x_703, 1);
lean_inc(x_741);
lean_dec(x_703);
x_742 = lean_ctor_get(x_713, 0);
lean_inc(x_742);
if (lean_is_exclusive(x_713)) {
 lean_ctor_release(x_713, 0);
 lean_ctor_release(x_713, 1);
 x_743 = x_713;
} else {
 lean_dec_ref(x_713);
 x_743 = lean_box(0);
}
x_744 = lean_ctor_get(x_715, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_715, 1);
lean_inc(x_745);
if (lean_is_exclusive(x_715)) {
 lean_ctor_release(x_715, 0);
 lean_ctor_release(x_715, 1);
 x_746 = x_715;
} else {
 lean_dec_ref(x_715);
 x_746 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_747 = l_Lean_Meta_mkEqSymm(x_699, x_7, x_8, x_9, x_10, x_741);
if (lean_obj_tag(x_747) == 0)
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; 
x_748 = lean_ctor_get(x_747, 0);
lean_inc(x_748);
x_749 = lean_ctor_get(x_747, 1);
lean_inc(x_749);
lean_dec(x_747);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_744);
lean_inc(x_745);
x_750 = l_Lean_Meta_mkEq(x_745, x_744, x_7, x_8, x_9, x_10, x_749);
if (lean_obj_tag(x_750) == 0)
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; uint8_t x_754; 
x_751 = lean_ctor_get(x_750, 0);
lean_inc(x_751);
x_752 = lean_ctor_get(x_750, 1);
lean_inc(x_752);
lean_dec(x_750);
x_753 = l_Lean_Expr_getAppFn(x_745);
x_754 = l_Lean_Expr_isMVar(x_753);
lean_dec(x_753);
if (x_754 == 0)
{
lean_object* x_755; lean_object* x_756; 
lean_dec(x_751);
lean_dec(x_746);
lean_dec(x_743);
lean_dec(x_714);
lean_dec(x_698);
x_755 = lean_box(0);
x_756 = l_Lean_MVarId_rewrite___lambda__9(x_5, x_6, x_745, x_744, x_742, x_748, x_2, x_1, x_695, x_696, x_3, x_755, x_7, x_8, x_9, x_10, x_752);
return x_756;
}
else
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; 
lean_dec(x_748);
lean_dec(x_744);
lean_dec(x_742);
lean_dec(x_696);
lean_dec(x_695);
lean_dec(x_5);
lean_dec(x_3);
x_757 = l_Lean_indentExpr(x_745);
x_758 = l_Lean_MVarId_rewrite___lambda__18___closed__6;
if (lean_is_scalar(x_746)) {
 x_759 = lean_alloc_ctor(7, 2, 0);
} else {
 x_759 = x_746;
 lean_ctor_set_tag(x_759, 7);
}
lean_ctor_set(x_759, 0, x_758);
lean_ctor_set(x_759, 1, x_757);
x_760 = l_Lean_MVarId_rewrite___lambda__18___closed__8;
if (lean_is_scalar(x_743)) {
 x_761 = lean_alloc_ctor(7, 2, 0);
} else {
 x_761 = x_743;
 lean_ctor_set_tag(x_761, 7);
}
lean_ctor_set(x_761, 0, x_759);
lean_ctor_set(x_761, 1, x_760);
x_762 = l_Lean_indentExpr(x_751);
if (lean_is_scalar(x_698)) {
 x_763 = lean_alloc_ctor(7, 2, 0);
} else {
 x_763 = x_698;
 lean_ctor_set_tag(x_763, 7);
}
lean_ctor_set(x_763, 0, x_761);
lean_ctor_set(x_763, 1, x_762);
x_764 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
x_765 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_765, 0, x_763);
lean_ctor_set(x_765, 1, x_764);
if (lean_is_scalar(x_714)) {
 x_766 = lean_alloc_ctor(1, 1, 0);
} else {
 x_766 = x_714;
}
lean_ctor_set(x_766, 0, x_765);
x_767 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_766, x_7, x_8, x_9, x_10, x_752);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_768 = lean_ctor_get(x_767, 0);
lean_inc(x_768);
x_769 = lean_ctor_get(x_767, 1);
lean_inc(x_769);
if (lean_is_exclusive(x_767)) {
 lean_ctor_release(x_767, 0);
 lean_ctor_release(x_767, 1);
 x_770 = x_767;
} else {
 lean_dec_ref(x_767);
 x_770 = lean_box(0);
}
if (lean_is_scalar(x_770)) {
 x_771 = lean_alloc_ctor(1, 2, 0);
} else {
 x_771 = x_770;
}
lean_ctor_set(x_771, 0, x_768);
lean_ctor_set(x_771, 1, x_769);
return x_771;
}
}
else
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; 
lean_dec(x_748);
lean_dec(x_746);
lean_dec(x_745);
lean_dec(x_744);
lean_dec(x_743);
lean_dec(x_742);
lean_dec(x_714);
lean_dec(x_698);
lean_dec(x_696);
lean_dec(x_695);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_772 = lean_ctor_get(x_750, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_750, 1);
lean_inc(x_773);
if (lean_is_exclusive(x_750)) {
 lean_ctor_release(x_750, 0);
 lean_ctor_release(x_750, 1);
 x_774 = x_750;
} else {
 lean_dec_ref(x_750);
 x_774 = lean_box(0);
}
if (lean_is_scalar(x_774)) {
 x_775 = lean_alloc_ctor(1, 2, 0);
} else {
 x_775 = x_774;
}
lean_ctor_set(x_775, 0, x_772);
lean_ctor_set(x_775, 1, x_773);
return x_775;
}
}
else
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; 
lean_dec(x_746);
lean_dec(x_745);
lean_dec(x_744);
lean_dec(x_743);
lean_dec(x_742);
lean_dec(x_714);
lean_dec(x_698);
lean_dec(x_696);
lean_dec(x_695);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_776 = lean_ctor_get(x_747, 0);
lean_inc(x_776);
x_777 = lean_ctor_get(x_747, 1);
lean_inc(x_777);
if (lean_is_exclusive(x_747)) {
 lean_ctor_release(x_747, 0);
 lean_ctor_release(x_747, 1);
 x_778 = x_747;
} else {
 lean_dec_ref(x_747);
 x_778 = lean_box(0);
}
if (lean_is_scalar(x_778)) {
 x_779 = lean_alloc_ctor(1, 2, 0);
} else {
 x_779 = x_778;
}
lean_ctor_set(x_779, 0, x_776);
lean_ctor_set(x_779, 1, x_777);
return x_779;
}
}
}
}
else
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; 
lean_dec(x_699);
lean_dec(x_698);
lean_dec(x_697);
lean_dec(x_696);
lean_dec(x_695);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_780 = lean_ctor_get(x_703, 0);
lean_inc(x_780);
x_781 = lean_ctor_get(x_703, 1);
lean_inc(x_781);
if (lean_is_exclusive(x_703)) {
 lean_ctor_release(x_703, 0);
 lean_ctor_release(x_703, 1);
 x_782 = x_703;
} else {
 lean_dec_ref(x_703);
 x_782 = lean_box(0);
}
if (lean_is_scalar(x_782)) {
 x_783 = lean_alloc_ctor(1, 2, 0);
} else {
 x_783 = x_782;
}
lean_ctor_set(x_783, 0, x_780);
lean_ctor_set(x_783, 1, x_781);
return x_783;
}
}
else
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; 
x_784 = l_Lean_Expr_appFn_x21(x_697);
x_785 = l_Lean_Expr_appArg_x21(x_784);
lean_dec(x_784);
x_786 = l_Lean_Expr_appArg_x21(x_697);
lean_dec(x_697);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_786);
lean_inc(x_785);
x_787 = l_Lean_Meta_mkEq(x_785, x_786, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_787) == 0)
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; 
x_788 = lean_ctor_get(x_787, 0);
lean_inc(x_788);
x_789 = lean_ctor_get(x_787, 1);
lean_inc(x_789);
lean_dec(x_787);
x_790 = lean_box(0);
x_791 = l_Lean_MVarId_rewrite___lambda__18___closed__11;
x_792 = l_Lean_mkApp3(x_791, x_785, x_786, x_699);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_788);
x_793 = l_Lean_Meta_matchEq_x3f(x_788, x_7, x_8, x_9, x_10, x_789);
if (lean_obj_tag(x_793) == 0)
{
lean_object* x_794; 
x_794 = lean_ctor_get(x_793, 0);
lean_inc(x_794);
if (lean_obj_tag(x_794) == 0)
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; 
lean_dec(x_792);
lean_dec(x_696);
lean_dec(x_695);
lean_dec(x_5);
lean_dec(x_3);
x_795 = lean_ctor_get(x_793, 1);
lean_inc(x_795);
lean_dec(x_793);
x_796 = l_Lean_indentExpr(x_788);
x_797 = l_Lean_MVarId_rewrite___lambda__18___closed__4;
if (lean_is_scalar(x_698)) {
 x_798 = lean_alloc_ctor(7, 2, 0);
} else {
 x_798 = x_698;
 lean_ctor_set_tag(x_798, 7);
}
lean_ctor_set(x_798, 0, x_797);
lean_ctor_set(x_798, 1, x_796);
x_799 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
x_800 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_800, 0, x_798);
lean_ctor_set(x_800, 1, x_799);
x_801 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_801, 0, x_800);
x_802 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_801, x_7, x_8, x_9, x_10, x_795);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_802;
}
else
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; 
x_803 = lean_ctor_get(x_794, 0);
lean_inc(x_803);
if (lean_is_exclusive(x_794)) {
 lean_ctor_release(x_794, 0);
 x_804 = x_794;
} else {
 lean_dec_ref(x_794);
 x_804 = lean_box(0);
}
x_805 = lean_ctor_get(x_803, 1);
lean_inc(x_805);
if (x_4 == 0)
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; uint8_t x_813; 
x_806 = lean_ctor_get(x_793, 1);
lean_inc(x_806);
lean_dec(x_793);
x_807 = lean_ctor_get(x_803, 0);
lean_inc(x_807);
if (lean_is_exclusive(x_803)) {
 lean_ctor_release(x_803, 0);
 lean_ctor_release(x_803, 1);
 x_808 = x_803;
} else {
 lean_dec_ref(x_803);
 x_808 = lean_box(0);
}
x_809 = lean_ctor_get(x_805, 0);
lean_inc(x_809);
x_810 = lean_ctor_get(x_805, 1);
lean_inc(x_810);
if (lean_is_exclusive(x_805)) {
 lean_ctor_release(x_805, 0);
 lean_ctor_release(x_805, 1);
 x_811 = x_805;
} else {
 lean_dec_ref(x_805);
 x_811 = lean_box(0);
}
x_812 = l_Lean_Expr_getAppFn(x_809);
x_813 = l_Lean_Expr_isMVar(x_812);
lean_dec(x_812);
if (x_813 == 0)
{
lean_object* x_814; lean_object* x_815; 
lean_dec(x_811);
lean_dec(x_808);
lean_dec(x_804);
lean_dec(x_788);
lean_dec(x_698);
x_814 = lean_box(0);
x_815 = l_Lean_MVarId_rewrite___lambda__13(x_5, x_6, x_809, x_810, x_807, x_790, x_792, x_2, x_1, x_695, x_696, x_3, x_814, x_7, x_8, x_9, x_10, x_806);
return x_815;
}
else
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; 
lean_dec(x_810);
lean_dec(x_807);
lean_dec(x_792);
lean_dec(x_696);
lean_dec(x_695);
lean_dec(x_5);
lean_dec(x_3);
x_816 = l_Lean_indentExpr(x_809);
x_817 = l_Lean_MVarId_rewrite___lambda__18___closed__6;
if (lean_is_scalar(x_811)) {
 x_818 = lean_alloc_ctor(7, 2, 0);
} else {
 x_818 = x_811;
 lean_ctor_set_tag(x_818, 7);
}
lean_ctor_set(x_818, 0, x_817);
lean_ctor_set(x_818, 1, x_816);
x_819 = l_Lean_MVarId_rewrite___lambda__18___closed__8;
if (lean_is_scalar(x_808)) {
 x_820 = lean_alloc_ctor(7, 2, 0);
} else {
 x_820 = x_808;
 lean_ctor_set_tag(x_820, 7);
}
lean_ctor_set(x_820, 0, x_818);
lean_ctor_set(x_820, 1, x_819);
x_821 = l_Lean_indentExpr(x_788);
if (lean_is_scalar(x_698)) {
 x_822 = lean_alloc_ctor(7, 2, 0);
} else {
 x_822 = x_698;
 lean_ctor_set_tag(x_822, 7);
}
lean_ctor_set(x_822, 0, x_820);
lean_ctor_set(x_822, 1, x_821);
x_823 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
x_824 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_824, 0, x_822);
lean_ctor_set(x_824, 1, x_823);
if (lean_is_scalar(x_804)) {
 x_825 = lean_alloc_ctor(1, 1, 0);
} else {
 x_825 = x_804;
}
lean_ctor_set(x_825, 0, x_824);
x_826 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_825, x_7, x_8, x_9, x_10, x_806);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_827 = lean_ctor_get(x_826, 0);
lean_inc(x_827);
x_828 = lean_ctor_get(x_826, 1);
lean_inc(x_828);
if (lean_is_exclusive(x_826)) {
 lean_ctor_release(x_826, 0);
 lean_ctor_release(x_826, 1);
 x_829 = x_826;
} else {
 lean_dec_ref(x_826);
 x_829 = lean_box(0);
}
if (lean_is_scalar(x_829)) {
 x_830 = lean_alloc_ctor(1, 2, 0);
} else {
 x_830 = x_829;
}
lean_ctor_set(x_830, 0, x_827);
lean_ctor_set(x_830, 1, x_828);
return x_830;
}
}
else
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; 
lean_dec(x_788);
x_831 = lean_ctor_get(x_793, 1);
lean_inc(x_831);
lean_dec(x_793);
x_832 = lean_ctor_get(x_803, 0);
lean_inc(x_832);
if (lean_is_exclusive(x_803)) {
 lean_ctor_release(x_803, 0);
 lean_ctor_release(x_803, 1);
 x_833 = x_803;
} else {
 lean_dec_ref(x_803);
 x_833 = lean_box(0);
}
x_834 = lean_ctor_get(x_805, 0);
lean_inc(x_834);
x_835 = lean_ctor_get(x_805, 1);
lean_inc(x_835);
if (lean_is_exclusive(x_805)) {
 lean_ctor_release(x_805, 0);
 lean_ctor_release(x_805, 1);
 x_836 = x_805;
} else {
 lean_dec_ref(x_805);
 x_836 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_837 = l_Lean_Meta_mkEqSymm(x_792, x_7, x_8, x_9, x_10, x_831);
if (lean_obj_tag(x_837) == 0)
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; 
x_838 = lean_ctor_get(x_837, 0);
lean_inc(x_838);
x_839 = lean_ctor_get(x_837, 1);
lean_inc(x_839);
lean_dec(x_837);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_834);
lean_inc(x_835);
x_840 = l_Lean_Meta_mkEq(x_835, x_834, x_7, x_8, x_9, x_10, x_839);
if (lean_obj_tag(x_840) == 0)
{
lean_object* x_841; lean_object* x_842; lean_object* x_843; uint8_t x_844; 
x_841 = lean_ctor_get(x_840, 0);
lean_inc(x_841);
x_842 = lean_ctor_get(x_840, 1);
lean_inc(x_842);
lean_dec(x_840);
x_843 = l_Lean_Expr_getAppFn(x_835);
x_844 = l_Lean_Expr_isMVar(x_843);
lean_dec(x_843);
if (x_844 == 0)
{
lean_object* x_845; lean_object* x_846; 
lean_dec(x_841);
lean_dec(x_836);
lean_dec(x_833);
lean_dec(x_804);
lean_dec(x_698);
x_845 = lean_box(0);
x_846 = l_Lean_MVarId_rewrite___lambda__17(x_5, x_6, x_835, x_834, x_832, x_790, x_838, x_2, x_1, x_695, x_696, x_3, x_845, x_7, x_8, x_9, x_10, x_842);
return x_846;
}
else
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; 
lean_dec(x_838);
lean_dec(x_834);
lean_dec(x_832);
lean_dec(x_696);
lean_dec(x_695);
lean_dec(x_5);
lean_dec(x_3);
x_847 = l_Lean_indentExpr(x_835);
x_848 = l_Lean_MVarId_rewrite___lambda__18___closed__6;
if (lean_is_scalar(x_836)) {
 x_849 = lean_alloc_ctor(7, 2, 0);
} else {
 x_849 = x_836;
 lean_ctor_set_tag(x_849, 7);
}
lean_ctor_set(x_849, 0, x_848);
lean_ctor_set(x_849, 1, x_847);
x_850 = l_Lean_MVarId_rewrite___lambda__18___closed__8;
if (lean_is_scalar(x_833)) {
 x_851 = lean_alloc_ctor(7, 2, 0);
} else {
 x_851 = x_833;
 lean_ctor_set_tag(x_851, 7);
}
lean_ctor_set(x_851, 0, x_849);
lean_ctor_set(x_851, 1, x_850);
x_852 = l_Lean_indentExpr(x_841);
if (lean_is_scalar(x_698)) {
 x_853 = lean_alloc_ctor(7, 2, 0);
} else {
 x_853 = x_698;
 lean_ctor_set_tag(x_853, 7);
}
lean_ctor_set(x_853, 0, x_851);
lean_ctor_set(x_853, 1, x_852);
x_854 = l_Lean_MVarId_rewrite___lambda__3___closed__6;
x_855 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_855, 0, x_853);
lean_ctor_set(x_855, 1, x_854);
if (lean_is_scalar(x_804)) {
 x_856 = lean_alloc_ctor(1, 1, 0);
} else {
 x_856 = x_804;
}
lean_ctor_set(x_856, 0, x_855);
x_857 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_856, x_7, x_8, x_9, x_10, x_842);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_858 = lean_ctor_get(x_857, 0);
lean_inc(x_858);
x_859 = lean_ctor_get(x_857, 1);
lean_inc(x_859);
if (lean_is_exclusive(x_857)) {
 lean_ctor_release(x_857, 0);
 lean_ctor_release(x_857, 1);
 x_860 = x_857;
} else {
 lean_dec_ref(x_857);
 x_860 = lean_box(0);
}
if (lean_is_scalar(x_860)) {
 x_861 = lean_alloc_ctor(1, 2, 0);
} else {
 x_861 = x_860;
}
lean_ctor_set(x_861, 0, x_858);
lean_ctor_set(x_861, 1, x_859);
return x_861;
}
}
else
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; 
lean_dec(x_838);
lean_dec(x_836);
lean_dec(x_835);
lean_dec(x_834);
lean_dec(x_833);
lean_dec(x_832);
lean_dec(x_804);
lean_dec(x_698);
lean_dec(x_696);
lean_dec(x_695);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_862 = lean_ctor_get(x_840, 0);
lean_inc(x_862);
x_863 = lean_ctor_get(x_840, 1);
lean_inc(x_863);
if (lean_is_exclusive(x_840)) {
 lean_ctor_release(x_840, 0);
 lean_ctor_release(x_840, 1);
 x_864 = x_840;
} else {
 lean_dec_ref(x_840);
 x_864 = lean_box(0);
}
if (lean_is_scalar(x_864)) {
 x_865 = lean_alloc_ctor(1, 2, 0);
} else {
 x_865 = x_864;
}
lean_ctor_set(x_865, 0, x_862);
lean_ctor_set(x_865, 1, x_863);
return x_865;
}
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; 
lean_dec(x_836);
lean_dec(x_835);
lean_dec(x_834);
lean_dec(x_833);
lean_dec(x_832);
lean_dec(x_804);
lean_dec(x_698);
lean_dec(x_696);
lean_dec(x_695);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_866 = lean_ctor_get(x_837, 0);
lean_inc(x_866);
x_867 = lean_ctor_get(x_837, 1);
lean_inc(x_867);
if (lean_is_exclusive(x_837)) {
 lean_ctor_release(x_837, 0);
 lean_ctor_release(x_837, 1);
 x_868 = x_837;
} else {
 lean_dec_ref(x_837);
 x_868 = lean_box(0);
}
if (lean_is_scalar(x_868)) {
 x_869 = lean_alloc_ctor(1, 2, 0);
} else {
 x_869 = x_868;
}
lean_ctor_set(x_869, 0, x_866);
lean_ctor_set(x_869, 1, x_867);
return x_869;
}
}
}
}
else
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; 
lean_dec(x_792);
lean_dec(x_788);
lean_dec(x_698);
lean_dec(x_696);
lean_dec(x_695);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_870 = lean_ctor_get(x_793, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_793, 1);
lean_inc(x_871);
if (lean_is_exclusive(x_793)) {
 lean_ctor_release(x_793, 0);
 lean_ctor_release(x_793, 1);
 x_872 = x_793;
} else {
 lean_dec_ref(x_793);
 x_872 = lean_box(0);
}
if (lean_is_scalar(x_872)) {
 x_873 = lean_alloc_ctor(1, 2, 0);
} else {
 x_873 = x_872;
}
lean_ctor_set(x_873, 0, x_870);
lean_ctor_set(x_873, 1, x_871);
return x_873;
}
}
else
{
lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; 
lean_dec(x_786);
lean_dec(x_785);
lean_dec(x_699);
lean_dec(x_698);
lean_dec(x_696);
lean_dec(x_695);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_874 = lean_ctor_get(x_787, 0);
lean_inc(x_874);
x_875 = lean_ctor_get(x_787, 1);
lean_inc(x_875);
if (lean_is_exclusive(x_787)) {
 lean_ctor_release(x_787, 0);
 lean_ctor_release(x_787, 1);
 x_876 = x_787;
} else {
 lean_dec_ref(x_787);
 x_876 = lean_box(0);
}
if (lean_is_scalar(x_876)) {
 x_877 = lean_alloc_ctor(1, 2, 0);
} else {
 x_877 = x_876;
}
lean_ctor_set(x_877, 0, x_874);
lean_ctor_set(x_877, 1, x_875);
return x_877;
}
}
}
}
else
{
uint8_t x_878; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_878 = !lean_is_exclusive(x_23);
if (x_878 == 0)
{
return x_23;
}
else
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; 
x_879 = lean_ctor_get(x_23, 0);
x_880 = lean_ctor_get(x_23, 1);
lean_inc(x_880);
lean_inc(x_879);
lean_dec(x_23);
x_881 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_881, 0, x_879);
lean_ctor_set(x_881, 1, x_880);
return x_881;
}
}
}
else
{
uint8_t x_882; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_882 = !lean_is_exclusive(x_14);
if (x_882 == 0)
{
return x_14;
}
else
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; 
x_883 = lean_ctor_get(x_14, 0);
x_884 = lean_ctor_get(x_14, 1);
lean_inc(x_884);
lean_inc(x_883);
lean_dec(x_14);
x_885 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_885, 0, x_883);
lean_ctor_set(x_885, 1, x_884);
return x_885;
}
}
}
else
{
uint8_t x_886; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_886 = !lean_is_exclusive(x_12);
if (x_886 == 0)
{
return x_12;
}
else
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; 
x_887 = lean_ctor_get(x_12, 0);
x_888 = lean_ctor_get(x_12, 1);
lean_inc(x_888);
lean_inc(x_887);
lean_dec(x_12);
x_889 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_889, 0, x_887);
lean_ctor_set(x_889, 1, x_888);
return x_889;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rewrite", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_rewrite___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_MVarId_rewrite___closed__2;
x_12 = lean_box(x_4);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lambda__18___boxed), 11, 6);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_11);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_12);
lean_closure_set(x_13, 4, x_2);
lean_closure_set(x_13, 5, x_5);
x_14 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_13, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_rewrite___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_MVarId_rewrite___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_MVarId_rewrite___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_MVarId_rewrite___spec__3(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at_Lean_MVarId_rewrite___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at_Lean_MVarId_rewrite___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__4(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__5(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__6(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__7(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__8(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_rewrite___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__2___boxed(lean_object** _args) {
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
x_19 = l_Lean_MVarId_rewrite___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_13);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__3___boxed(lean_object** _args) {
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
x_18 = l_Lean_MVarId_rewrite___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__4___boxed(lean_object** _args) {
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
x_18 = l_Lean_MVarId_rewrite___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_12);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__5___boxed(lean_object** _args) {
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
x_18 = l_Lean_MVarId_rewrite___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_12);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__6___boxed(lean_object** _args) {
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
x_19 = l_Lean_MVarId_rewrite___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_13);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__7___boxed(lean_object** _args) {
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
x_18 = l_Lean_MVarId_rewrite___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__8___boxed(lean_object** _args) {
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
x_18 = l_Lean_MVarId_rewrite___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_12);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__9___boxed(lean_object** _args) {
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
x_18 = l_Lean_MVarId_rewrite___lambda__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_12);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__10___boxed(lean_object** _args) {
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
_start:
{
lean_object* x_20; 
x_20 = l_Lean_MVarId_rewrite___lambda__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_14);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__11___boxed(lean_object** _args) {
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
x_19 = l_Lean_MVarId_rewrite___lambda__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__12___boxed(lean_object** _args) {
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
x_19 = l_Lean_MVarId_rewrite___lambda__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_13);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__13___boxed(lean_object** _args) {
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
x_19 = l_Lean_MVarId_rewrite___lambda__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_13);
lean_dec(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__14___boxed(lean_object** _args) {
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
_start:
{
lean_object* x_20; 
x_20 = l_Lean_MVarId_rewrite___lambda__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_14);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__15___boxed(lean_object** _args) {
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
x_19 = l_Lean_MVarId_rewrite___lambda__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__16___boxed(lean_object** _args) {
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
x_19 = l_Lean_MVarId_rewrite___lambda__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_13);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__17___boxed(lean_object** _args) {
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
x_19 = l_Lean_MVarId_rewrite___lambda__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_13);
lean_dec(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_MVarId_rewrite___lambda__18(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_MVarId_rewrite(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_KAbstract(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_BinderNameHint(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MatchUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_KAbstract(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_BinderNameHint(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_MVarId_rewrite___lambda__2___closed__1 = _init_l_Lean_MVarId_rewrite___lambda__2___closed__1();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__2___closed__1);
l_Lean_MVarId_rewrite___lambda__2___closed__2 = _init_l_Lean_MVarId_rewrite___lambda__2___closed__2();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__2___closed__2);
l_Lean_MVarId_rewrite___lambda__2___closed__3 = _init_l_Lean_MVarId_rewrite___lambda__2___closed__3();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__2___closed__3);
l_Lean_MVarId_rewrite___lambda__2___closed__4 = _init_l_Lean_MVarId_rewrite___lambda__2___closed__4();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__2___closed__4);
l_Lean_MVarId_rewrite___lambda__3___closed__1 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__1();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__1);
l_Lean_MVarId_rewrite___lambda__3___closed__2 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__2();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__2);
l_Lean_MVarId_rewrite___lambda__3___closed__3 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__3();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__3);
l_Lean_MVarId_rewrite___lambda__3___closed__4 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__4();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__4);
l_Lean_MVarId_rewrite___lambda__3___closed__5 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__5();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__5);
l_Lean_MVarId_rewrite___lambda__3___closed__6 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__6();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__6);
l_Lean_MVarId_rewrite___lambda__3___closed__7 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__7();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__7);
l_Lean_MVarId_rewrite___lambda__3___closed__8 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__8();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__8);
l_Lean_MVarId_rewrite___lambda__3___closed__9 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__9();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__9);
l_Lean_MVarId_rewrite___lambda__3___closed__10 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__10();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__10);
l_Lean_MVarId_rewrite___lambda__3___closed__11 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__11();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__11);
l_Lean_MVarId_rewrite___lambda__3___closed__12 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__12();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__12);
l_Lean_MVarId_rewrite___lambda__3___closed__13 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__13();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__13);
l_Lean_MVarId_rewrite___lambda__3___closed__14 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__14();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__14);
l_Lean_MVarId_rewrite___lambda__3___closed__15 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__15();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__15);
l_Lean_MVarId_rewrite___lambda__3___closed__16 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__16();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__16);
l_Lean_MVarId_rewrite___lambda__3___closed__17 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__17();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__17);
l_Lean_MVarId_rewrite___lambda__3___closed__18 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__18();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__18);
l_Lean_MVarId_rewrite___lambda__3___closed__19 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__19();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__19);
l_Lean_MVarId_rewrite___lambda__3___closed__20 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__20();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__20);
l_Lean_MVarId_rewrite___lambda__3___closed__21 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__21();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__21);
l_Lean_MVarId_rewrite___lambda__3___closed__22 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__22();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__22);
l_Lean_MVarId_rewrite___lambda__3___closed__23 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__23();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__23);
l_Lean_MVarId_rewrite___lambda__3___closed__24 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__24();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__24);
l_Lean_MVarId_rewrite___lambda__3___closed__25 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__25();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__25);
l_Lean_MVarId_rewrite___lambda__3___closed__26 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__26();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__26);
l_Lean_MVarId_rewrite___lambda__5___closed__1 = _init_l_Lean_MVarId_rewrite___lambda__5___closed__1();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__5___closed__1);
l_Lean_MVarId_rewrite___lambda__5___closed__2 = _init_l_Lean_MVarId_rewrite___lambda__5___closed__2();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__5___closed__2);
l_Lean_MVarId_rewrite___lambda__18___closed__1 = _init_l_Lean_MVarId_rewrite___lambda__18___closed__1();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__18___closed__1);
l_Lean_MVarId_rewrite___lambda__18___closed__2 = _init_l_Lean_MVarId_rewrite___lambda__18___closed__2();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__18___closed__2);
l_Lean_MVarId_rewrite___lambda__18___closed__3 = _init_l_Lean_MVarId_rewrite___lambda__18___closed__3();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__18___closed__3);
l_Lean_MVarId_rewrite___lambda__18___closed__4 = _init_l_Lean_MVarId_rewrite___lambda__18___closed__4();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__18___closed__4);
l_Lean_MVarId_rewrite___lambda__18___closed__5 = _init_l_Lean_MVarId_rewrite___lambda__18___closed__5();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__18___closed__5);
l_Lean_MVarId_rewrite___lambda__18___closed__6 = _init_l_Lean_MVarId_rewrite___lambda__18___closed__6();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__18___closed__6);
l_Lean_MVarId_rewrite___lambda__18___closed__7 = _init_l_Lean_MVarId_rewrite___lambda__18___closed__7();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__18___closed__7);
l_Lean_MVarId_rewrite___lambda__18___closed__8 = _init_l_Lean_MVarId_rewrite___lambda__18___closed__8();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__18___closed__8);
l_Lean_MVarId_rewrite___lambda__18___closed__9 = _init_l_Lean_MVarId_rewrite___lambda__18___closed__9();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__18___closed__9);
l_Lean_MVarId_rewrite___lambda__18___closed__10 = _init_l_Lean_MVarId_rewrite___lambda__18___closed__10();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__18___closed__10);
l_Lean_MVarId_rewrite___lambda__18___closed__11 = _init_l_Lean_MVarId_rewrite___lambda__18___closed__11();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__18___closed__11);
l_Lean_MVarId_rewrite___closed__1 = _init_l_Lean_MVarId_rewrite___closed__1();
lean_mark_persistent(l_Lean_MVarId_rewrite___closed__1);
l_Lean_MVarId_rewrite___closed__2 = _init_l_Lean_MVarId_rewrite___closed__2();
lean_mark_persistent(l_Lean_MVarId_rewrite___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
