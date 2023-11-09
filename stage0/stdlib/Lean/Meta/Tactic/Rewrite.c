// Lean compiler output
// Module: Lean.Meta.Tactic.Rewrite
// Imports: Init Lean.Meta.AppBuilder Lean.Meta.MatchUtil Lean.Meta.KAbstract Lean.Meta.Check Lean.Meta.Tactic.Apply
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
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at_Lean_MVarId_rewrite___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__2___closed__2;
static lean_object* l_Lean_MVarId_rewrite___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at_Lean_MVarId_rewrite___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__13___closed__10;
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__13___closed__7;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_rewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__13___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__13___closed__9;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_postprocessAppMVars(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__2___closed__1;
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__2___closed__4;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__13___closed__8;
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__13___closed__11;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__13(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_rewrite___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__13___closed__1;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__2___closed__5;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__13___closed__5;
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__2___closed__3;
static lean_object* l_Lean_MVarId_rewrite___lambda__13___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_MVarId_rewrite___spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__13___closed__2;
static lean_object* l_Lean_MVarId_rewrite___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lambda__1___closed__1;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_MVarId_rewrite___lambda__3___closed__4;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_MVarId_rewrite___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_MVarId_rewrite___lambda__13___closed__6;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_rewrite___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc(x_11);
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
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_15 = l_Lean_Meta_mkEqRefl(x_1, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_18 = l_Lean_Meta_mkEqNDRec(x_2, x_16, x_3, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_23 = l_Lean_Meta_postprocessAppMVars(x_4, x_5, x_6, x_7, x_21, x_22, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_array_get_size(x_6);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = 0;
x_28 = l_Array_mapMUnsafe_map___at_Lean_MVarId_rewrite___spec__1(x_26, x_27, x_6);
x_29 = lean_array_get_size(x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_lt(x_30, x_29);
if (x_31 == 0)
{
lean_object* x_77; 
lean_dec(x_29);
lean_dec(x_28);
x_77 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_32 = x_77;
x_33 = x_24;
goto block_76;
}
else
{
uint8_t x_78; 
x_78 = lean_nat_dec_le(x_29, x_29);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_29);
lean_dec(x_28);
x_79 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_32 = x_79;
x_33 = x_24;
goto block_76;
}
else
{
size_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_81 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_82 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__5(x_28, x_27, x_80, x_81, x_10, x_11, x_12, x_13, x_24);
lean_dec(x_28);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_32 = x_83;
x_33 = x_84;
goto block_76;
}
}
block_76:
{
lean_object* x_34; uint8_t x_35; 
lean_inc(x_19);
x_34 = l_Lean_Meta_getMVarsNoDelayed(x_19, x_10, x_11, x_12, x_13, x_33);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_array_get_size(x_36);
x_38 = lean_nat_dec_lt(x_30, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_37);
lean_dec(x_36);
x_39 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_40 = l_Array_append___rarg(x_32, x_39);
x_41 = lean_array_to_list(lean_box(0), x_40);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_8);
lean_ctor_set(x_42, 1, x_19);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_34, 0, x_42);
return x_34;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_37, x_37);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_37);
lean_dec(x_36);
x_44 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_45 = l_Array_append___rarg(x_32, x_44);
x_46 = lean_array_to_list(lean_box(0), x_45);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_8);
lean_ctor_set(x_47, 1, x_19);
lean_ctor_set(x_47, 2, x_46);
lean_ctor_set(x_34, 0, x_47);
return x_34;
}
else
{
size_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_49 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_50 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__4(x_32, x_36, x_27, x_48, x_49);
lean_dec(x_36);
x_51 = l_Array_append___rarg(x_32, x_50);
x_52 = lean_array_to_list(lean_box(0), x_51);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_8);
lean_ctor_set(x_53, 1, x_19);
lean_ctor_set(x_53, 2, x_52);
lean_ctor_set(x_34, 0, x_53);
return x_34;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_34, 0);
x_55 = lean_ctor_get(x_34, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_34);
x_56 = lean_array_get_size(x_54);
x_57 = lean_nat_dec_lt(x_30, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_56);
lean_dec(x_54);
x_58 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_59 = l_Array_append___rarg(x_32, x_58);
x_60 = lean_array_to_list(lean_box(0), x_59);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_8);
lean_ctor_set(x_61, 1, x_19);
lean_ctor_set(x_61, 2, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_55);
return x_62;
}
else
{
uint8_t x_63; 
x_63 = lean_nat_dec_le(x_56, x_56);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_56);
lean_dec(x_54);
x_64 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_65 = l_Array_append___rarg(x_32, x_64);
x_66 = lean_array_to_list(lean_box(0), x_65);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_8);
lean_ctor_set(x_67, 1, x_19);
lean_ctor_set(x_67, 2, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_55);
return x_68;
}
else
{
size_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_70 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_71 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__4(x_32, x_54, x_27, x_69, x_70);
lean_dec(x_54);
x_72 = l_Array_append___rarg(x_32, x_71);
x_73 = lean_array_to_list(lean_box(0), x_72);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_8);
lean_ctor_set(x_74, 1, x_19);
lean_ctor_set(x_74, 2, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_55);
return x_75;
}
}
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
x_85 = !lean_is_exclusive(x_23);
if (x_85 == 0)
{
return x_23;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_23, 0);
x_87 = lean_ctor_get(x_23, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_23);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_89 = !lean_is_exclusive(x_18);
if (x_89 == 0)
{
return x_18;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_18, 0);
x_91 = lean_ctor_get(x_18, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_18);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_93 = !lean_is_exclusive(x_15);
if (x_93 == 0)
{
return x_15;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_15, 0);
x_95 = lean_ctor_get(x_15, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_15);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_a", 2);
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
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("motive is not type correct", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lambda__2___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lambda__2___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
x_16 = lean_expr_instantiate1(x_1, x_2);
lean_dec(x_2);
x_17 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_16, x_11, x_12, x_13, x_14, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc_n(x_3, 2);
x_20 = l_Lean_Meta_mkEq(x_3, x_3, x_11, x_12, x_13, x_14, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Expr_appFn_x21(x_21);
lean_dec(x_21);
x_24 = l_Lean_Expr_app___override(x_23, x_1);
x_25 = l_Lean_MVarId_rewrite___lambda__2___closed__2;
x_26 = 0;
x_27 = l_Lean_Expr_lam___override(x_25, x_4, x_24, x_26);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_27);
x_28 = l_Lean_Meta_isTypeCorrect(x_27, x_11, x_12, x_13, x_14, x_22);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_MVarId_rewrite___lambda__2___closed__5;
x_33 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_7, x_32, x_11, x_12, x_13, x_14, x_31);
lean_dec(x_14);
lean_dec(x_12);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_dec(x_28);
x_39 = lean_box(0);
x_40 = l_Lean_MVarId_rewrite___lambda__1(x_3, x_27, x_5, x_6, x_7, x_8, x_9, x_18, x_39, x_11, x_12, x_13, x_14, x_38);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_28);
if (x_41 == 0)
{
return x_28;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_28, 0);
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_28);
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
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_20);
if (x_45 == 0)
{
return x_20;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_20, 0);
x_47 = lean_ctor_get(x_20, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_20);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("did not find instance of the pattern in the target expression", 61);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_11);
x_17 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_1, x_12, x_13, x_14, x_15, x_16);
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_12, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_12, 3);
lean_inc(x_24);
x_25 = lean_ctor_get(x_12, 4);
lean_inc(x_25);
x_26 = lean_ctor_get(x_12, 5);
lean_inc(x_26);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_dec(x_2);
lean_ctor_set_uint8(x_18, 8, x_28);
lean_ctor_set_uint8(x_18, 9, x_29);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 3, x_24);
lean_ctor_set(x_30, 4, x_25);
lean_ctor_set(x_30, 5, x_26);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_3);
lean_inc(x_19);
x_31 = l_Lean_Meta_kabstract(x_19, x_3, x_21, x_30, x_13, x_14, x_15, x_20);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Expr_hasLooseBVars(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_32);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = l_Lean_indentExpr(x_3);
x_36 = l_Lean_MVarId_rewrite___lambda__3___closed__2;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_MVarId_rewrite___lambda__3___closed__4;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_8, x_39, x_12, x_13, x_14, x_15, x_33);
lean_dec(x_15);
lean_dec(x_13);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_3);
x_45 = lean_box(0);
x_46 = l_Lean_MVarId_rewrite___lambda__2(x_32, x_4, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_45, x_12, x_13, x_14, x_15, x_33);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_31);
if (x_47 == 0)
{
return x_31;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_31, 0);
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_31);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_51 = lean_ctor_get_uint8(x_18, 0);
x_52 = lean_ctor_get_uint8(x_18, 1);
x_53 = lean_ctor_get_uint8(x_18, 2);
x_54 = lean_ctor_get_uint8(x_18, 3);
x_55 = lean_ctor_get_uint8(x_18, 4);
x_56 = lean_ctor_get_uint8(x_18, 5);
x_57 = lean_ctor_get_uint8(x_18, 6);
x_58 = lean_ctor_get_uint8(x_18, 7);
x_59 = lean_ctor_get_uint8(x_18, 10);
x_60 = lean_ctor_get_uint8(x_18, 11);
lean_dec(x_18);
x_61 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_62 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_dec(x_2);
x_63 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_63, 0, x_51);
lean_ctor_set_uint8(x_63, 1, x_52);
lean_ctor_set_uint8(x_63, 2, x_53);
lean_ctor_set_uint8(x_63, 3, x_54);
lean_ctor_set_uint8(x_63, 4, x_55);
lean_ctor_set_uint8(x_63, 5, x_56);
lean_ctor_set_uint8(x_63, 6, x_57);
lean_ctor_set_uint8(x_63, 7, x_58);
lean_ctor_set_uint8(x_63, 8, x_61);
lean_ctor_set_uint8(x_63, 9, x_62);
lean_ctor_set_uint8(x_63, 10, x_59);
lean_ctor_set_uint8(x_63, 11, x_60);
x_64 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_22);
lean_ctor_set(x_64, 2, x_23);
lean_ctor_set(x_64, 3, x_24);
lean_ctor_set(x_64, 4, x_25);
lean_ctor_set(x_64, 5, x_26);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_3);
lean_inc(x_19);
x_65 = l_Lean_Meta_kabstract(x_19, x_3, x_21, x_64, x_13, x_14, x_15, x_20);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Expr_hasLooseBVars(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_66);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_69 = l_Lean_indentExpr(x_3);
x_70 = l_Lean_MVarId_rewrite___lambda__3___closed__2;
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_Lean_MVarId_rewrite___lambda__3___closed__4;
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_8, x_73, x_12, x_13, x_14, x_15, x_67);
lean_dec(x_15);
lean_dec(x_13);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_3);
x_79 = lean_box(0);
x_80 = l_Lean_MVarId_rewrite___lambda__2(x_66, x_4, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_79, x_12, x_13, x_14, x_15, x_67);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_81 = lean_ctor_get(x_65, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_65, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_83 = x_65;
} else {
 lean_dec_ref(x_65);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_15 = l_Lean_Meta_mkEqRefl(x_1, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_18 = l_Lean_Meta_mkEqNDRec(x_2, x_16, x_3, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_23 = l_Lean_Meta_postprocessAppMVars(x_4, x_5, x_6, x_7, x_21, x_22, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_array_get_size(x_6);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = 0;
x_28 = l_Array_mapMUnsafe_map___at_Lean_MVarId_rewrite___spec__1(x_26, x_27, x_6);
x_29 = lean_array_get_size(x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_lt(x_30, x_29);
if (x_31 == 0)
{
lean_object* x_77; 
lean_dec(x_29);
lean_dec(x_28);
x_77 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_32 = x_77;
x_33 = x_24;
goto block_76;
}
else
{
uint8_t x_78; 
x_78 = lean_nat_dec_le(x_29, x_29);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_29);
lean_dec(x_28);
x_79 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_32 = x_79;
x_33 = x_24;
goto block_76;
}
else
{
size_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_81 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_82 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__5(x_28, x_27, x_80, x_81, x_10, x_11, x_12, x_13, x_24);
lean_dec(x_28);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_32 = x_83;
x_33 = x_84;
goto block_76;
}
}
block_76:
{
lean_object* x_34; uint8_t x_35; 
lean_inc(x_19);
x_34 = l_Lean_Meta_getMVarsNoDelayed(x_19, x_10, x_11, x_12, x_13, x_33);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_array_get_size(x_36);
x_38 = lean_nat_dec_lt(x_30, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_37);
lean_dec(x_36);
x_39 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_40 = l_Array_append___rarg(x_32, x_39);
x_41 = lean_array_to_list(lean_box(0), x_40);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_8);
lean_ctor_set(x_42, 1, x_19);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_34, 0, x_42);
return x_34;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_37, x_37);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_37);
lean_dec(x_36);
x_44 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_45 = l_Array_append___rarg(x_32, x_44);
x_46 = lean_array_to_list(lean_box(0), x_45);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_8);
lean_ctor_set(x_47, 1, x_19);
lean_ctor_set(x_47, 2, x_46);
lean_ctor_set(x_34, 0, x_47);
return x_34;
}
else
{
size_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_49 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_50 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__6(x_32, x_36, x_27, x_48, x_49);
lean_dec(x_36);
x_51 = l_Array_append___rarg(x_32, x_50);
x_52 = lean_array_to_list(lean_box(0), x_51);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_8);
lean_ctor_set(x_53, 1, x_19);
lean_ctor_set(x_53, 2, x_52);
lean_ctor_set(x_34, 0, x_53);
return x_34;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_34, 0);
x_55 = lean_ctor_get(x_34, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_34);
x_56 = lean_array_get_size(x_54);
x_57 = lean_nat_dec_lt(x_30, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_56);
lean_dec(x_54);
x_58 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_59 = l_Array_append___rarg(x_32, x_58);
x_60 = lean_array_to_list(lean_box(0), x_59);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_8);
lean_ctor_set(x_61, 1, x_19);
lean_ctor_set(x_61, 2, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_55);
return x_62;
}
else
{
uint8_t x_63; 
x_63 = lean_nat_dec_le(x_56, x_56);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_56);
lean_dec(x_54);
x_64 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_65 = l_Array_append___rarg(x_32, x_64);
x_66 = lean_array_to_list(lean_box(0), x_65);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_8);
lean_ctor_set(x_67, 1, x_19);
lean_ctor_set(x_67, 2, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_55);
return x_68;
}
else
{
size_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_70 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_71 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__6(x_32, x_54, x_27, x_69, x_70);
lean_dec(x_54);
x_72 = l_Array_append___rarg(x_32, x_71);
x_73 = lean_array_to_list(lean_box(0), x_72);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_8);
lean_ctor_set(x_74, 1, x_19);
lean_ctor_set(x_74, 2, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_55);
return x_75;
}
}
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
x_85 = !lean_is_exclusive(x_23);
if (x_85 == 0)
{
return x_23;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_23, 0);
x_87 = lean_ctor_get(x_23, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_23);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_89 = !lean_is_exclusive(x_18);
if (x_89 == 0)
{
return x_18;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_18, 0);
x_91 = lean_ctor_get(x_18, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_18);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_93 = !lean_is_exclusive(x_15);
if (x_93 == 0)
{
return x_15;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_15, 0);
x_95 = lean_ctor_get(x_15, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_15);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
x_16 = lean_expr_instantiate1(x_1, x_2);
lean_dec(x_2);
x_17 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_16, x_11, x_12, x_13, x_14, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc_n(x_3, 2);
x_20 = l_Lean_Meta_mkEq(x_3, x_3, x_11, x_12, x_13, x_14, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Expr_appFn_x21(x_21);
lean_dec(x_21);
x_24 = l_Lean_Expr_app___override(x_23, x_1);
x_25 = l_Lean_MVarId_rewrite___lambda__2___closed__2;
x_26 = 0;
x_27 = l_Lean_Expr_lam___override(x_25, x_4, x_24, x_26);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_27);
x_28 = l_Lean_Meta_isTypeCorrect(x_27, x_11, x_12, x_13, x_14, x_22);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_MVarId_rewrite___lambda__2___closed__5;
x_33 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_7, x_32, x_11, x_12, x_13, x_14, x_31);
lean_dec(x_14);
lean_dec(x_12);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_dec(x_28);
x_39 = lean_box(0);
x_40 = l_Lean_MVarId_rewrite___lambda__4(x_3, x_27, x_5, x_6, x_7, x_8, x_9, x_18, x_39, x_11, x_12, x_13, x_14, x_38);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_28);
if (x_41 == 0)
{
return x_28;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_28, 0);
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_28);
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
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_20);
if (x_45 == 0)
{
return x_20;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_20, 0);
x_47 = lean_ctor_get(x_20, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_20);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_11);
x_17 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_1, x_12, x_13, x_14, x_15, x_16);
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_12, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_12, 3);
lean_inc(x_24);
x_25 = lean_ctor_get(x_12, 4);
lean_inc(x_25);
x_26 = lean_ctor_get(x_12, 5);
lean_inc(x_26);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_dec(x_2);
lean_ctor_set_uint8(x_18, 8, x_28);
lean_ctor_set_uint8(x_18, 9, x_29);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 3, x_24);
lean_ctor_set(x_30, 4, x_25);
lean_ctor_set(x_30, 5, x_26);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_3);
lean_inc(x_19);
x_31 = l_Lean_Meta_kabstract(x_19, x_3, x_21, x_30, x_13, x_14, x_15, x_20);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Expr_hasLooseBVars(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_32);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = l_Lean_indentExpr(x_3);
x_36 = l_Lean_MVarId_rewrite___lambda__3___closed__2;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_MVarId_rewrite___lambda__3___closed__4;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_8, x_39, x_12, x_13, x_14, x_15, x_33);
lean_dec(x_15);
lean_dec(x_13);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_3);
x_45 = lean_box(0);
x_46 = l_Lean_MVarId_rewrite___lambda__5(x_32, x_4, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_45, x_12, x_13, x_14, x_15, x_33);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_31);
if (x_47 == 0)
{
return x_31;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_31, 0);
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_31);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_51 = lean_ctor_get_uint8(x_18, 0);
x_52 = lean_ctor_get_uint8(x_18, 1);
x_53 = lean_ctor_get_uint8(x_18, 2);
x_54 = lean_ctor_get_uint8(x_18, 3);
x_55 = lean_ctor_get_uint8(x_18, 4);
x_56 = lean_ctor_get_uint8(x_18, 5);
x_57 = lean_ctor_get_uint8(x_18, 6);
x_58 = lean_ctor_get_uint8(x_18, 7);
x_59 = lean_ctor_get_uint8(x_18, 10);
x_60 = lean_ctor_get_uint8(x_18, 11);
lean_dec(x_18);
x_61 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_62 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_dec(x_2);
x_63 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_63, 0, x_51);
lean_ctor_set_uint8(x_63, 1, x_52);
lean_ctor_set_uint8(x_63, 2, x_53);
lean_ctor_set_uint8(x_63, 3, x_54);
lean_ctor_set_uint8(x_63, 4, x_55);
lean_ctor_set_uint8(x_63, 5, x_56);
lean_ctor_set_uint8(x_63, 6, x_57);
lean_ctor_set_uint8(x_63, 7, x_58);
lean_ctor_set_uint8(x_63, 8, x_61);
lean_ctor_set_uint8(x_63, 9, x_62);
lean_ctor_set_uint8(x_63, 10, x_59);
lean_ctor_set_uint8(x_63, 11, x_60);
x_64 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_22);
lean_ctor_set(x_64, 2, x_23);
lean_ctor_set(x_64, 3, x_24);
lean_ctor_set(x_64, 4, x_25);
lean_ctor_set(x_64, 5, x_26);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_3);
lean_inc(x_19);
x_65 = l_Lean_Meta_kabstract(x_19, x_3, x_21, x_64, x_13, x_14, x_15, x_20);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Expr_hasLooseBVars(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_66);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_69 = l_Lean_indentExpr(x_3);
x_70 = l_Lean_MVarId_rewrite___lambda__3___closed__2;
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_Lean_MVarId_rewrite___lambda__3___closed__4;
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_8, x_73, x_12, x_13, x_14, x_15, x_67);
lean_dec(x_15);
lean_dec(x_13);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_3);
x_79 = lean_box(0);
x_80 = l_Lean_MVarId_rewrite___lambda__5(x_66, x_4, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_79, x_12, x_13, x_14, x_15, x_67);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_81 = lean_ctor_get(x_65, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_65, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_83 = x_65;
} else {
 lean_dec_ref(x_65);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_15 = l_Lean_Meta_mkEqRefl(x_1, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_18 = l_Lean_Meta_mkEqNDRec(x_2, x_16, x_3, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_23 = l_Lean_Meta_postprocessAppMVars(x_4, x_5, x_6, x_7, x_21, x_22, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_array_get_size(x_6);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = 0;
x_28 = l_Array_mapMUnsafe_map___at_Lean_MVarId_rewrite___spec__1(x_26, x_27, x_6);
x_29 = lean_array_get_size(x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_lt(x_30, x_29);
if (x_31 == 0)
{
lean_object* x_77; 
lean_dec(x_29);
lean_dec(x_28);
x_77 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_32 = x_77;
x_33 = x_24;
goto block_76;
}
else
{
uint8_t x_78; 
x_78 = lean_nat_dec_le(x_29, x_29);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_29);
lean_dec(x_28);
x_79 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_32 = x_79;
x_33 = x_24;
goto block_76;
}
else
{
size_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_81 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_82 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__5(x_28, x_27, x_80, x_81, x_10, x_11, x_12, x_13, x_24);
lean_dec(x_28);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_32 = x_83;
x_33 = x_84;
goto block_76;
}
}
block_76:
{
lean_object* x_34; uint8_t x_35; 
lean_inc(x_19);
x_34 = l_Lean_Meta_getMVarsNoDelayed(x_19, x_10, x_11, x_12, x_13, x_33);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_array_get_size(x_36);
x_38 = lean_nat_dec_lt(x_30, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_37);
lean_dec(x_36);
x_39 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_40 = l_Array_append___rarg(x_32, x_39);
x_41 = lean_array_to_list(lean_box(0), x_40);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_8);
lean_ctor_set(x_42, 1, x_19);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_34, 0, x_42);
return x_34;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_37, x_37);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_37);
lean_dec(x_36);
x_44 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_45 = l_Array_append___rarg(x_32, x_44);
x_46 = lean_array_to_list(lean_box(0), x_45);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_8);
lean_ctor_set(x_47, 1, x_19);
lean_ctor_set(x_47, 2, x_46);
lean_ctor_set(x_34, 0, x_47);
return x_34;
}
else
{
size_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_49 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_50 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__7(x_32, x_36, x_27, x_48, x_49);
lean_dec(x_36);
x_51 = l_Array_append___rarg(x_32, x_50);
x_52 = lean_array_to_list(lean_box(0), x_51);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_8);
lean_ctor_set(x_53, 1, x_19);
lean_ctor_set(x_53, 2, x_52);
lean_ctor_set(x_34, 0, x_53);
return x_34;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_34, 0);
x_55 = lean_ctor_get(x_34, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_34);
x_56 = lean_array_get_size(x_54);
x_57 = lean_nat_dec_lt(x_30, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_56);
lean_dec(x_54);
x_58 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_59 = l_Array_append___rarg(x_32, x_58);
x_60 = lean_array_to_list(lean_box(0), x_59);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_8);
lean_ctor_set(x_61, 1, x_19);
lean_ctor_set(x_61, 2, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_55);
return x_62;
}
else
{
uint8_t x_63; 
x_63 = lean_nat_dec_le(x_56, x_56);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_56);
lean_dec(x_54);
x_64 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_65 = l_Array_append___rarg(x_32, x_64);
x_66 = lean_array_to_list(lean_box(0), x_65);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_8);
lean_ctor_set(x_67, 1, x_19);
lean_ctor_set(x_67, 2, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_55);
return x_68;
}
else
{
size_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_70 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_71 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__7(x_32, x_54, x_27, x_69, x_70);
lean_dec(x_54);
x_72 = l_Array_append___rarg(x_32, x_71);
x_73 = lean_array_to_list(lean_box(0), x_72);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_8);
lean_ctor_set(x_74, 1, x_19);
lean_ctor_set(x_74, 2, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_55);
return x_75;
}
}
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
x_85 = !lean_is_exclusive(x_23);
if (x_85 == 0)
{
return x_23;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_23, 0);
x_87 = lean_ctor_get(x_23, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_23);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_89 = !lean_is_exclusive(x_18);
if (x_89 == 0)
{
return x_18;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_18, 0);
x_91 = lean_ctor_get(x_18, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_18);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_93 = !lean_is_exclusive(x_15);
if (x_93 == 0)
{
return x_15;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_15, 0);
x_95 = lean_ctor_get(x_15, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_15);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
x_16 = lean_expr_instantiate1(x_1, x_2);
lean_dec(x_2);
x_17 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_16, x_11, x_12, x_13, x_14, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc_n(x_3, 2);
x_20 = l_Lean_Meta_mkEq(x_3, x_3, x_11, x_12, x_13, x_14, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Expr_appFn_x21(x_21);
lean_dec(x_21);
x_24 = l_Lean_Expr_app___override(x_23, x_1);
x_25 = l_Lean_MVarId_rewrite___lambda__2___closed__2;
x_26 = 0;
x_27 = l_Lean_Expr_lam___override(x_25, x_4, x_24, x_26);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_27);
x_28 = l_Lean_Meta_isTypeCorrect(x_27, x_11, x_12, x_13, x_14, x_22);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_MVarId_rewrite___lambda__2___closed__5;
x_33 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_7, x_32, x_11, x_12, x_13, x_14, x_31);
lean_dec(x_14);
lean_dec(x_12);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_dec(x_28);
x_39 = lean_box(0);
x_40 = l_Lean_MVarId_rewrite___lambda__7(x_3, x_27, x_5, x_6, x_7, x_8, x_9, x_18, x_39, x_11, x_12, x_13, x_14, x_38);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_28);
if (x_41 == 0)
{
return x_28;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_28, 0);
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_28);
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
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_20);
if (x_45 == 0)
{
return x_20;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_20, 0);
x_47 = lean_ctor_get(x_20, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_20);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_11);
x_17 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_1, x_12, x_13, x_14, x_15, x_16);
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_12, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_12, 3);
lean_inc(x_24);
x_25 = lean_ctor_get(x_12, 4);
lean_inc(x_25);
x_26 = lean_ctor_get(x_12, 5);
lean_inc(x_26);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_dec(x_2);
lean_ctor_set_uint8(x_18, 8, x_28);
lean_ctor_set_uint8(x_18, 9, x_29);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 3, x_24);
lean_ctor_set(x_30, 4, x_25);
lean_ctor_set(x_30, 5, x_26);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_3);
lean_inc(x_19);
x_31 = l_Lean_Meta_kabstract(x_19, x_3, x_21, x_30, x_13, x_14, x_15, x_20);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Expr_hasLooseBVars(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_32);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = l_Lean_indentExpr(x_3);
x_36 = l_Lean_MVarId_rewrite___lambda__3___closed__2;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_MVarId_rewrite___lambda__3___closed__4;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_8, x_39, x_12, x_13, x_14, x_15, x_33);
lean_dec(x_15);
lean_dec(x_13);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_3);
x_45 = lean_box(0);
x_46 = l_Lean_MVarId_rewrite___lambda__8(x_32, x_4, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_45, x_12, x_13, x_14, x_15, x_33);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_31);
if (x_47 == 0)
{
return x_31;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_31, 0);
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_31);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_51 = lean_ctor_get_uint8(x_18, 0);
x_52 = lean_ctor_get_uint8(x_18, 1);
x_53 = lean_ctor_get_uint8(x_18, 2);
x_54 = lean_ctor_get_uint8(x_18, 3);
x_55 = lean_ctor_get_uint8(x_18, 4);
x_56 = lean_ctor_get_uint8(x_18, 5);
x_57 = lean_ctor_get_uint8(x_18, 6);
x_58 = lean_ctor_get_uint8(x_18, 7);
x_59 = lean_ctor_get_uint8(x_18, 10);
x_60 = lean_ctor_get_uint8(x_18, 11);
lean_dec(x_18);
x_61 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_62 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_dec(x_2);
x_63 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_63, 0, x_51);
lean_ctor_set_uint8(x_63, 1, x_52);
lean_ctor_set_uint8(x_63, 2, x_53);
lean_ctor_set_uint8(x_63, 3, x_54);
lean_ctor_set_uint8(x_63, 4, x_55);
lean_ctor_set_uint8(x_63, 5, x_56);
lean_ctor_set_uint8(x_63, 6, x_57);
lean_ctor_set_uint8(x_63, 7, x_58);
lean_ctor_set_uint8(x_63, 8, x_61);
lean_ctor_set_uint8(x_63, 9, x_62);
lean_ctor_set_uint8(x_63, 10, x_59);
lean_ctor_set_uint8(x_63, 11, x_60);
x_64 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_22);
lean_ctor_set(x_64, 2, x_23);
lean_ctor_set(x_64, 3, x_24);
lean_ctor_set(x_64, 4, x_25);
lean_ctor_set(x_64, 5, x_26);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_3);
lean_inc(x_19);
x_65 = l_Lean_Meta_kabstract(x_19, x_3, x_21, x_64, x_13, x_14, x_15, x_20);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Expr_hasLooseBVars(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_66);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_69 = l_Lean_indentExpr(x_3);
x_70 = l_Lean_MVarId_rewrite___lambda__3___closed__2;
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_Lean_MVarId_rewrite___lambda__3___closed__4;
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_8, x_73, x_12, x_13, x_14, x_15, x_67);
lean_dec(x_15);
lean_dec(x_13);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_3);
x_79 = lean_box(0);
x_80 = l_Lean_MVarId_rewrite___lambda__8(x_66, x_4, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_79, x_12, x_13, x_14, x_15, x_67);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_81 = lean_ctor_get(x_65, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_65, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_83 = x_65;
} else {
 lean_dec_ref(x_65);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_15 = l_Lean_Meta_mkEqRefl(x_1, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_18 = l_Lean_Meta_mkEqNDRec(x_2, x_16, x_3, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_23 = l_Lean_Meta_postprocessAppMVars(x_4, x_5, x_6, x_7, x_21, x_22, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_array_get_size(x_6);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = 0;
x_28 = l_Array_mapMUnsafe_map___at_Lean_MVarId_rewrite___spec__1(x_26, x_27, x_6);
x_29 = lean_array_get_size(x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_lt(x_30, x_29);
if (x_31 == 0)
{
lean_object* x_77; 
lean_dec(x_29);
lean_dec(x_28);
x_77 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_32 = x_77;
x_33 = x_24;
goto block_76;
}
else
{
uint8_t x_78; 
x_78 = lean_nat_dec_le(x_29, x_29);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_29);
lean_dec(x_28);
x_79 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_32 = x_79;
x_33 = x_24;
goto block_76;
}
else
{
size_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_81 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_82 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__5(x_28, x_27, x_80, x_81, x_10, x_11, x_12, x_13, x_24);
lean_dec(x_28);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_32 = x_83;
x_33 = x_84;
goto block_76;
}
}
block_76:
{
lean_object* x_34; uint8_t x_35; 
lean_inc(x_19);
x_34 = l_Lean_Meta_getMVarsNoDelayed(x_19, x_10, x_11, x_12, x_13, x_33);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_array_get_size(x_36);
x_38 = lean_nat_dec_lt(x_30, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_37);
lean_dec(x_36);
x_39 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_40 = l_Array_append___rarg(x_32, x_39);
x_41 = lean_array_to_list(lean_box(0), x_40);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_8);
lean_ctor_set(x_42, 1, x_19);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_34, 0, x_42);
return x_34;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_37, x_37);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_37);
lean_dec(x_36);
x_44 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_45 = l_Array_append___rarg(x_32, x_44);
x_46 = lean_array_to_list(lean_box(0), x_45);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_8);
lean_ctor_set(x_47, 1, x_19);
lean_ctor_set(x_47, 2, x_46);
lean_ctor_set(x_34, 0, x_47);
return x_34;
}
else
{
size_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_49 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_50 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__8(x_32, x_36, x_27, x_48, x_49);
lean_dec(x_36);
x_51 = l_Array_append___rarg(x_32, x_50);
x_52 = lean_array_to_list(lean_box(0), x_51);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_8);
lean_ctor_set(x_53, 1, x_19);
lean_ctor_set(x_53, 2, x_52);
lean_ctor_set(x_34, 0, x_53);
return x_34;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_34, 0);
x_55 = lean_ctor_get(x_34, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_34);
x_56 = lean_array_get_size(x_54);
x_57 = lean_nat_dec_lt(x_30, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_56);
lean_dec(x_54);
x_58 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_59 = l_Array_append___rarg(x_32, x_58);
x_60 = lean_array_to_list(lean_box(0), x_59);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_8);
lean_ctor_set(x_61, 1, x_19);
lean_ctor_set(x_61, 2, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_55);
return x_62;
}
else
{
uint8_t x_63; 
x_63 = lean_nat_dec_le(x_56, x_56);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_56);
lean_dec(x_54);
x_64 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_65 = l_Array_append___rarg(x_32, x_64);
x_66 = lean_array_to_list(lean_box(0), x_65);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_8);
lean_ctor_set(x_67, 1, x_19);
lean_ctor_set(x_67, 2, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_55);
return x_68;
}
else
{
size_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_70 = l_Lean_MVarId_rewrite___lambda__1___closed__1;
x_71 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_rewrite___spec__8(x_32, x_54, x_27, x_69, x_70);
lean_dec(x_54);
x_72 = l_Array_append___rarg(x_32, x_71);
x_73 = lean_array_to_list(lean_box(0), x_72);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_8);
lean_ctor_set(x_74, 1, x_19);
lean_ctor_set(x_74, 2, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_55);
return x_75;
}
}
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
x_85 = !lean_is_exclusive(x_23);
if (x_85 == 0)
{
return x_23;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_23, 0);
x_87 = lean_ctor_get(x_23, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_23);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_89 = !lean_is_exclusive(x_18);
if (x_89 == 0)
{
return x_18;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_18, 0);
x_91 = lean_ctor_get(x_18, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_18);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_93 = !lean_is_exclusive(x_15);
if (x_93 == 0)
{
return x_15;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_15, 0);
x_95 = lean_ctor_get(x_15, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_15);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
x_16 = lean_expr_instantiate1(x_1, x_2);
lean_dec(x_2);
x_17 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_16, x_11, x_12, x_13, x_14, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc_n(x_3, 2);
x_20 = l_Lean_Meta_mkEq(x_3, x_3, x_11, x_12, x_13, x_14, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Expr_appFn_x21(x_21);
lean_dec(x_21);
x_24 = l_Lean_Expr_app___override(x_23, x_1);
x_25 = l_Lean_MVarId_rewrite___lambda__2___closed__2;
x_26 = 0;
x_27 = l_Lean_Expr_lam___override(x_25, x_4, x_24, x_26);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_27);
x_28 = l_Lean_Meta_isTypeCorrect(x_27, x_11, x_12, x_13, x_14, x_22);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_MVarId_rewrite___lambda__2___closed__5;
x_33 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_7, x_32, x_11, x_12, x_13, x_14, x_31);
lean_dec(x_14);
lean_dec(x_12);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_dec(x_28);
x_39 = lean_box(0);
x_40 = l_Lean_MVarId_rewrite___lambda__10(x_3, x_27, x_5, x_6, x_7, x_8, x_9, x_18, x_39, x_11, x_12, x_13, x_14, x_38);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_28);
if (x_41 == 0)
{
return x_28;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_28, 0);
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_28);
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
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_20);
if (x_45 == 0)
{
return x_20;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_20, 0);
x_47 = lean_ctor_get(x_20, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_20);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_11);
x_17 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_1, x_12, x_13, x_14, x_15, x_16);
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_12, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_12, 3);
lean_inc(x_24);
x_25 = lean_ctor_get(x_12, 4);
lean_inc(x_25);
x_26 = lean_ctor_get(x_12, 5);
lean_inc(x_26);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_dec(x_2);
lean_ctor_set_uint8(x_18, 8, x_28);
lean_ctor_set_uint8(x_18, 9, x_29);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 3, x_24);
lean_ctor_set(x_30, 4, x_25);
lean_ctor_set(x_30, 5, x_26);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_3);
lean_inc(x_19);
x_31 = l_Lean_Meta_kabstract(x_19, x_3, x_21, x_30, x_13, x_14, x_15, x_20);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Expr_hasLooseBVars(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_32);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = l_Lean_indentExpr(x_3);
x_36 = l_Lean_MVarId_rewrite___lambda__3___closed__2;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_MVarId_rewrite___lambda__3___closed__4;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_8, x_39, x_12, x_13, x_14, x_15, x_33);
lean_dec(x_15);
lean_dec(x_13);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_3);
x_45 = lean_box(0);
x_46 = l_Lean_MVarId_rewrite___lambda__11(x_32, x_4, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_45, x_12, x_13, x_14, x_15, x_33);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_31);
if (x_47 == 0)
{
return x_31;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_31, 0);
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_31);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_51 = lean_ctor_get_uint8(x_18, 0);
x_52 = lean_ctor_get_uint8(x_18, 1);
x_53 = lean_ctor_get_uint8(x_18, 2);
x_54 = lean_ctor_get_uint8(x_18, 3);
x_55 = lean_ctor_get_uint8(x_18, 4);
x_56 = lean_ctor_get_uint8(x_18, 5);
x_57 = lean_ctor_get_uint8(x_18, 6);
x_58 = lean_ctor_get_uint8(x_18, 7);
x_59 = lean_ctor_get_uint8(x_18, 10);
x_60 = lean_ctor_get_uint8(x_18, 11);
lean_dec(x_18);
x_61 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_62 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_dec(x_2);
x_63 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_63, 0, x_51);
lean_ctor_set_uint8(x_63, 1, x_52);
lean_ctor_set_uint8(x_63, 2, x_53);
lean_ctor_set_uint8(x_63, 3, x_54);
lean_ctor_set_uint8(x_63, 4, x_55);
lean_ctor_set_uint8(x_63, 5, x_56);
lean_ctor_set_uint8(x_63, 6, x_57);
lean_ctor_set_uint8(x_63, 7, x_58);
lean_ctor_set_uint8(x_63, 8, x_61);
lean_ctor_set_uint8(x_63, 9, x_62);
lean_ctor_set_uint8(x_63, 10, x_59);
lean_ctor_set_uint8(x_63, 11, x_60);
x_64 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_22);
lean_ctor_set(x_64, 2, x_23);
lean_ctor_set(x_64, 3, x_24);
lean_ctor_set(x_64, 4, x_25);
lean_ctor_set(x_64, 5, x_26);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_3);
lean_inc(x_19);
x_65 = l_Lean_Meta_kabstract(x_19, x_3, x_21, x_64, x_13, x_14, x_15, x_20);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Expr_hasLooseBVars(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_66);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_69 = l_Lean_indentExpr(x_3);
x_70 = l_Lean_MVarId_rewrite___lambda__3___closed__2;
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_Lean_MVarId_rewrite___lambda__3___closed__4;
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_8, x_73, x_12, x_13, x_14, x_15, x_67);
lean_dec(x_15);
lean_dec(x_13);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_3);
x_79 = lean_box(0);
x_80 = l_Lean_MVarId_rewrite___lambda__11(x_66, x_4, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_79, x_12, x_13, x_14, x_15, x_67);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_81 = lean_ctor_get(x_65, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_65, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_83 = x_65;
} else {
 lean_dec_ref(x_65);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__13___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Iff", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__13___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_rewrite___lambda__13___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__13___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("equality or iff proof expected", 30);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__13___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lambda__13___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__13___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("pattern is a metavariable", 25);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__13___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lambda__13___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__13___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nfrom equation", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__13___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lambda__13___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__13___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("propext", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__13___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_rewrite___lambda__13___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lambda__13___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_rewrite___lambda__13___closed__10;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_9);
lean_inc(x_7);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
lean_inc(x_27);
x_30 = l_Lean_mkAppN(x_3, x_27);
x_31 = l_Lean_MVarId_rewrite___lambda__13___closed__2;
x_32 = lean_unsigned_to_nat(2u);
x_33 = l_Lean_Expr_isAppOfArity(x_29, x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_29);
x_34 = l_Lean_Meta_matchEq_x3f(x_29, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_indentExpr(x_29);
x_38 = l_Lean_MVarId_rewrite___lambda__13___closed__4;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_MVarId_rewrite___lambda__3___closed__4;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_41, x_7, x_8, x_9, x_10, x_36);
lean_dec(x_10);
lean_dec(x_8);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
lean_dec(x_35);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (x_4 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
lean_dec(x_34);
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = l_Lean_Expr_getAppFn(x_47);
x_50 = l_Lean_Expr_isMVar(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_29);
x_51 = lean_box(0);
x_52 = l_Lean_MVarId_rewrite___lambda__3(x_5, x_6, x_47, x_48, x_46, x_30, x_2, x_1, x_27, x_28, x_51, x_7, x_8, x_9, x_10, x_45);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec(x_48);
lean_dec(x_46);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
x_53 = l_Lean_indentExpr(x_47);
x_54 = l_Lean_MVarId_rewrite___lambda__13___closed__6;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_MVarId_rewrite___lambda__13___closed__8;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_indentExpr(x_29);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_MVarId_rewrite___lambda__3___closed__4;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_61, x_7, x_8, x_9, x_10, x_45);
lean_dec(x_10);
lean_dec(x_8);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
return x_62;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_62);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_29);
x_67 = lean_ctor_get(x_34, 1);
lean_inc(x_67);
lean_dec(x_34);
x_68 = lean_ctor_get(x_43, 0);
lean_inc(x_68);
lean_dec(x_43);
x_69 = lean_ctor_get(x_44, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_44, 1);
lean_inc(x_70);
lean_dec(x_44);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_71 = l_Lean_Meta_mkEqSymm(x_30, x_7, x_8, x_9, x_10, x_67);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_69);
lean_inc(x_70);
x_74 = l_Lean_Meta_mkEq(x_70, x_69, x_7, x_8, x_9, x_10, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Expr_getAppFn(x_70);
x_78 = l_Lean_Expr_isMVar(x_77);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_75);
x_79 = lean_box(0);
x_80 = l_Lean_MVarId_rewrite___lambda__6(x_5, x_6, x_70, x_69, x_68, x_72, x_2, x_1, x_27, x_28, x_79, x_7, x_8, x_9, x_10, x_76);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
lean_dec(x_72);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
x_81 = l_Lean_indentExpr(x_70);
x_82 = l_Lean_MVarId_rewrite___lambda__13___closed__6;
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = l_Lean_MVarId_rewrite___lambda__13___closed__8;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_indentExpr(x_75);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_MVarId_rewrite___lambda__3___closed__4;
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_89, x_7, x_8, x_9, x_10, x_76);
lean_dec(x_10);
lean_dec(x_8);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
return x_90;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_90);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_72);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_74);
if (x_95 == 0)
{
return x_74;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_74, 0);
x_97 = lean_ctor_get(x_74, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_74);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_71);
if (x_99 == 0)
{
return x_71;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_71, 0);
x_101 = lean_ctor_get(x_71, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_71);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_34);
if (x_103 == 0)
{
return x_34;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_34, 0);
x_105 = lean_ctor_get(x_34, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_34);
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
x_107 = l_Lean_Expr_appFn_x21(x_29);
x_108 = l_Lean_Expr_appArg_x21(x_107);
lean_dec(x_107);
x_109 = l_Lean_Expr_appArg_x21(x_29);
lean_dec(x_29);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_109);
lean_inc(x_108);
x_110 = l_Lean_Meta_mkEq(x_108, x_109, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = l_Lean_MVarId_rewrite___lambda__13___closed__11;
x_114 = l_Lean_mkApp3(x_113, x_108, x_109, x_30);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_111);
x_115 = l_Lean_Meta_matchEq_x3f(x_111, x_7, x_8, x_9, x_10, x_112);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_114);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = l_Lean_indentExpr(x_111);
x_119 = l_Lean_MVarId_rewrite___lambda__13___closed__4;
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
x_121 = l_Lean_MVarId_rewrite___lambda__3___closed__4;
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_122, x_7, x_8, x_9, x_10, x_117);
lean_dec(x_10);
lean_dec(x_8);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_116, 0);
lean_inc(x_124);
lean_dec(x_116);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
if (x_4 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_126 = lean_ctor_get(x_115, 1);
lean_inc(x_126);
lean_dec(x_115);
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
lean_dec(x_124);
x_128 = lean_ctor_get(x_125, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_125, 1);
lean_inc(x_129);
lean_dec(x_125);
x_130 = l_Lean_Expr_getAppFn(x_128);
x_131 = l_Lean_Expr_isMVar(x_130);
lean_dec(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_111);
x_132 = lean_box(0);
x_133 = l_Lean_MVarId_rewrite___lambda__9(x_5, x_6, x_128, x_129, x_127, x_114, x_2, x_1, x_27, x_28, x_132, x_7, x_8, x_9, x_10, x_126);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_114);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
x_134 = l_Lean_indentExpr(x_128);
x_135 = l_Lean_MVarId_rewrite___lambda__13___closed__6;
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_134);
x_137 = l_Lean_MVarId_rewrite___lambda__13___closed__8;
x_138 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = l_Lean_indentExpr(x_111);
x_140 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_141 = l_Lean_MVarId_rewrite___lambda__3___closed__4;
x_142 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_142, x_7, x_8, x_9, x_10, x_126);
lean_dec(x_10);
lean_dec(x_8);
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
return x_143;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_143, 0);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_143);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_111);
x_148 = lean_ctor_get(x_115, 1);
lean_inc(x_148);
lean_dec(x_115);
x_149 = lean_ctor_get(x_124, 0);
lean_inc(x_149);
lean_dec(x_124);
x_150 = lean_ctor_get(x_125, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_125, 1);
lean_inc(x_151);
lean_dec(x_125);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_152 = l_Lean_Meta_mkEqSymm(x_114, x_7, x_8, x_9, x_10, x_148);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_150);
lean_inc(x_151);
x_155 = l_Lean_Meta_mkEq(x_151, x_150, x_7, x_8, x_9, x_10, x_154);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = l_Lean_Expr_getAppFn(x_151);
x_159 = l_Lean_Expr_isMVar(x_158);
lean_dec(x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_156);
x_160 = lean_box(0);
x_161 = l_Lean_MVarId_rewrite___lambda__12(x_5, x_6, x_151, x_150, x_149, x_153, x_2, x_1, x_27, x_28, x_160, x_7, x_8, x_9, x_10, x_157);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
lean_dec(x_153);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
x_162 = l_Lean_indentExpr(x_151);
x_163 = l_Lean_MVarId_rewrite___lambda__13___closed__6;
x_164 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
x_165 = l_Lean_MVarId_rewrite___lambda__13___closed__8;
x_166 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lean_indentExpr(x_156);
x_168 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = l_Lean_MVarId_rewrite___lambda__3___closed__4;
x_170 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
x_171 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_170, x_7, x_8, x_9, x_10, x_157);
lean_dec(x_10);
lean_dec(x_8);
x_172 = !lean_is_exclusive(x_171);
if (x_172 == 0)
{
return x_171;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_171, 0);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_171);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_176 = !lean_is_exclusive(x_155);
if (x_176 == 0)
{
return x_155;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_155, 0);
x_178 = lean_ctor_get(x_155, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_155);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
else
{
uint8_t x_180; 
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_180 = !lean_is_exclusive(x_152);
if (x_180 == 0)
{
return x_152;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_152, 0);
x_182 = lean_ctor_get(x_152, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_152);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_114);
lean_dec(x_111);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_184 = !lean_is_exclusive(x_115);
if (x_184 == 0)
{
return x_115;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_115, 0);
x_186 = lean_ctor_get(x_115, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_115);
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
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_188 = !lean_is_exclusive(x_110);
if (x_188 == 0)
{
return x_110;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_110, 0);
x_190 = lean_ctor_get(x_110, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_110);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_192 = !lean_is_exclusive(x_23);
if (x_192 == 0)
{
return x_23;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_23, 0);
x_194 = lean_ctor_get(x_23, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_23);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_196 = !lean_is_exclusive(x_14);
if (x_196 == 0)
{
return x_14;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_14, 0);
x_198 = lean_ctor_get(x_14, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_14);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
else
{
uint8_t x_200; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_200 = !lean_is_exclusive(x_12);
if (x_200 == 0)
{
return x_12;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_12, 0);
x_202 = lean_ctor_get(x_12, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_12);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rewrite", 7);
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
x_13 = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lambda__13___boxed), 11, 6);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_MVarId_rewrite___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_MVarId_rewrite___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_MVarId_rewrite___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_MVarId_rewrite___lambda__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lambda__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_MVarId_rewrite___lambda__13(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Meta_rewrite(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_rewrite(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rewrite___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Meta_rewrite(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_KAbstract(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_MVarId_rewrite___lambda__1___closed__1 = _init_l_Lean_MVarId_rewrite___lambda__1___closed__1();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__1___closed__1);
l_Lean_MVarId_rewrite___lambda__2___closed__1 = _init_l_Lean_MVarId_rewrite___lambda__2___closed__1();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__2___closed__1);
l_Lean_MVarId_rewrite___lambda__2___closed__2 = _init_l_Lean_MVarId_rewrite___lambda__2___closed__2();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__2___closed__2);
l_Lean_MVarId_rewrite___lambda__2___closed__3 = _init_l_Lean_MVarId_rewrite___lambda__2___closed__3();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__2___closed__3);
l_Lean_MVarId_rewrite___lambda__2___closed__4 = _init_l_Lean_MVarId_rewrite___lambda__2___closed__4();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__2___closed__4);
l_Lean_MVarId_rewrite___lambda__2___closed__5 = _init_l_Lean_MVarId_rewrite___lambda__2___closed__5();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__2___closed__5);
l_Lean_MVarId_rewrite___lambda__3___closed__1 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__1();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__1);
l_Lean_MVarId_rewrite___lambda__3___closed__2 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__2();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__2);
l_Lean_MVarId_rewrite___lambda__3___closed__3 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__3();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__3);
l_Lean_MVarId_rewrite___lambda__3___closed__4 = _init_l_Lean_MVarId_rewrite___lambda__3___closed__4();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__3___closed__4);
l_Lean_MVarId_rewrite___lambda__13___closed__1 = _init_l_Lean_MVarId_rewrite___lambda__13___closed__1();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__13___closed__1);
l_Lean_MVarId_rewrite___lambda__13___closed__2 = _init_l_Lean_MVarId_rewrite___lambda__13___closed__2();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__13___closed__2);
l_Lean_MVarId_rewrite___lambda__13___closed__3 = _init_l_Lean_MVarId_rewrite___lambda__13___closed__3();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__13___closed__3);
l_Lean_MVarId_rewrite___lambda__13___closed__4 = _init_l_Lean_MVarId_rewrite___lambda__13___closed__4();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__13___closed__4);
l_Lean_MVarId_rewrite___lambda__13___closed__5 = _init_l_Lean_MVarId_rewrite___lambda__13___closed__5();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__13___closed__5);
l_Lean_MVarId_rewrite___lambda__13___closed__6 = _init_l_Lean_MVarId_rewrite___lambda__13___closed__6();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__13___closed__6);
l_Lean_MVarId_rewrite___lambda__13___closed__7 = _init_l_Lean_MVarId_rewrite___lambda__13___closed__7();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__13___closed__7);
l_Lean_MVarId_rewrite___lambda__13___closed__8 = _init_l_Lean_MVarId_rewrite___lambda__13___closed__8();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__13___closed__8);
l_Lean_MVarId_rewrite___lambda__13___closed__9 = _init_l_Lean_MVarId_rewrite___lambda__13___closed__9();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__13___closed__9);
l_Lean_MVarId_rewrite___lambda__13___closed__10 = _init_l_Lean_MVarId_rewrite___lambda__13___closed__10();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__13___closed__10);
l_Lean_MVarId_rewrite___lambda__13___closed__11 = _init_l_Lean_MVarId_rewrite___lambda__13___closed__11();
lean_mark_persistent(l_Lean_MVarId_rewrite___lambda__13___closed__11);
l_Lean_MVarId_rewrite___closed__1 = _init_l_Lean_MVarId_rewrite___closed__1();
lean_mark_persistent(l_Lean_MVarId_rewrite___closed__1);
l_Lean_MVarId_rewrite___closed__2 = _init_l_Lean_MVarId_rewrite___closed__2();
lean_mark_persistent(l_Lean_MVarId_rewrite___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
