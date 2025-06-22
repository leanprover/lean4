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
lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__37;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__39;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__35;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__31;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__0;
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__27;
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__20;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__7;
lean_object* l_Lean_Expr_resolveBinderNameHint(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__32;
lean_object* l_Lean_Meta_postprocessAppMVars(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__17;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__9;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__11;
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__14;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__36;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__8;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__38;
uint8_t l_Lean_Expr_hasBinderNameHint(lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_MVarId_rewrite_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__21;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___Lean_MVarId_rewrite_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__29;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__26;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__28;
extern lean_object* l_Lean_Meta_tactic_skipAssignedInstances;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__6;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__4;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__12;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__34;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__18;
static lean_object* l_Lean_MVarId_rewrite___closed__0;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__15;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__23;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_MVarId_rewrite_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__24;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__22;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__13;
LEAN_EXPORT uint8_t l_Array_contains___at___Lean_MVarId_rewrite_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__16;
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_MVarId_applyN_spec__0(size_t, size_t, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__5;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__33;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___closed__1;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__25;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__30;
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__3;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__10;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_rewrite___lam__1___closed__19;
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_MVarId_rewrite_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
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
return x_7;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___Lean_MVarId_rewrite_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = 0;
x_7 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_MVarId_rewrite_spec__0_spec__0(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_2, x_3);
x_13 = l_Array_contains___at___Lean_MVarId_rewrite_spec__0(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_array_push(x_5, x_12);
x_6 = x_14;
goto block_10;
}
else
{
lean_dec(x_12);
x_6 = x_5;
goto block_10;
}
}
else
{
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__3___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_2, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_array_uget(x_1, x_2);
x_18 = l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0___redArg(x_14, x_5, x_6);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_15 = x_21;
goto block_17;
}
else
{
lean_object* x_22; 
lean_dec(x_14);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_7 = x_4;
x_8 = x_22;
goto block_12;
}
block_17:
{
lean_object* x_16; 
x_16 = lean_array_push(x_4, x_14);
x_7 = x_16;
x_8 = x_15;
goto block_12;
}
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_7;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__3___redArg(x_1, x_2, x_3, x_4, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("motive is dependent", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congrArg", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__5;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_tactic_skipAssignedInstances;
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("motive is not type correct:", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nError: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\nExplanation: The rewrite tactic rewrites an expression 'e' using an equality 'a = b' by the following process. First, it looks for all 'a' in 'e'. Second, it tries to abstract these occurrences of 'a' to create a function 'm := fun _a => ...', called the *motive*, with the property that 'm a' is definitionally equal to 'e'. Third, we observe that '", 352, 352);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' implies that 'm a = m b', which can be used with lemmas such as '", 67, 67);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__14;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mpr", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__17;
x_2 = l_Lean_MVarId_rewrite___lam__1___closed__16;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' to change the goal. However, if 'e' depends on specific properties of 'a', then the motive 'm' might not typecheck.\n\nPossible solutions: use rewrite's 'occs' configuration option to limit which occurrences are rewritten, or use 'simp' or 'conv' mode, which have strategies for certain kinds of dependencies (these tactics can handle proofs and '", 347, 347);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__19;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Decidable", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__21;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' instances whose types depend on the rewritten term, and 'simp' can apply user-defined '@[congr]' theorems as well).", 117, 117);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__23;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_a", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__25;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("did not find instance of the pattern in the target expression", 61, 61);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__27;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pattern is a metavariable", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__29;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nfrom equation", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__31;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("equality or iff proof expected", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__33;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Iff", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__35;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("propext", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___lam__1___closed__37;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___lam__1___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_rewrite___lam__1___closed__38;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_42; 
lean_inc(x_2);
lean_inc(x_1);
x_42 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_44 = lean_infer_type(x_3, x_7, x_8, x_9, x_10, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_45, x_8, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = lean_box(0);
x_52 = lean_box(0);
x_53 = lean_unbox(x_52);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_54 = l_Lean_Meta_forallMetaTelescopeReducing(x_48, x_51, x_53, x_7, x_8, x_9, x_10, x_49);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_475; lean_object* x_476; lean_object* x_477; uint8_t x_478; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_59 = x_55;
} else {
 lean_dec_ref(x_55);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_56, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_62 = x_56;
} else {
 lean_dec_ref(x_56);
 x_62 = lean_box(0);
}
lean_inc(x_3);
x_475 = l_Lean_mkAppN(x_3, x_58);
x_476 = l_Lean_MVarId_rewrite___lam__1___closed__36;
x_477 = lean_unsigned_to_nat(2u);
x_478 = l_Lean_Expr_isAppOfArity(x_61, x_476, x_477);
if (x_478 == 0)
{
x_429 = x_475;
x_430 = x_61;
x_431 = x_7;
x_432 = x_8;
x_433 = x_9;
x_434 = x_10;
x_435 = x_57;
goto block_474;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_479 = l_Lean_Expr_appFn_x21(x_61);
x_480 = l_Lean_Expr_appArg_x21(x_479);
lean_dec(x_479);
x_481 = l_Lean_Expr_appArg_x21(x_61);
lean_dec(x_61);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_481);
lean_inc(x_480);
x_482 = l_Lean_Meta_mkEq(x_480, x_481, x_7, x_8, x_9, x_10, x_57);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_482, 1);
lean_inc(x_484);
lean_dec(x_482);
x_485 = l_Lean_MVarId_rewrite___lam__1___closed__39;
x_486 = l_Lean_mkApp3(x_485, x_480, x_481, x_475);
x_429 = x_486;
x_430 = x_483;
x_431 = x_7;
x_432 = x_8;
x_433 = x_9;
x_434 = x_10;
x_435 = x_484;
goto block_474;
}
else
{
uint8_t x_487; 
lean_dec(x_481);
lean_dec(x_480);
lean_dec(x_475);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_487 = !lean_is_exclusive(x_482);
if (x_487 == 0)
{
return x_482;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_488 = lean_ctor_get(x_482, 0);
x_489 = lean_ctor_get(x_482, 1);
lean_inc(x_489);
lean_inc(x_488);
lean_dec(x_482);
x_490 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_490, 0, x_488);
lean_ctor_set(x_490, 1, x_489);
return x_490;
}
}
}
block_91:
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_71 = lean_box(0);
x_72 = lean_unbox(x_71);
lean_inc(x_68);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_69);
x_73 = l_Lean_Meta_postprocessAppMVars(x_2, x_1, x_58, x_60, x_70, x_72, x_69, x_64, x_65, x_68, x_63);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; size_t x_75; size_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_array_size(x_58);
x_76 = 0;
x_77 = l_Array_mapMUnsafe_map___at___Lean_MVarId_applyN_spec__0(x_75, x_76, x_58);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_array_get_size(x_77);
x_80 = l_Lean_MVarId_rewrite___lam__1___closed__0;
x_81 = lean_nat_dec_lt(x_78, x_79);
if (x_81 == 0)
{
lean_dec(x_79);
lean_dec(x_77);
x_22 = x_78;
x_23 = x_64;
x_24 = x_76;
x_25 = x_65;
x_26 = x_67;
x_27 = x_66;
x_28 = x_68;
x_29 = x_69;
x_30 = x_80;
x_31 = x_74;
goto block_41;
}
else
{
uint8_t x_82; 
x_82 = lean_nat_dec_le(x_79, x_79);
if (x_82 == 0)
{
lean_dec(x_79);
lean_dec(x_77);
x_22 = x_78;
x_23 = x_64;
x_24 = x_76;
x_25 = x_65;
x_26 = x_67;
x_27 = x_66;
x_28 = x_68;
x_29 = x_69;
x_30 = x_80;
x_31 = x_74;
goto block_41;
}
else
{
size_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_usize_of_nat(x_79);
lean_dec(x_79);
x_84 = l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__3___redArg(x_77, x_76, x_83, x_80, x_64, x_74);
lean_dec(x_77);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_22 = x_78;
x_23 = x_64;
x_24 = x_76;
x_25 = x_65;
x_26 = x_67;
x_27 = x_66;
x_28 = x_68;
x_29 = x_69;
x_30 = x_85;
x_31 = x_86;
goto block_41;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_58);
lean_dec(x_3);
x_87 = !lean_is_exclusive(x_73);
if (x_87 == 0)
{
return x_73;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_73, 0);
x_89 = lean_ctor_get(x_73, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_73);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
block_158:
{
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
lean_inc(x_100);
lean_inc(x_96);
lean_inc(x_94);
lean_inc(x_102);
lean_inc(x_98);
x_107 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__2___redArg(x_104, x_98, x_103, x_102, x_94, x_96, x_100, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_unbox(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
lean_dec(x_108);
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_95);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_3);
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
lean_dec(x_107);
x_111 = l_Lean_MVarId_rewrite___lam__1___closed__2;
x_112 = l_Lean_MessageData_ofExpr(x_97);
x_113 = l_Lean_indentD(x_112);
if (lean_is_scalar(x_62)) {
 x_114 = lean_alloc_ctor(7, 2, 0);
} else {
 x_114 = x_62;
 lean_ctor_set_tag(x_114, 7);
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_MVarId_rewrite___lam__1___closed__4;
if (lean_is_scalar(x_59)) {
 x_116 = lean_alloc_ctor(7, 2, 0);
} else {
 x_116 = x_59;
 lean_ctor_set_tag(x_116, 7);
}
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_117, x_102, x_94, x_96, x_100, x_110);
lean_dec(x_100);
lean_dec(x_96);
lean_dec(x_94);
lean_dec(x_102);
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
return x_118;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_118);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_107, 1);
lean_inc(x_123);
lean_dec(x_107);
lean_inc(x_100);
lean_inc(x_96);
lean_inc(x_94);
lean_inc(x_102);
lean_inc(x_98);
x_124 = l_Lean_Meta_getLevel(x_98, x_102, x_94, x_96, x_100, x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
lean_inc(x_100);
lean_inc(x_96);
lean_inc(x_94);
lean_inc(x_102);
lean_inc(x_101);
x_127 = l_Lean_Meta_getLevel(x_101, x_102, x_94, x_96, x_100, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_ctor_get(x_96, 2);
lean_inc(x_130);
x_131 = l_Lean_MVarId_rewrite___lam__1___closed__6;
x_132 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_62;
 lean_ctor_set_tag(x_133, 1);
}
lean_ctor_set(x_133, 0, x_128);
lean_ctor_set(x_133, 1, x_132);
if (lean_is_scalar(x_59)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_59;
 lean_ctor_set_tag(x_134, 1);
}
lean_ctor_set(x_134, 0, x_125);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Lean_Expr_const___override(x_131, x_134);
x_136 = l_Lean_mkApp6(x_135, x_98, x_101, x_99, x_92, x_97, x_93);
x_137 = l_Lean_MVarId_rewrite___lam__1___closed__7;
x_138 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_130, x_137);
lean_dec(x_130);
if (x_138 == 0)
{
uint8_t x_139; 
x_139 = lean_unbox(x_108);
lean_dec(x_108);
x_63 = x_129;
x_64 = x_94;
x_65 = x_96;
x_66 = x_136;
x_67 = x_95;
x_68 = x_100;
x_69 = x_102;
x_70 = x_139;
goto block_91;
}
else
{
lean_object* x_140; uint8_t x_141; 
lean_dec(x_108);
x_140 = lean_box(0);
x_141 = lean_unbox(x_140);
x_63 = x_129;
x_64 = x_94;
x_65 = x_96;
x_66 = x_136;
x_67 = x_95;
x_68 = x_100;
x_69 = x_102;
x_70 = x_141;
goto block_91;
}
}
else
{
uint8_t x_142; 
lean_dec(x_125);
lean_dec(x_108);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_142 = !lean_is_exclusive(x_127);
if (x_142 == 0)
{
return x_127;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_127, 0);
x_144 = lean_ctor_get(x_127, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_127);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
uint8_t x_146; 
lean_dec(x_108);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_146 = !lean_is_exclusive(x_124);
if (x_146 == 0)
{
return x_124;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_124, 0);
x_148 = lean_ctor_get(x_124, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_124);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_150 = !lean_is_exclusive(x_107);
if (x_150 == 0)
{
return x_107;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_107, 0);
x_152 = lean_ctor_get(x_107, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_107);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_154 = !lean_is_exclusive(x_105);
if (x_154 == 0)
{
return x_105;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_105, 0);
x_156 = lean_ctor_get(x_105, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_105);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
block_203:
{
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_170);
x_176 = l_Lean_MVarId_rewrite___lam__1___closed__9;
lean_inc(x_164);
x_177 = l_Lean_MessageData_ofExpr(x_164);
x_178 = l_Lean_indentD(x_177);
if (lean_is_scalar(x_50)) {
 x_179 = lean_alloc_ctor(7, 2, 0);
} else {
 x_179 = x_50;
 lean_ctor_set_tag(x_179, 7);
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_178);
x_180 = l_Lean_MVarId_rewrite___lam__1___closed__11;
x_181 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_182 = l_Lean_Exception_toMessageData(x_167);
x_183 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = l_Lean_MVarId_rewrite___lam__1___closed__13;
x_185 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
x_186 = l_Lean_MVarId_rewrite___lam__1___closed__6;
x_187 = l_Lean_MessageData_ofConstName(x_186, x_175);
x_188 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_187);
x_189 = l_Lean_MVarId_rewrite___lam__1___closed__15;
x_190 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = l_Lean_MVarId_rewrite___lam__1___closed__18;
x_192 = l_Lean_MessageData_ofConstName(x_191, x_175);
x_193 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_192);
x_194 = l_Lean_MVarId_rewrite___lam__1___closed__20;
x_195 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
x_196 = l_Lean_MVarId_rewrite___lam__1___closed__22;
x_197 = l_Lean_MessageData_ofConstName(x_196, x_175);
x_198 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_197);
x_199 = l_Lean_MVarId_rewrite___lam__1___closed__24;
x_200 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_200);
lean_inc(x_1);
lean_inc(x_2);
x_202 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_201, x_172, x_161, x_163, x_169, x_168);
x_92 = x_159;
x_93 = x_160;
x_94 = x_161;
x_95 = x_162;
x_96 = x_163;
x_97 = x_164;
x_98 = x_165;
x_99 = x_166;
x_100 = x_169;
x_101 = x_171;
x_102 = x_172;
x_103 = x_173;
x_104 = x_174;
x_105 = x_202;
goto block_158;
}
else
{
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_50);
x_92 = x_159;
x_93 = x_160;
x_94 = x_161;
x_95 = x_162;
x_96 = x_163;
x_97 = x_164;
x_98 = x_165;
x_99 = x_166;
x_100 = x_169;
x_101 = x_171;
x_102 = x_172;
x_103 = x_173;
x_104 = x_174;
x_105 = x_170;
goto block_158;
}
}
block_234:
{
lean_object* x_217; 
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
x_217 = lean_infer_type(x_208, x_212, x_213, x_214, x_215, x_216);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
lean_inc(x_218);
x_220 = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lam__0___boxed), 8, 2);
lean_closure_set(x_220, 0, x_204);
lean_closure_set(x_220, 1, x_218);
x_221 = l_Lean_MVarId_rewrite___lam__1___closed__26;
x_222 = lean_box(0);
x_223 = lean_unbox(x_222);
lean_inc(x_206);
x_224 = l_Lean_Expr_lam___override(x_221, x_206, x_210, x_223);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_224);
x_225 = l_Lean_Meta_check(x_224, x_212, x_213, x_214, x_215, x_219);
if (lean_obj_tag(x_225) == 0)
{
lean_dec(x_50);
x_92 = x_207;
x_93 = x_209;
x_94 = x_213;
x_95 = x_211;
x_96 = x_214;
x_97 = x_224;
x_98 = x_206;
x_99 = x_205;
x_100 = x_215;
x_101 = x_218;
x_102 = x_212;
x_103 = x_220;
x_104 = x_221;
x_105 = x_225;
goto block_158;
}
else
{
lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
x_228 = l_Lean_Exception_isInterrupt(x_226);
if (x_228 == 0)
{
uint8_t x_229; 
x_229 = l_Lean_Exception_isRuntime(x_226);
x_159 = x_207;
x_160 = x_209;
x_161 = x_213;
x_162 = x_211;
x_163 = x_214;
x_164 = x_224;
x_165 = x_206;
x_166 = x_205;
x_167 = x_226;
x_168 = x_227;
x_169 = x_215;
x_170 = x_225;
x_171 = x_218;
x_172 = x_212;
x_173 = x_220;
x_174 = x_221;
x_175 = x_229;
goto block_203;
}
else
{
x_159 = x_207;
x_160 = x_209;
x_161 = x_213;
x_162 = x_211;
x_163 = x_214;
x_164 = x_224;
x_165 = x_206;
x_166 = x_205;
x_167 = x_226;
x_168 = x_227;
x_169 = x_215;
x_170 = x_225;
x_171 = x_218;
x_172 = x_212;
x_173 = x_220;
x_174 = x_221;
x_175 = x_228;
goto block_203;
}
}
}
else
{
uint8_t x_230; 
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_230 = !lean_is_exclusive(x_217);
if (x_230 == 0)
{
return x_217;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_217, 0);
x_232 = lean_ctor_get(x_217, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_217);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
block_428:
{
lean_object* x_245; uint8_t x_246; 
x_245 = l_Lean_Expr_getAppFn(x_238);
x_246 = l_Lean_Expr_isMVar(x_245);
lean_dec(x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; uint8_t x_249; 
lean_dec(x_237);
x_247 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_4, x_241, x_244);
x_248 = lean_ctor_get(x_240, 0);
lean_inc(x_248);
x_249 = !lean_is_exclusive(x_247);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; uint8_t x_252; uint8_t x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_250 = lean_ctor_get(x_247, 0);
x_251 = lean_ctor_get(x_247, 1);
x_252 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_253 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_254 = lean_ctor_get(x_5, 0);
lean_inc(x_254);
lean_dec(x_5);
x_255 = lean_ctor_get_uint8(x_240, sizeof(void*)*7 + 8);
x_256 = lean_ctor_get(x_240, 1);
lean_inc(x_256);
x_257 = lean_ctor_get(x_240, 2);
lean_inc(x_257);
x_258 = lean_ctor_get(x_240, 3);
lean_inc(x_258);
x_259 = lean_ctor_get(x_240, 4);
lean_inc(x_259);
x_260 = lean_ctor_get(x_240, 5);
lean_inc(x_260);
x_261 = lean_ctor_get(x_240, 6);
lean_inc(x_261);
x_262 = !lean_is_exclusive(x_248);
if (x_262 == 0)
{
uint8_t x_263; uint8_t x_264; uint64_t x_265; lean_object* x_266; lean_object* x_267; 
x_263 = lean_ctor_get_uint8(x_240, sizeof(void*)*7 + 9);
x_264 = lean_ctor_get_uint8(x_240, sizeof(void*)*7 + 10);
lean_ctor_set_uint8(x_248, 8, x_253);
lean_ctor_set_uint8(x_248, 9, x_252);
x_265 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_248);
x_266 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_266, 0, x_248);
lean_ctor_set(x_266, 1, x_256);
lean_ctor_set(x_266, 2, x_257);
lean_ctor_set(x_266, 3, x_258);
lean_ctor_set(x_266, 4, x_259);
lean_ctor_set(x_266, 5, x_260);
lean_ctor_set(x_266, 6, x_261);
lean_ctor_set_uint64(x_266, sizeof(void*)*7, x_265);
lean_ctor_set_uint8(x_266, sizeof(void*)*7 + 8, x_255);
lean_ctor_set_uint8(x_266, sizeof(void*)*7 + 9, x_263);
lean_ctor_set_uint8(x_266, sizeof(void*)*7 + 10, x_264);
lean_inc(x_243);
lean_inc(x_242);
lean_inc(x_241);
lean_inc(x_238);
lean_inc(x_250);
x_267 = l_Lean_Meta_kabstract(x_250, x_238, x_254, x_266, x_241, x_242, x_243, x_251);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec(x_267);
x_270 = l_Lean_Expr_hasLooseBVars(x_268);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
lean_dec(x_268);
lean_dec(x_250);
lean_dec(x_239);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_3);
x_271 = l_Lean_MVarId_rewrite___lam__1___closed__28;
x_272 = l_Lean_indentExpr(x_238);
lean_ctor_set_tag(x_247, 7);
lean_ctor_set(x_247, 1, x_272);
lean_ctor_set(x_247, 0, x_271);
x_273 = l_Lean_MVarId_rewrite___lam__1___closed__4;
x_274 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_274, 0, x_247);
lean_ctor_set(x_274, 1, x_273);
x_275 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_275, 0, x_274);
x_276 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_275, x_240, x_241, x_242, x_243, x_269);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
x_277 = !lean_is_exclusive(x_276);
if (x_277 == 0)
{
return x_276;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_276, 0);
x_279 = lean_ctor_get(x_276, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_276);
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
return x_280;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; 
lean_free_object(x_247);
x_281 = lean_expr_instantiate1(x_268, x_239);
x_282 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_281, x_241, x_269);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_285 = l_Lean_Expr_hasBinderNameHint(x_239);
if (x_285 == 0)
{
lean_inc(x_268);
x_204 = x_268;
x_205 = x_238;
x_206 = x_235;
x_207 = x_239;
x_208 = x_250;
x_209 = x_236;
x_210 = x_268;
x_211 = x_283;
x_212 = x_240;
x_213 = x_241;
x_214 = x_242;
x_215 = x_243;
x_216 = x_284;
goto block_234;
}
else
{
lean_object* x_286; 
lean_inc(x_243);
lean_inc(x_242);
x_286 = l_Lean_Expr_resolveBinderNameHint(x_283, x_242, x_243, x_284);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
lean_inc(x_268);
x_204 = x_268;
x_205 = x_238;
x_206 = x_235;
x_207 = x_239;
x_208 = x_250;
x_209 = x_236;
x_210 = x_268;
x_211 = x_287;
x_212 = x_240;
x_213 = x_241;
x_214 = x_242;
x_215 = x_243;
x_216 = x_288;
goto block_234;
}
else
{
uint8_t x_289; 
lean_dec(x_268);
lean_dec(x_250);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_289 = !lean_is_exclusive(x_286);
if (x_289 == 0)
{
return x_286;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_286, 0);
x_291 = lean_ctor_get(x_286, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_286);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
}
}
}
}
else
{
uint8_t x_293; 
lean_free_object(x_247);
lean_dec(x_250);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_293 = !lean_is_exclusive(x_267);
if (x_293 == 0)
{
return x_267;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_267, 0);
x_295 = lean_ctor_get(x_267, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_267);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
return x_296;
}
}
}
else
{
uint8_t x_297; uint8_t x_298; uint8_t x_299; uint8_t x_300; uint8_t x_301; uint8_t x_302; uint8_t x_303; uint8_t x_304; uint8_t x_305; uint8_t x_306; uint8_t x_307; uint8_t x_308; uint8_t x_309; uint8_t x_310; uint8_t x_311; uint8_t x_312; uint8_t x_313; uint8_t x_314; lean_object* x_315; uint64_t x_316; lean_object* x_317; lean_object* x_318; 
x_297 = lean_ctor_get_uint8(x_240, sizeof(void*)*7 + 9);
x_298 = lean_ctor_get_uint8(x_240, sizeof(void*)*7 + 10);
x_299 = lean_ctor_get_uint8(x_248, 0);
x_300 = lean_ctor_get_uint8(x_248, 1);
x_301 = lean_ctor_get_uint8(x_248, 2);
x_302 = lean_ctor_get_uint8(x_248, 3);
x_303 = lean_ctor_get_uint8(x_248, 4);
x_304 = lean_ctor_get_uint8(x_248, 5);
x_305 = lean_ctor_get_uint8(x_248, 6);
x_306 = lean_ctor_get_uint8(x_248, 7);
x_307 = lean_ctor_get_uint8(x_248, 10);
x_308 = lean_ctor_get_uint8(x_248, 11);
x_309 = lean_ctor_get_uint8(x_248, 12);
x_310 = lean_ctor_get_uint8(x_248, 13);
x_311 = lean_ctor_get_uint8(x_248, 14);
x_312 = lean_ctor_get_uint8(x_248, 15);
x_313 = lean_ctor_get_uint8(x_248, 16);
x_314 = lean_ctor_get_uint8(x_248, 17);
lean_dec(x_248);
x_315 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_315, 0, x_299);
lean_ctor_set_uint8(x_315, 1, x_300);
lean_ctor_set_uint8(x_315, 2, x_301);
lean_ctor_set_uint8(x_315, 3, x_302);
lean_ctor_set_uint8(x_315, 4, x_303);
lean_ctor_set_uint8(x_315, 5, x_304);
lean_ctor_set_uint8(x_315, 6, x_305);
lean_ctor_set_uint8(x_315, 7, x_306);
lean_ctor_set_uint8(x_315, 8, x_253);
lean_ctor_set_uint8(x_315, 9, x_252);
lean_ctor_set_uint8(x_315, 10, x_307);
lean_ctor_set_uint8(x_315, 11, x_308);
lean_ctor_set_uint8(x_315, 12, x_309);
lean_ctor_set_uint8(x_315, 13, x_310);
lean_ctor_set_uint8(x_315, 14, x_311);
lean_ctor_set_uint8(x_315, 15, x_312);
lean_ctor_set_uint8(x_315, 16, x_313);
lean_ctor_set_uint8(x_315, 17, x_314);
x_316 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_315);
x_317 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_256);
lean_ctor_set(x_317, 2, x_257);
lean_ctor_set(x_317, 3, x_258);
lean_ctor_set(x_317, 4, x_259);
lean_ctor_set(x_317, 5, x_260);
lean_ctor_set(x_317, 6, x_261);
lean_ctor_set_uint64(x_317, sizeof(void*)*7, x_316);
lean_ctor_set_uint8(x_317, sizeof(void*)*7 + 8, x_255);
lean_ctor_set_uint8(x_317, sizeof(void*)*7 + 9, x_297);
lean_ctor_set_uint8(x_317, sizeof(void*)*7 + 10, x_298);
lean_inc(x_243);
lean_inc(x_242);
lean_inc(x_241);
lean_inc(x_238);
lean_inc(x_250);
x_318 = l_Lean_Meta_kabstract(x_250, x_238, x_254, x_317, x_241, x_242, x_243, x_251);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; uint8_t x_321; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec(x_318);
x_321 = l_Lean_Expr_hasLooseBVars(x_319);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_319);
lean_dec(x_250);
lean_dec(x_239);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_3);
x_322 = l_Lean_MVarId_rewrite___lam__1___closed__28;
x_323 = l_Lean_indentExpr(x_238);
lean_ctor_set_tag(x_247, 7);
lean_ctor_set(x_247, 1, x_323);
lean_ctor_set(x_247, 0, x_322);
x_324 = l_Lean_MVarId_rewrite___lam__1___closed__4;
x_325 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_325, 0, x_247);
lean_ctor_set(x_325, 1, x_324);
x_326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_326, 0, x_325);
x_327 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_326, x_240, x_241, x_242, x_243, x_320);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_330 = x_327;
} else {
 lean_dec_ref(x_327);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(1, 2, 0);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_328);
lean_ctor_set(x_331, 1, x_329);
return x_331;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; 
lean_free_object(x_247);
x_332 = lean_expr_instantiate1(x_319, x_239);
x_333 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_332, x_241, x_320);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_333, 1);
lean_inc(x_335);
lean_dec(x_333);
x_336 = l_Lean_Expr_hasBinderNameHint(x_239);
if (x_336 == 0)
{
lean_inc(x_319);
x_204 = x_319;
x_205 = x_238;
x_206 = x_235;
x_207 = x_239;
x_208 = x_250;
x_209 = x_236;
x_210 = x_319;
x_211 = x_334;
x_212 = x_240;
x_213 = x_241;
x_214 = x_242;
x_215 = x_243;
x_216 = x_335;
goto block_234;
}
else
{
lean_object* x_337; 
lean_inc(x_243);
lean_inc(x_242);
x_337 = l_Lean_Expr_resolveBinderNameHint(x_334, x_242, x_243, x_335);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
lean_inc(x_319);
x_204 = x_319;
x_205 = x_238;
x_206 = x_235;
x_207 = x_239;
x_208 = x_250;
x_209 = x_236;
x_210 = x_319;
x_211 = x_338;
x_212 = x_240;
x_213 = x_241;
x_214 = x_242;
x_215 = x_243;
x_216 = x_339;
goto block_234;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_dec(x_319);
lean_dec(x_250);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_340 = lean_ctor_get(x_337, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_337, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_342 = x_337;
} else {
 lean_dec_ref(x_337);
 x_342 = lean_box(0);
}
if (lean_is_scalar(x_342)) {
 x_343 = lean_alloc_ctor(1, 2, 0);
} else {
 x_343 = x_342;
}
lean_ctor_set(x_343, 0, x_340);
lean_ctor_set(x_343, 1, x_341);
return x_343;
}
}
}
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
lean_free_object(x_247);
lean_dec(x_250);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_344 = lean_ctor_get(x_318, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_318, 1);
lean_inc(x_345);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_346 = x_318;
} else {
 lean_dec_ref(x_318);
 x_346 = lean_box(0);
}
if (lean_is_scalar(x_346)) {
 x_347 = lean_alloc_ctor(1, 2, 0);
} else {
 x_347 = x_346;
}
lean_ctor_set(x_347, 0, x_344);
lean_ctor_set(x_347, 1, x_345);
return x_347;
}
}
}
else
{
lean_object* x_348; lean_object* x_349; uint8_t x_350; uint8_t x_351; lean_object* x_352; uint8_t x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; uint8_t x_360; uint8_t x_361; uint8_t x_362; uint8_t x_363; uint8_t x_364; uint8_t x_365; uint8_t x_366; uint8_t x_367; uint8_t x_368; uint8_t x_369; uint8_t x_370; uint8_t x_371; uint8_t x_372; uint8_t x_373; uint8_t x_374; uint8_t x_375; uint8_t x_376; uint8_t x_377; lean_object* x_378; lean_object* x_379; uint64_t x_380; lean_object* x_381; lean_object* x_382; 
x_348 = lean_ctor_get(x_247, 0);
x_349 = lean_ctor_get(x_247, 1);
lean_inc(x_349);
lean_inc(x_348);
lean_dec(x_247);
x_350 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_351 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_352 = lean_ctor_get(x_5, 0);
lean_inc(x_352);
lean_dec(x_5);
x_353 = lean_ctor_get_uint8(x_240, sizeof(void*)*7 + 8);
x_354 = lean_ctor_get(x_240, 1);
lean_inc(x_354);
x_355 = lean_ctor_get(x_240, 2);
lean_inc(x_355);
x_356 = lean_ctor_get(x_240, 3);
lean_inc(x_356);
x_357 = lean_ctor_get(x_240, 4);
lean_inc(x_357);
x_358 = lean_ctor_get(x_240, 5);
lean_inc(x_358);
x_359 = lean_ctor_get(x_240, 6);
lean_inc(x_359);
x_360 = lean_ctor_get_uint8(x_240, sizeof(void*)*7 + 9);
x_361 = lean_ctor_get_uint8(x_240, sizeof(void*)*7 + 10);
x_362 = lean_ctor_get_uint8(x_248, 0);
x_363 = lean_ctor_get_uint8(x_248, 1);
x_364 = lean_ctor_get_uint8(x_248, 2);
x_365 = lean_ctor_get_uint8(x_248, 3);
x_366 = lean_ctor_get_uint8(x_248, 4);
x_367 = lean_ctor_get_uint8(x_248, 5);
x_368 = lean_ctor_get_uint8(x_248, 6);
x_369 = lean_ctor_get_uint8(x_248, 7);
x_370 = lean_ctor_get_uint8(x_248, 10);
x_371 = lean_ctor_get_uint8(x_248, 11);
x_372 = lean_ctor_get_uint8(x_248, 12);
x_373 = lean_ctor_get_uint8(x_248, 13);
x_374 = lean_ctor_get_uint8(x_248, 14);
x_375 = lean_ctor_get_uint8(x_248, 15);
x_376 = lean_ctor_get_uint8(x_248, 16);
x_377 = lean_ctor_get_uint8(x_248, 17);
if (lean_is_exclusive(x_248)) {
 x_378 = x_248;
} else {
 lean_dec_ref(x_248);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(0, 0, 18);
} else {
 x_379 = x_378;
}
lean_ctor_set_uint8(x_379, 0, x_362);
lean_ctor_set_uint8(x_379, 1, x_363);
lean_ctor_set_uint8(x_379, 2, x_364);
lean_ctor_set_uint8(x_379, 3, x_365);
lean_ctor_set_uint8(x_379, 4, x_366);
lean_ctor_set_uint8(x_379, 5, x_367);
lean_ctor_set_uint8(x_379, 6, x_368);
lean_ctor_set_uint8(x_379, 7, x_369);
lean_ctor_set_uint8(x_379, 8, x_351);
lean_ctor_set_uint8(x_379, 9, x_350);
lean_ctor_set_uint8(x_379, 10, x_370);
lean_ctor_set_uint8(x_379, 11, x_371);
lean_ctor_set_uint8(x_379, 12, x_372);
lean_ctor_set_uint8(x_379, 13, x_373);
lean_ctor_set_uint8(x_379, 14, x_374);
lean_ctor_set_uint8(x_379, 15, x_375);
lean_ctor_set_uint8(x_379, 16, x_376);
lean_ctor_set_uint8(x_379, 17, x_377);
x_380 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_379);
x_381 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_354);
lean_ctor_set(x_381, 2, x_355);
lean_ctor_set(x_381, 3, x_356);
lean_ctor_set(x_381, 4, x_357);
lean_ctor_set(x_381, 5, x_358);
lean_ctor_set(x_381, 6, x_359);
lean_ctor_set_uint64(x_381, sizeof(void*)*7, x_380);
lean_ctor_set_uint8(x_381, sizeof(void*)*7 + 8, x_353);
lean_ctor_set_uint8(x_381, sizeof(void*)*7 + 9, x_360);
lean_ctor_set_uint8(x_381, sizeof(void*)*7 + 10, x_361);
lean_inc(x_243);
lean_inc(x_242);
lean_inc(x_241);
lean_inc(x_238);
lean_inc(x_348);
x_382 = l_Lean_Meta_kabstract(x_348, x_238, x_352, x_381, x_241, x_242, x_243, x_349);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; uint8_t x_385; 
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_382, 1);
lean_inc(x_384);
lean_dec(x_382);
x_385 = l_Lean_Expr_hasLooseBVars(x_383);
if (x_385 == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
lean_dec(x_383);
lean_dec(x_348);
lean_dec(x_239);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_3);
x_386 = l_Lean_MVarId_rewrite___lam__1___closed__28;
x_387 = l_Lean_indentExpr(x_238);
x_388 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_387);
x_389 = l_Lean_MVarId_rewrite___lam__1___closed__4;
x_390 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_390, 0, x_388);
lean_ctor_set(x_390, 1, x_389);
x_391 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_391, 0, x_390);
x_392 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_391, x_240, x_241, x_242, x_243, x_384);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_392, 1);
lean_inc(x_394);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 x_395 = x_392;
} else {
 lean_dec_ref(x_392);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(1, 2, 0);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_393);
lean_ctor_set(x_396, 1, x_394);
return x_396;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; 
x_397 = lean_expr_instantiate1(x_383, x_239);
x_398 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_397, x_241, x_384);
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
x_401 = l_Lean_Expr_hasBinderNameHint(x_239);
if (x_401 == 0)
{
lean_inc(x_383);
x_204 = x_383;
x_205 = x_238;
x_206 = x_235;
x_207 = x_239;
x_208 = x_348;
x_209 = x_236;
x_210 = x_383;
x_211 = x_399;
x_212 = x_240;
x_213 = x_241;
x_214 = x_242;
x_215 = x_243;
x_216 = x_400;
goto block_234;
}
else
{
lean_object* x_402; 
lean_inc(x_243);
lean_inc(x_242);
x_402 = l_Lean_Expr_resolveBinderNameHint(x_399, x_242, x_243, x_400);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; lean_object* x_404; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_402, 1);
lean_inc(x_404);
lean_dec(x_402);
lean_inc(x_383);
x_204 = x_383;
x_205 = x_238;
x_206 = x_235;
x_207 = x_239;
x_208 = x_348;
x_209 = x_236;
x_210 = x_383;
x_211 = x_403;
x_212 = x_240;
x_213 = x_241;
x_214 = x_242;
x_215 = x_243;
x_216 = x_404;
goto block_234;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
lean_dec(x_383);
lean_dec(x_348);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_405 = lean_ctor_get(x_402, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_402, 1);
lean_inc(x_406);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 lean_ctor_release(x_402, 1);
 x_407 = x_402;
} else {
 lean_dec_ref(x_402);
 x_407 = lean_box(0);
}
if (lean_is_scalar(x_407)) {
 x_408 = lean_alloc_ctor(1, 2, 0);
} else {
 x_408 = x_407;
}
lean_ctor_set(x_408, 0, x_405);
lean_ctor_set(x_408, 1, x_406);
return x_408;
}
}
}
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
lean_dec(x_348);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_409 = lean_ctor_get(x_382, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_382, 1);
lean_inc(x_410);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 x_411 = x_382;
} else {
 lean_dec_ref(x_382);
 x_411 = lean_box(0);
}
if (lean_is_scalar(x_411)) {
 x_412 = lean_alloc_ctor(1, 2, 0);
} else {
 x_412 = x_411;
}
lean_ctor_set(x_412, 0, x_409);
lean_ctor_set(x_412, 1, x_410);
return x_412;
}
}
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; 
lean_dec(x_239);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_413 = l_Lean_MVarId_rewrite___lam__1___closed__30;
x_414 = l_Lean_indentExpr(x_238);
x_415 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_415, 0, x_413);
lean_ctor_set(x_415, 1, x_414);
x_416 = l_Lean_MVarId_rewrite___lam__1___closed__32;
x_417 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_417, 0, x_415);
lean_ctor_set(x_417, 1, x_416);
x_418 = l_Lean_indentExpr(x_237);
x_419 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_419, 0, x_417);
lean_ctor_set(x_419, 1, x_418);
x_420 = l_Lean_MVarId_rewrite___lam__1___closed__4;
x_421 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_421, 0, x_419);
lean_ctor_set(x_421, 1, x_420);
x_422 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_422, 0, x_421);
x_423 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_422, x_240, x_241, x_242, x_243, x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
x_424 = !lean_is_exclusive(x_423);
if (x_424 == 0)
{
return x_423;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_425 = lean_ctor_get(x_423, 0);
x_426 = lean_ctor_get(x_423, 1);
lean_inc(x_426);
lean_inc(x_425);
lean_dec(x_423);
x_427 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_427, 0, x_425);
lean_ctor_set(x_427, 1, x_426);
return x_427;
}
}
}
block_474:
{
lean_object* x_436; 
lean_inc(x_434);
lean_inc(x_433);
lean_inc(x_432);
lean_inc(x_431);
lean_inc(x_430);
x_436 = l_Lean_Meta_matchEq_x3f(x_430, x_431, x_432, x_433, x_434, x_435);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; 
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
if (lean_obj_tag(x_437) == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_429);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_438 = lean_ctor_get(x_436, 1);
lean_inc(x_438);
lean_dec(x_436);
x_439 = l_Lean_MVarId_rewrite___lam__1___closed__34;
x_440 = l_Lean_indentExpr(x_430);
x_441 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_440);
x_442 = l_Lean_MVarId_rewrite___lam__1___closed__4;
x_443 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
x_444 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_444, 0, x_443);
x_445 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_444, x_431, x_432, x_433, x_434, x_438);
lean_dec(x_434);
lean_dec(x_433);
lean_dec(x_432);
lean_dec(x_431);
return x_445;
}
else
{
lean_object* x_446; lean_object* x_447; 
x_446 = lean_ctor_get(x_437, 0);
lean_inc(x_446);
lean_dec(x_437);
x_447 = lean_ctor_get(x_446, 1);
lean_inc(x_447);
if (x_6 == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_448 = lean_ctor_get(x_436, 1);
lean_inc(x_448);
lean_dec(x_436);
x_449 = lean_ctor_get(x_446, 0);
lean_inc(x_449);
lean_dec(x_446);
x_450 = lean_ctor_get(x_447, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_447, 1);
lean_inc(x_451);
lean_dec(x_447);
x_235 = x_449;
x_236 = x_429;
x_237 = x_430;
x_238 = x_450;
x_239 = x_451;
x_240 = x_431;
x_241 = x_432;
x_242 = x_433;
x_243 = x_434;
x_244 = x_448;
goto block_428;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
lean_dec(x_430);
x_452 = lean_ctor_get(x_436, 1);
lean_inc(x_452);
lean_dec(x_436);
x_453 = lean_ctor_get(x_446, 0);
lean_inc(x_453);
lean_dec(x_446);
x_454 = lean_ctor_get(x_447, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_447, 1);
lean_inc(x_455);
lean_dec(x_447);
lean_inc(x_434);
lean_inc(x_433);
lean_inc(x_432);
lean_inc(x_431);
x_456 = l_Lean_Meta_mkEqSymm(x_429, x_431, x_432, x_433, x_434, x_452);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_456, 1);
lean_inc(x_458);
lean_dec(x_456);
lean_inc(x_434);
lean_inc(x_433);
lean_inc(x_432);
lean_inc(x_431);
lean_inc(x_454);
lean_inc(x_455);
x_459 = l_Lean_Meta_mkEq(x_455, x_454, x_431, x_432, x_433, x_434, x_458);
if (lean_obj_tag(x_459) == 0)
{
lean_object* x_460; lean_object* x_461; 
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_459, 1);
lean_inc(x_461);
lean_dec(x_459);
x_235 = x_453;
x_236 = x_457;
x_237 = x_460;
x_238 = x_455;
x_239 = x_454;
x_240 = x_431;
x_241 = x_432;
x_242 = x_433;
x_243 = x_434;
x_244 = x_461;
goto block_428;
}
else
{
uint8_t x_462; 
lean_dec(x_457);
lean_dec(x_455);
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_434);
lean_dec(x_433);
lean_dec(x_432);
lean_dec(x_431);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_462 = !lean_is_exclusive(x_459);
if (x_462 == 0)
{
return x_459;
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_463 = lean_ctor_get(x_459, 0);
x_464 = lean_ctor_get(x_459, 1);
lean_inc(x_464);
lean_inc(x_463);
lean_dec(x_459);
x_465 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_465, 0, x_463);
lean_ctor_set(x_465, 1, x_464);
return x_465;
}
}
}
else
{
uint8_t x_466; 
lean_dec(x_455);
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_434);
lean_dec(x_433);
lean_dec(x_432);
lean_dec(x_431);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_466 = !lean_is_exclusive(x_456);
if (x_466 == 0)
{
return x_456;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_467 = lean_ctor_get(x_456, 0);
x_468 = lean_ctor_get(x_456, 1);
lean_inc(x_468);
lean_inc(x_467);
lean_dec(x_456);
x_469 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_469, 0, x_467);
lean_ctor_set(x_469, 1, x_468);
return x_469;
}
}
}
}
}
else
{
uint8_t x_470; 
lean_dec(x_434);
lean_dec(x_433);
lean_dec(x_432);
lean_dec(x_431);
lean_dec(x_430);
lean_dec(x_429);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_470 = !lean_is_exclusive(x_436);
if (x_470 == 0)
{
return x_436;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_471 = lean_ctor_get(x_436, 0);
x_472 = lean_ctor_get(x_436, 1);
lean_inc(x_472);
lean_inc(x_471);
lean_dec(x_436);
x_473 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_473, 0, x_471);
lean_ctor_set(x_473, 1, x_472);
return x_473;
}
}
}
}
else
{
uint8_t x_491; 
lean_dec(x_50);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_491 = !lean_is_exclusive(x_54);
if (x_491 == 0)
{
return x_54;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_492 = lean_ctor_get(x_54, 0);
x_493 = lean_ctor_get(x_54, 1);
lean_inc(x_493);
lean_inc(x_492);
lean_dec(x_54);
x_494 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_494, 0, x_492);
lean_ctor_set(x_494, 1, x_493);
return x_494;
}
}
}
else
{
uint8_t x_495; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_495 = !lean_is_exclusive(x_44);
if (x_495 == 0)
{
return x_44;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_496 = lean_ctor_get(x_44, 0);
x_497 = lean_ctor_get(x_44, 1);
lean_inc(x_497);
lean_inc(x_496);
lean_dec(x_44);
x_498 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_498, 0, x_496);
lean_ctor_set(x_498, 1, x_497);
return x_498;
}
}
}
else
{
uint8_t x_499; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_499 = !lean_is_exclusive(x_42);
if (x_499 == 0)
{
return x_42;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_500 = lean_ctor_get(x_42, 0);
x_501 = lean_ctor_get(x_42, 1);
lean_inc(x_501);
lean_inc(x_500);
lean_dec(x_42);
x_502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_502, 0, x_500);
lean_ctor_set(x_502, 1, x_501);
return x_502;
}
}
block_21:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = l_Array_append___redArg(x_15, x_16);
lean_dec(x_16);
x_18 = lean_array_to_list(x_17);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
block_41:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = l_Lean_Meta_getMVarsNoDelayed(x_3, x_29, x_23, x_25, x_28, x_31);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_29);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_array_get_size(x_33);
x_36 = lean_mk_empty_array_with_capacity(x_22);
x_37 = lean_nat_dec_lt(x_22, x_35);
if (x_37 == 0)
{
lean_dec(x_35);
lean_dec(x_33);
x_12 = x_34;
x_13 = x_27;
x_14 = x_26;
x_15 = x_30;
x_16 = x_36;
goto block_21;
}
else
{
uint8_t x_38; 
x_38 = lean_nat_dec_le(x_35, x_35);
if (x_38 == 0)
{
lean_dec(x_35);
lean_dec(x_33);
x_12 = x_34;
x_13 = x_27;
x_14 = x_26;
x_15 = x_30;
x_16 = x_36;
goto block_21;
}
else
{
size_t x_39; lean_object* x_40; 
x_39 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_40 = l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__2(x_30, x_33, x_24, x_39, x_36);
lean_dec(x_33);
x_12 = x_34;
x_13 = x_27;
x_14 = x_26;
x_15 = x_30;
x_16 = x_40;
goto block_21;
}
}
}
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rewrite", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_rewrite___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_rewrite___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_MVarId_rewrite___closed__1;
x_12 = lean_box(x_4);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lam__1___boxed), 11, 6);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_11);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_2);
lean_closure_set(x_13, 4, x_5);
lean_closure_set(x_13, 5, x_12);
x_14 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_13, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_MVarId_rewrite_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_MVarId_rewrite_spec__0_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___Lean_MVarId_rewrite_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___Lean_MVarId_rewrite_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__3___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__3(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_rewrite___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l_Lean_MVarId_rewrite___lam__1(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
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
l_Lean_MVarId_rewrite___lam__1___closed__0 = _init_l_Lean_MVarId_rewrite___lam__1___closed__0();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__0);
l_Lean_MVarId_rewrite___lam__1___closed__1 = _init_l_Lean_MVarId_rewrite___lam__1___closed__1();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__1);
l_Lean_MVarId_rewrite___lam__1___closed__2 = _init_l_Lean_MVarId_rewrite___lam__1___closed__2();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__2);
l_Lean_MVarId_rewrite___lam__1___closed__3 = _init_l_Lean_MVarId_rewrite___lam__1___closed__3();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__3);
l_Lean_MVarId_rewrite___lam__1___closed__4 = _init_l_Lean_MVarId_rewrite___lam__1___closed__4();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__4);
l_Lean_MVarId_rewrite___lam__1___closed__5 = _init_l_Lean_MVarId_rewrite___lam__1___closed__5();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__5);
l_Lean_MVarId_rewrite___lam__1___closed__6 = _init_l_Lean_MVarId_rewrite___lam__1___closed__6();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__6);
l_Lean_MVarId_rewrite___lam__1___closed__7 = _init_l_Lean_MVarId_rewrite___lam__1___closed__7();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__7);
l_Lean_MVarId_rewrite___lam__1___closed__8 = _init_l_Lean_MVarId_rewrite___lam__1___closed__8();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__8);
l_Lean_MVarId_rewrite___lam__1___closed__9 = _init_l_Lean_MVarId_rewrite___lam__1___closed__9();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__9);
l_Lean_MVarId_rewrite___lam__1___closed__10 = _init_l_Lean_MVarId_rewrite___lam__1___closed__10();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__10);
l_Lean_MVarId_rewrite___lam__1___closed__11 = _init_l_Lean_MVarId_rewrite___lam__1___closed__11();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__11);
l_Lean_MVarId_rewrite___lam__1___closed__12 = _init_l_Lean_MVarId_rewrite___lam__1___closed__12();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__12);
l_Lean_MVarId_rewrite___lam__1___closed__13 = _init_l_Lean_MVarId_rewrite___lam__1___closed__13();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__13);
l_Lean_MVarId_rewrite___lam__1___closed__14 = _init_l_Lean_MVarId_rewrite___lam__1___closed__14();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__14);
l_Lean_MVarId_rewrite___lam__1___closed__15 = _init_l_Lean_MVarId_rewrite___lam__1___closed__15();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__15);
l_Lean_MVarId_rewrite___lam__1___closed__16 = _init_l_Lean_MVarId_rewrite___lam__1___closed__16();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__16);
l_Lean_MVarId_rewrite___lam__1___closed__17 = _init_l_Lean_MVarId_rewrite___lam__1___closed__17();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__17);
l_Lean_MVarId_rewrite___lam__1___closed__18 = _init_l_Lean_MVarId_rewrite___lam__1___closed__18();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__18);
l_Lean_MVarId_rewrite___lam__1___closed__19 = _init_l_Lean_MVarId_rewrite___lam__1___closed__19();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__19);
l_Lean_MVarId_rewrite___lam__1___closed__20 = _init_l_Lean_MVarId_rewrite___lam__1___closed__20();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__20);
l_Lean_MVarId_rewrite___lam__1___closed__21 = _init_l_Lean_MVarId_rewrite___lam__1___closed__21();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__21);
l_Lean_MVarId_rewrite___lam__1___closed__22 = _init_l_Lean_MVarId_rewrite___lam__1___closed__22();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__22);
l_Lean_MVarId_rewrite___lam__1___closed__23 = _init_l_Lean_MVarId_rewrite___lam__1___closed__23();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__23);
l_Lean_MVarId_rewrite___lam__1___closed__24 = _init_l_Lean_MVarId_rewrite___lam__1___closed__24();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__24);
l_Lean_MVarId_rewrite___lam__1___closed__25 = _init_l_Lean_MVarId_rewrite___lam__1___closed__25();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__25);
l_Lean_MVarId_rewrite___lam__1___closed__26 = _init_l_Lean_MVarId_rewrite___lam__1___closed__26();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__26);
l_Lean_MVarId_rewrite___lam__1___closed__27 = _init_l_Lean_MVarId_rewrite___lam__1___closed__27();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__27);
l_Lean_MVarId_rewrite___lam__1___closed__28 = _init_l_Lean_MVarId_rewrite___lam__1___closed__28();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__28);
l_Lean_MVarId_rewrite___lam__1___closed__29 = _init_l_Lean_MVarId_rewrite___lam__1___closed__29();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__29);
l_Lean_MVarId_rewrite___lam__1___closed__30 = _init_l_Lean_MVarId_rewrite___lam__1___closed__30();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__30);
l_Lean_MVarId_rewrite___lam__1___closed__31 = _init_l_Lean_MVarId_rewrite___lam__1___closed__31();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__31);
l_Lean_MVarId_rewrite___lam__1___closed__32 = _init_l_Lean_MVarId_rewrite___lam__1___closed__32();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__32);
l_Lean_MVarId_rewrite___lam__1___closed__33 = _init_l_Lean_MVarId_rewrite___lam__1___closed__33();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__33);
l_Lean_MVarId_rewrite___lam__1___closed__34 = _init_l_Lean_MVarId_rewrite___lam__1___closed__34();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__34);
l_Lean_MVarId_rewrite___lam__1___closed__35 = _init_l_Lean_MVarId_rewrite___lam__1___closed__35();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__35);
l_Lean_MVarId_rewrite___lam__1___closed__36 = _init_l_Lean_MVarId_rewrite___lam__1___closed__36();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__36);
l_Lean_MVarId_rewrite___lam__1___closed__37 = _init_l_Lean_MVarId_rewrite___lam__1___closed__37();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__37);
l_Lean_MVarId_rewrite___lam__1___closed__38 = _init_l_Lean_MVarId_rewrite___lam__1___closed__38();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__38);
l_Lean_MVarId_rewrite___lam__1___closed__39 = _init_l_Lean_MVarId_rewrite___lam__1___closed__39();
lean_mark_persistent(l_Lean_MVarId_rewrite___lam__1___closed__39);
l_Lean_MVarId_rewrite___closed__0 = _init_l_Lean_MVarId_rewrite___closed__0();
lean_mark_persistent(l_Lean_MVarId_rewrite___closed__0);
l_Lean_MVarId_rewrite___closed__1 = _init_l_Lean_MVarId_rewrite___closed__1();
lean_mark_persistent(l_Lean_MVarId_rewrite___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
