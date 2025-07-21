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
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
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
uint8_t x_11; 
x_11 = 0;
return x_11;
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
lean_dec_ref(x_18);
x_15 = x_21;
goto block_17;
}
else
{
lean_object* x_22; 
lean_dec(x_14);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec_ref(x_18);
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
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_10 = lean_infer_type(x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Lean_Meta_isExprDefEq(x_11, x_2, x_4, x_5, x_6, x_7, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_42; 
lean_inc(x_2);
lean_inc(x_1);
x_42 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec_ref(x_42);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_3);
x_44 = lean_infer_type(x_3, x_7, x_8, x_9, x_10, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec_ref(x_44);
x_47 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__0___redArg(x_45, x_8, x_46);
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
x_52 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_53 = l_Lean_Meta_forallMetaTelescopeReducing(x_48, x_51, x_52, x_7, x_8, x_9, x_10, x_49);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_473; lean_object* x_474; lean_object* x_475; uint8_t x_476; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec_ref(x_53);
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_58 = x_54;
} else {
 lean_dec_ref(x_54);
 x_58 = lean_box(0);
}
x_59 = lean_ctor_get(x_55, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_61 = x_55;
} else {
 lean_dec_ref(x_55);
 x_61 = lean_box(0);
}
lean_inc_ref(x_3);
x_473 = l_Lean_mkAppN(x_3, x_57);
x_474 = l_Lean_MVarId_rewrite___lam__1___closed__36;
x_475 = lean_unsigned_to_nat(2u);
x_476 = l_Lean_Expr_isAppOfArity(x_60, x_474, x_475);
if (x_476 == 0)
{
x_427 = x_473;
x_428 = x_60;
x_429 = x_7;
x_430 = x_8;
x_431 = x_9;
x_432 = x_10;
x_433 = x_56;
goto block_472;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_477 = l_Lean_Expr_appFn_x21(x_60);
x_478 = l_Lean_Expr_appArg_x21(x_477);
lean_dec_ref(x_477);
x_479 = l_Lean_Expr_appArg_x21(x_60);
lean_dec(x_60);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_479);
lean_inc_ref(x_478);
x_480 = l_Lean_Meta_mkEq(x_478, x_479, x_7, x_8, x_9, x_10, x_56);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_480, 1);
lean_inc(x_482);
lean_dec_ref(x_480);
x_483 = l_Lean_MVarId_rewrite___lam__1___closed__39;
x_484 = l_Lean_mkApp3(x_483, x_478, x_479, x_473);
x_427 = x_484;
x_428 = x_481;
x_429 = x_7;
x_430 = x_8;
x_431 = x_9;
x_432 = x_10;
x_433 = x_482;
goto block_472;
}
else
{
uint8_t x_485; 
lean_dec_ref(x_479);
lean_dec_ref(x_478);
lean_dec_ref(x_473);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_50);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_485 = !lean_is_exclusive(x_480);
if (x_485 == 0)
{
return x_480;
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_486 = lean_ctor_get(x_480, 0);
x_487 = lean_ctor_get(x_480, 1);
lean_inc(x_487);
lean_inc(x_486);
lean_dec(x_480);
x_488 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set(x_488, 1, x_487);
return x_488;
}
}
}
block_89:
{
uint8_t x_70; lean_object* x_71; 
x_70 = 0;
lean_inc(x_62);
lean_inc_ref(x_65);
lean_inc(x_63);
lean_inc_ref(x_66);
x_71 = l_Lean_Meta_postprocessAppMVars(x_2, x_1, x_57, x_59, x_69, x_70, x_66, x_63, x_65, x_62, x_64);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec_ref(x_71);
x_73 = lean_array_size(x_57);
x_74 = 0;
x_75 = l_Array_mapMUnsafe_map___at___Lean_MVarId_applyN_spec__0(x_73, x_74, x_57);
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_array_get_size(x_75);
x_78 = l_Lean_MVarId_rewrite___lam__1___closed__0;
x_79 = lean_nat_dec_lt(x_76, x_77);
if (x_79 == 0)
{
lean_dec(x_77);
lean_dec_ref(x_75);
x_22 = x_62;
x_23 = x_63;
x_24 = x_65;
x_25 = x_66;
x_26 = x_67;
x_27 = x_76;
x_28 = x_68;
x_29 = x_74;
x_30 = x_78;
x_31 = x_72;
goto block_41;
}
else
{
uint8_t x_80; 
x_80 = lean_nat_dec_le(x_77, x_77);
if (x_80 == 0)
{
lean_dec(x_77);
lean_dec_ref(x_75);
x_22 = x_62;
x_23 = x_63;
x_24 = x_65;
x_25 = x_66;
x_26 = x_67;
x_27 = x_76;
x_28 = x_68;
x_29 = x_74;
x_30 = x_78;
x_31 = x_72;
goto block_41;
}
else
{
size_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_82 = l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__3___redArg(x_75, x_74, x_81, x_78, x_63, x_72);
lean_dec_ref(x_75);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec_ref(x_82);
x_22 = x_62;
x_23 = x_63;
x_24 = x_65;
x_25 = x_66;
x_26 = x_67;
x_27 = x_76;
x_28 = x_68;
x_29 = x_74;
x_30 = x_83;
x_31 = x_84;
goto block_41;
}
}
}
else
{
uint8_t x_85; 
lean_dec_ref(x_68);
lean_dec_ref(x_67);
lean_dec_ref(x_66);
lean_dec_ref(x_65);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_57);
lean_dec_ref(x_3);
x_85 = !lean_is_exclusive(x_71);
if (x_85 == 0)
{
return x_71;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_71, 0);
x_87 = lean_ctor_get(x_71, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_71);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
block_155:
{
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec_ref(x_103);
lean_inc(x_90);
lean_inc_ref(x_96);
lean_inc(x_94);
lean_inc_ref(x_95);
lean_inc_ref(x_102);
x_105 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__2___redArg(x_97, x_102, x_98, x_95, x_94, x_96, x_90, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_unbox(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
lean_dec(x_106);
lean_dec_ref(x_102);
lean_dec_ref(x_100);
lean_dec_ref(x_99);
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_dec_ref(x_91);
lean_dec(x_59);
lean_dec(x_57);
lean_dec_ref(x_3);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_dec_ref(x_105);
x_109 = l_Lean_MVarId_rewrite___lam__1___closed__2;
x_110 = l_Lean_MessageData_ofExpr(x_101);
x_111 = l_Lean_indentD(x_110);
if (lean_is_scalar(x_61)) {
 x_112 = lean_alloc_ctor(7, 2, 0);
} else {
 x_112 = x_61;
 lean_ctor_set_tag(x_112, 7);
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_MVarId_rewrite___lam__1___closed__4;
if (lean_is_scalar(x_58)) {
 x_114 = lean_alloc_ctor(7, 2, 0);
} else {
 x_114 = x_58;
 lean_ctor_set_tag(x_114, 7);
}
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_115, x_95, x_94, x_96, x_90, x_108);
lean_dec(x_90);
lean_dec_ref(x_96);
lean_dec(x_94);
lean_dec_ref(x_95);
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
return x_116;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_116, 0);
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_116);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_105, 1);
lean_inc(x_121);
lean_dec_ref(x_105);
lean_inc(x_90);
lean_inc_ref(x_96);
lean_inc(x_94);
lean_inc_ref(x_95);
lean_inc_ref(x_102);
x_122 = l_Lean_Meta_getLevel(x_102, x_95, x_94, x_96, x_90, x_121);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec_ref(x_122);
lean_inc(x_90);
lean_inc_ref(x_96);
lean_inc(x_94);
lean_inc_ref(x_95);
lean_inc_ref(x_93);
x_125 = l_Lean_Meta_getLevel(x_93, x_95, x_94, x_96, x_90, x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec_ref(x_125);
x_128 = lean_ctor_get(x_96, 2);
lean_inc(x_128);
x_129 = l_Lean_MVarId_rewrite___lam__1___closed__6;
x_130 = lean_box(0);
if (lean_is_scalar(x_61)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_61;
 lean_ctor_set_tag(x_131, 1);
}
lean_ctor_set(x_131, 0, x_126);
lean_ctor_set(x_131, 1, x_130);
if (lean_is_scalar(x_58)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_58;
 lean_ctor_set_tag(x_132, 1);
}
lean_ctor_set(x_132, 0, x_123);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_Lean_Expr_const___override(x_129, x_132);
x_134 = l_Lean_mkApp6(x_133, x_102, x_93, x_92, x_91, x_101, x_99);
x_135 = l_Lean_MVarId_rewrite___lam__1___closed__7;
x_136 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_128, x_135);
lean_dec(x_128);
if (x_136 == 0)
{
uint8_t x_137; 
x_137 = lean_unbox(x_106);
lean_dec(x_106);
x_62 = x_90;
x_63 = x_94;
x_64 = x_127;
x_65 = x_96;
x_66 = x_95;
x_67 = x_100;
x_68 = x_134;
x_69 = x_137;
goto block_89;
}
else
{
uint8_t x_138; 
lean_dec(x_106);
x_138 = 0;
x_62 = x_90;
x_63 = x_94;
x_64 = x_127;
x_65 = x_96;
x_66 = x_95;
x_67 = x_100;
x_68 = x_134;
x_69 = x_138;
goto block_89;
}
}
else
{
uint8_t x_139; 
lean_dec(x_123);
lean_dec(x_106);
lean_dec_ref(x_102);
lean_dec_ref(x_101);
lean_dec_ref(x_100);
lean_dec_ref(x_99);
lean_dec_ref(x_96);
lean_dec_ref(x_95);
lean_dec(x_94);
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_125);
if (x_139 == 0)
{
return x_125;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_125, 0);
x_141 = lean_ctor_get(x_125, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_125);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_106);
lean_dec_ref(x_102);
lean_dec_ref(x_101);
lean_dec_ref(x_100);
lean_dec_ref(x_99);
lean_dec_ref(x_96);
lean_dec_ref(x_95);
lean_dec(x_94);
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_122);
if (x_143 == 0)
{
return x_122;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_122, 0);
x_145 = lean_ctor_get(x_122, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_122);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
}
else
{
uint8_t x_147; 
lean_dec_ref(x_102);
lean_dec_ref(x_101);
lean_dec_ref(x_100);
lean_dec_ref(x_99);
lean_dec_ref(x_96);
lean_dec_ref(x_95);
lean_dec(x_94);
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_147 = !lean_is_exclusive(x_105);
if (x_147 == 0)
{
return x_105;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_105, 0);
x_149 = lean_ctor_get(x_105, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_105);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
else
{
uint8_t x_151; 
lean_dec_ref(x_102);
lean_dec_ref(x_101);
lean_dec_ref(x_100);
lean_dec_ref(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec_ref(x_95);
lean_dec(x_94);
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_151 = !lean_is_exclusive(x_103);
if (x_151 == 0)
{
return x_103;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_103, 0);
x_153 = lean_ctor_get(x_103, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_103);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
block_200:
{
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec_ref(x_156);
x_173 = l_Lean_MVarId_rewrite___lam__1___closed__9;
lean_inc_ref(x_170);
x_174 = l_Lean_MessageData_ofExpr(x_170);
x_175 = l_Lean_indentD(x_174);
if (lean_is_scalar(x_50)) {
 x_176 = lean_alloc_ctor(7, 2, 0);
} else {
 x_176 = x_50;
 lean_ctor_set_tag(x_176, 7);
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_175);
x_177 = l_Lean_MVarId_rewrite___lam__1___closed__11;
x_178 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_179 = l_Lean_Exception_toMessageData(x_167);
x_180 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
x_181 = l_Lean_MVarId_rewrite___lam__1___closed__13;
x_182 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
x_183 = l_Lean_MVarId_rewrite___lam__1___closed__6;
x_184 = l_Lean_MessageData_ofConstName(x_183, x_172);
x_185 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_184);
x_186 = l_Lean_MVarId_rewrite___lam__1___closed__15;
x_187 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_188 = l_Lean_MVarId_rewrite___lam__1___closed__18;
x_189 = l_Lean_MessageData_ofConstName(x_188, x_172);
x_190 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_189);
x_191 = l_Lean_MVarId_rewrite___lam__1___closed__20;
x_192 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_193 = l_Lean_MVarId_rewrite___lam__1___closed__22;
x_194 = l_Lean_MessageData_ofConstName(x_193, x_172);
x_195 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_194);
x_196 = l_Lean_MVarId_rewrite___lam__1___closed__24;
x_197 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_197);
lean_inc(x_1);
lean_inc(x_2);
x_199 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_198, x_162, x_161, x_163, x_157, x_166);
x_90 = x_157;
x_91 = x_158;
x_92 = x_159;
x_93 = x_160;
x_94 = x_161;
x_95 = x_162;
x_96 = x_163;
x_97 = x_164;
x_98 = x_165;
x_99 = x_168;
x_100 = x_169;
x_101 = x_170;
x_102 = x_171;
x_103 = x_199;
goto block_155;
}
else
{
lean_dec_ref(x_167);
lean_dec(x_50);
x_90 = x_157;
x_91 = x_158;
x_92 = x_159;
x_93 = x_160;
x_94 = x_161;
x_95 = x_162;
x_96 = x_163;
x_97 = x_164;
x_98 = x_165;
x_99 = x_168;
x_100 = x_169;
x_101 = x_170;
x_102 = x_171;
x_103 = x_156;
goto block_155;
}
}
block_230:
{
lean_object* x_214; 
lean_inc(x_212);
lean_inc_ref(x_211);
lean_inc(x_210);
lean_inc_ref(x_209);
x_214 = lean_infer_type(x_205, x_209, x_210, x_211, x_212, x_213);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec_ref(x_214);
lean_inc(x_215);
x_217 = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lam__0___boxed), 8, 2);
lean_closure_set(x_217, 0, x_201);
lean_closure_set(x_217, 1, x_215);
x_218 = l_Lean_MVarId_rewrite___lam__1___closed__26;
x_219 = 0;
lean_inc_ref(x_206);
x_220 = l_Lean_Expr_lam___override(x_218, x_206, x_207, x_219);
lean_inc(x_212);
lean_inc_ref(x_211);
lean_inc(x_210);
lean_inc_ref(x_209);
lean_inc_ref(x_220);
x_221 = l_Lean_Meta_check(x_220, x_209, x_210, x_211, x_212, x_216);
if (lean_obj_tag(x_221) == 0)
{
lean_dec(x_50);
x_90 = x_212;
x_91 = x_202;
x_92 = x_204;
x_93 = x_215;
x_94 = x_210;
x_95 = x_209;
x_96 = x_211;
x_97 = x_218;
x_98 = x_217;
x_99 = x_203;
x_100 = x_208;
x_101 = x_220;
x_102 = x_206;
x_103 = x_221;
goto block_155;
}
else
{
lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
x_224 = l_Lean_Exception_isInterrupt(x_222);
if (x_224 == 0)
{
uint8_t x_225; 
x_225 = l_Lean_Exception_isRuntime(x_222);
x_156 = x_221;
x_157 = x_212;
x_158 = x_202;
x_159 = x_204;
x_160 = x_215;
x_161 = x_210;
x_162 = x_209;
x_163 = x_211;
x_164 = x_218;
x_165 = x_217;
x_166 = x_223;
x_167 = x_222;
x_168 = x_203;
x_169 = x_208;
x_170 = x_220;
x_171 = x_206;
x_172 = x_225;
goto block_200;
}
else
{
x_156 = x_221;
x_157 = x_212;
x_158 = x_202;
x_159 = x_204;
x_160 = x_215;
x_161 = x_210;
x_162 = x_209;
x_163 = x_211;
x_164 = x_218;
x_165 = x_217;
x_166 = x_223;
x_167 = x_222;
x_168 = x_203;
x_169 = x_208;
x_170 = x_220;
x_171 = x_206;
x_172 = x_224;
goto block_200;
}
}
}
else
{
uint8_t x_226; 
lean_dec(x_212);
lean_dec_ref(x_211);
lean_dec(x_210);
lean_dec_ref(x_209);
lean_dec_ref(x_208);
lean_dec_ref(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_204);
lean_dec_ref(x_203);
lean_dec_ref(x_202);
lean_dec_ref(x_201);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_50);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_226 = !lean_is_exclusive(x_214);
if (x_226 == 0)
{
return x_214;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_214, 0);
x_228 = lean_ctor_get(x_214, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_214);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
block_426:
{
lean_object* x_241; uint8_t x_242; 
x_241 = l_Lean_Expr_getAppFn(x_234);
x_242 = l_Lean_Expr_isMVar(x_241);
lean_dec_ref(x_241);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; uint8_t x_245; 
lean_dec_ref(x_233);
x_243 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__0___redArg(x_4, x_237, x_240);
x_244 = lean_ctor_get(x_236, 0);
lean_inc_ref(x_244);
x_245 = !lean_is_exclusive(x_243);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; uint8_t x_248; uint8_t x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_246 = lean_ctor_get(x_243, 0);
x_247 = lean_ctor_get(x_243, 1);
x_248 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_249 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_250 = lean_ctor_get(x_5, 0);
lean_inc(x_250);
lean_dec_ref(x_5);
x_251 = lean_ctor_get_uint8(x_236, sizeof(void*)*7 + 8);
x_252 = lean_ctor_get(x_236, 1);
lean_inc(x_252);
x_253 = lean_ctor_get(x_236, 2);
lean_inc_ref(x_253);
x_254 = lean_ctor_get(x_236, 3);
lean_inc_ref(x_254);
x_255 = lean_ctor_get(x_236, 4);
lean_inc(x_255);
x_256 = lean_ctor_get(x_236, 5);
lean_inc(x_256);
x_257 = lean_ctor_get(x_236, 6);
lean_inc(x_257);
x_258 = !lean_is_exclusive(x_244);
if (x_258 == 0)
{
uint8_t x_259; uint8_t x_260; uint64_t x_261; lean_object* x_262; lean_object* x_263; 
x_259 = lean_ctor_get_uint8(x_236, sizeof(void*)*7 + 9);
x_260 = lean_ctor_get_uint8(x_236, sizeof(void*)*7 + 10);
lean_ctor_set_uint8(x_244, 8, x_249);
lean_ctor_set_uint8(x_244, 9, x_248);
x_261 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_244);
x_262 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_262, 0, x_244);
lean_ctor_set(x_262, 1, x_252);
lean_ctor_set(x_262, 2, x_253);
lean_ctor_set(x_262, 3, x_254);
lean_ctor_set(x_262, 4, x_255);
lean_ctor_set(x_262, 5, x_256);
lean_ctor_set(x_262, 6, x_257);
lean_ctor_set_uint64(x_262, sizeof(void*)*7, x_261);
lean_ctor_set_uint8(x_262, sizeof(void*)*7 + 8, x_251);
lean_ctor_set_uint8(x_262, sizeof(void*)*7 + 9, x_259);
lean_ctor_set_uint8(x_262, sizeof(void*)*7 + 10, x_260);
lean_inc(x_239);
lean_inc_ref(x_238);
lean_inc(x_237);
lean_inc_ref(x_234);
lean_inc(x_246);
x_263 = l_Lean_Meta_kabstract(x_246, x_234, x_250, x_262, x_237, x_238, x_239, x_247);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec_ref(x_263);
x_266 = l_Lean_Expr_hasLooseBVars(x_264);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; 
lean_dec(x_264);
lean_dec(x_246);
lean_dec_ref(x_235);
lean_dec_ref(x_232);
lean_dec_ref(x_231);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_50);
lean_dec_ref(x_3);
x_267 = l_Lean_MVarId_rewrite___lam__1___closed__28;
x_268 = l_Lean_indentExpr(x_234);
lean_ctor_set_tag(x_243, 7);
lean_ctor_set(x_243, 1, x_268);
lean_ctor_set(x_243, 0, x_267);
x_269 = l_Lean_MVarId_rewrite___lam__1___closed__4;
x_270 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_270, 0, x_243);
lean_ctor_set(x_270, 1, x_269);
x_271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_271, 0, x_270);
x_272 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_271, x_236, x_237, x_238, x_239, x_265);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
x_273 = !lean_is_exclusive(x_272);
if (x_273 == 0)
{
return x_272;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_272, 0);
x_275 = lean_ctor_get(x_272, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_272);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
lean_free_object(x_243);
x_277 = lean_expr_instantiate1(x_264, x_235);
x_278 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__0___redArg(x_277, x_237, x_265);
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
lean_dec_ref(x_278);
x_281 = l_Lean_Expr_hasBinderNameHint(x_235);
if (x_281 == 0)
{
lean_inc(x_264);
x_201 = x_264;
x_202 = x_235;
x_203 = x_232;
x_204 = x_234;
x_205 = x_246;
x_206 = x_231;
x_207 = x_264;
x_208 = x_279;
x_209 = x_236;
x_210 = x_237;
x_211 = x_238;
x_212 = x_239;
x_213 = x_280;
goto block_230;
}
else
{
lean_object* x_282; 
lean_inc(x_239);
lean_inc_ref(x_238);
x_282 = l_Lean_Expr_resolveBinderNameHint(x_279, x_238, x_239, x_280);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec_ref(x_282);
lean_inc(x_264);
x_201 = x_264;
x_202 = x_235;
x_203 = x_232;
x_204 = x_234;
x_205 = x_246;
x_206 = x_231;
x_207 = x_264;
x_208 = x_283;
x_209 = x_236;
x_210 = x_237;
x_211 = x_238;
x_212 = x_239;
x_213 = x_284;
goto block_230;
}
else
{
uint8_t x_285; 
lean_dec(x_264);
lean_dec(x_246);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_235);
lean_dec_ref(x_234);
lean_dec_ref(x_232);
lean_dec_ref(x_231);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_50);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_285 = !lean_is_exclusive(x_282);
if (x_285 == 0)
{
return x_282;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_282, 0);
x_287 = lean_ctor_get(x_282, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_282);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
return x_288;
}
}
}
}
}
else
{
uint8_t x_289; 
lean_free_object(x_243);
lean_dec(x_246);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_235);
lean_dec_ref(x_234);
lean_dec_ref(x_232);
lean_dec_ref(x_231);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_50);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_289 = !lean_is_exclusive(x_263);
if (x_289 == 0)
{
return x_263;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_263, 0);
x_291 = lean_ctor_get(x_263, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_263);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
}
}
else
{
uint8_t x_293; uint8_t x_294; uint8_t x_295; uint8_t x_296; uint8_t x_297; uint8_t x_298; uint8_t x_299; uint8_t x_300; uint8_t x_301; uint8_t x_302; uint8_t x_303; uint8_t x_304; uint8_t x_305; uint8_t x_306; uint8_t x_307; uint8_t x_308; uint8_t x_309; uint8_t x_310; uint8_t x_311; lean_object* x_312; uint64_t x_313; lean_object* x_314; lean_object* x_315; 
x_293 = lean_ctor_get_uint8(x_236, sizeof(void*)*7 + 9);
x_294 = lean_ctor_get_uint8(x_236, sizeof(void*)*7 + 10);
x_295 = lean_ctor_get_uint8(x_244, 0);
x_296 = lean_ctor_get_uint8(x_244, 1);
x_297 = lean_ctor_get_uint8(x_244, 2);
x_298 = lean_ctor_get_uint8(x_244, 3);
x_299 = lean_ctor_get_uint8(x_244, 4);
x_300 = lean_ctor_get_uint8(x_244, 5);
x_301 = lean_ctor_get_uint8(x_244, 6);
x_302 = lean_ctor_get_uint8(x_244, 7);
x_303 = lean_ctor_get_uint8(x_244, 10);
x_304 = lean_ctor_get_uint8(x_244, 11);
x_305 = lean_ctor_get_uint8(x_244, 12);
x_306 = lean_ctor_get_uint8(x_244, 13);
x_307 = lean_ctor_get_uint8(x_244, 14);
x_308 = lean_ctor_get_uint8(x_244, 15);
x_309 = lean_ctor_get_uint8(x_244, 16);
x_310 = lean_ctor_get_uint8(x_244, 17);
x_311 = lean_ctor_get_uint8(x_244, 18);
lean_dec(x_244);
x_312 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_312, 0, x_295);
lean_ctor_set_uint8(x_312, 1, x_296);
lean_ctor_set_uint8(x_312, 2, x_297);
lean_ctor_set_uint8(x_312, 3, x_298);
lean_ctor_set_uint8(x_312, 4, x_299);
lean_ctor_set_uint8(x_312, 5, x_300);
lean_ctor_set_uint8(x_312, 6, x_301);
lean_ctor_set_uint8(x_312, 7, x_302);
lean_ctor_set_uint8(x_312, 8, x_249);
lean_ctor_set_uint8(x_312, 9, x_248);
lean_ctor_set_uint8(x_312, 10, x_303);
lean_ctor_set_uint8(x_312, 11, x_304);
lean_ctor_set_uint8(x_312, 12, x_305);
lean_ctor_set_uint8(x_312, 13, x_306);
lean_ctor_set_uint8(x_312, 14, x_307);
lean_ctor_set_uint8(x_312, 15, x_308);
lean_ctor_set_uint8(x_312, 16, x_309);
lean_ctor_set_uint8(x_312, 17, x_310);
lean_ctor_set_uint8(x_312, 18, x_311);
x_313 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_312);
x_314 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_252);
lean_ctor_set(x_314, 2, x_253);
lean_ctor_set(x_314, 3, x_254);
lean_ctor_set(x_314, 4, x_255);
lean_ctor_set(x_314, 5, x_256);
lean_ctor_set(x_314, 6, x_257);
lean_ctor_set_uint64(x_314, sizeof(void*)*7, x_313);
lean_ctor_set_uint8(x_314, sizeof(void*)*7 + 8, x_251);
lean_ctor_set_uint8(x_314, sizeof(void*)*7 + 9, x_293);
lean_ctor_set_uint8(x_314, sizeof(void*)*7 + 10, x_294);
lean_inc(x_239);
lean_inc_ref(x_238);
lean_inc(x_237);
lean_inc_ref(x_234);
lean_inc(x_246);
x_315 = l_Lean_Meta_kabstract(x_246, x_234, x_250, x_314, x_237, x_238, x_239, x_247);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; uint8_t x_318; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec_ref(x_315);
x_318 = l_Lean_Expr_hasLooseBVars(x_316);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_316);
lean_dec(x_246);
lean_dec_ref(x_235);
lean_dec_ref(x_232);
lean_dec_ref(x_231);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_50);
lean_dec_ref(x_3);
x_319 = l_Lean_MVarId_rewrite___lam__1___closed__28;
x_320 = l_Lean_indentExpr(x_234);
lean_ctor_set_tag(x_243, 7);
lean_ctor_set(x_243, 1, x_320);
lean_ctor_set(x_243, 0, x_319);
x_321 = l_Lean_MVarId_rewrite___lam__1___closed__4;
x_322 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_322, 0, x_243);
lean_ctor_set(x_322, 1, x_321);
x_323 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_323, 0, x_322);
x_324 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_323, x_236, x_237, x_238, x_239, x_317);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_327 = x_324;
} else {
 lean_dec_ref(x_324);
 x_327 = lean_box(0);
}
if (lean_is_scalar(x_327)) {
 x_328 = lean_alloc_ctor(1, 2, 0);
} else {
 x_328 = x_327;
}
lean_ctor_set(x_328, 0, x_325);
lean_ctor_set(x_328, 1, x_326);
return x_328;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; 
lean_free_object(x_243);
x_329 = lean_expr_instantiate1(x_316, x_235);
x_330 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__0___redArg(x_329, x_237, x_317);
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec_ref(x_330);
x_333 = l_Lean_Expr_hasBinderNameHint(x_235);
if (x_333 == 0)
{
lean_inc(x_316);
x_201 = x_316;
x_202 = x_235;
x_203 = x_232;
x_204 = x_234;
x_205 = x_246;
x_206 = x_231;
x_207 = x_316;
x_208 = x_331;
x_209 = x_236;
x_210 = x_237;
x_211 = x_238;
x_212 = x_239;
x_213 = x_332;
goto block_230;
}
else
{
lean_object* x_334; 
lean_inc(x_239);
lean_inc_ref(x_238);
x_334 = l_Lean_Expr_resolveBinderNameHint(x_331, x_238, x_239, x_332);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; 
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
lean_dec_ref(x_334);
lean_inc(x_316);
x_201 = x_316;
x_202 = x_235;
x_203 = x_232;
x_204 = x_234;
x_205 = x_246;
x_206 = x_231;
x_207 = x_316;
x_208 = x_335;
x_209 = x_236;
x_210 = x_237;
x_211 = x_238;
x_212 = x_239;
x_213 = x_336;
goto block_230;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_316);
lean_dec(x_246);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_235);
lean_dec_ref(x_234);
lean_dec_ref(x_232);
lean_dec_ref(x_231);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_50);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_337 = lean_ctor_get(x_334, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_334, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_339 = x_334;
} else {
 lean_dec_ref(x_334);
 x_339 = lean_box(0);
}
if (lean_is_scalar(x_339)) {
 x_340 = lean_alloc_ctor(1, 2, 0);
} else {
 x_340 = x_339;
}
lean_ctor_set(x_340, 0, x_337);
lean_ctor_set(x_340, 1, x_338);
return x_340;
}
}
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_free_object(x_243);
lean_dec(x_246);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_235);
lean_dec_ref(x_234);
lean_dec_ref(x_232);
lean_dec_ref(x_231);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_50);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_341 = lean_ctor_get(x_315, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_315, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_343 = x_315;
} else {
 lean_dec_ref(x_315);
 x_343 = lean_box(0);
}
if (lean_is_scalar(x_343)) {
 x_344 = lean_alloc_ctor(1, 2, 0);
} else {
 x_344 = x_343;
}
lean_ctor_set(x_344, 0, x_341);
lean_ctor_set(x_344, 1, x_342);
return x_344;
}
}
}
else
{
lean_object* x_345; lean_object* x_346; uint8_t x_347; uint8_t x_348; lean_object* x_349; uint8_t x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; uint8_t x_358; uint8_t x_359; uint8_t x_360; uint8_t x_361; uint8_t x_362; uint8_t x_363; uint8_t x_364; uint8_t x_365; uint8_t x_366; uint8_t x_367; uint8_t x_368; uint8_t x_369; uint8_t x_370; uint8_t x_371; uint8_t x_372; uint8_t x_373; uint8_t x_374; uint8_t x_375; lean_object* x_376; lean_object* x_377; uint64_t x_378; lean_object* x_379; lean_object* x_380; 
x_345 = lean_ctor_get(x_243, 0);
x_346 = lean_ctor_get(x_243, 1);
lean_inc(x_346);
lean_inc(x_345);
lean_dec(x_243);
x_347 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_348 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_349 = lean_ctor_get(x_5, 0);
lean_inc(x_349);
lean_dec_ref(x_5);
x_350 = lean_ctor_get_uint8(x_236, sizeof(void*)*7 + 8);
x_351 = lean_ctor_get(x_236, 1);
lean_inc(x_351);
x_352 = lean_ctor_get(x_236, 2);
lean_inc_ref(x_352);
x_353 = lean_ctor_get(x_236, 3);
lean_inc_ref(x_353);
x_354 = lean_ctor_get(x_236, 4);
lean_inc(x_354);
x_355 = lean_ctor_get(x_236, 5);
lean_inc(x_355);
x_356 = lean_ctor_get(x_236, 6);
lean_inc(x_356);
x_357 = lean_ctor_get_uint8(x_236, sizeof(void*)*7 + 9);
x_358 = lean_ctor_get_uint8(x_236, sizeof(void*)*7 + 10);
x_359 = lean_ctor_get_uint8(x_244, 0);
x_360 = lean_ctor_get_uint8(x_244, 1);
x_361 = lean_ctor_get_uint8(x_244, 2);
x_362 = lean_ctor_get_uint8(x_244, 3);
x_363 = lean_ctor_get_uint8(x_244, 4);
x_364 = lean_ctor_get_uint8(x_244, 5);
x_365 = lean_ctor_get_uint8(x_244, 6);
x_366 = lean_ctor_get_uint8(x_244, 7);
x_367 = lean_ctor_get_uint8(x_244, 10);
x_368 = lean_ctor_get_uint8(x_244, 11);
x_369 = lean_ctor_get_uint8(x_244, 12);
x_370 = lean_ctor_get_uint8(x_244, 13);
x_371 = lean_ctor_get_uint8(x_244, 14);
x_372 = lean_ctor_get_uint8(x_244, 15);
x_373 = lean_ctor_get_uint8(x_244, 16);
x_374 = lean_ctor_get_uint8(x_244, 17);
x_375 = lean_ctor_get_uint8(x_244, 18);
if (lean_is_exclusive(x_244)) {
 x_376 = x_244;
} else {
 lean_dec_ref(x_244);
 x_376 = lean_box(0);
}
if (lean_is_scalar(x_376)) {
 x_377 = lean_alloc_ctor(0, 0, 19);
} else {
 x_377 = x_376;
}
lean_ctor_set_uint8(x_377, 0, x_359);
lean_ctor_set_uint8(x_377, 1, x_360);
lean_ctor_set_uint8(x_377, 2, x_361);
lean_ctor_set_uint8(x_377, 3, x_362);
lean_ctor_set_uint8(x_377, 4, x_363);
lean_ctor_set_uint8(x_377, 5, x_364);
lean_ctor_set_uint8(x_377, 6, x_365);
lean_ctor_set_uint8(x_377, 7, x_366);
lean_ctor_set_uint8(x_377, 8, x_348);
lean_ctor_set_uint8(x_377, 9, x_347);
lean_ctor_set_uint8(x_377, 10, x_367);
lean_ctor_set_uint8(x_377, 11, x_368);
lean_ctor_set_uint8(x_377, 12, x_369);
lean_ctor_set_uint8(x_377, 13, x_370);
lean_ctor_set_uint8(x_377, 14, x_371);
lean_ctor_set_uint8(x_377, 15, x_372);
lean_ctor_set_uint8(x_377, 16, x_373);
lean_ctor_set_uint8(x_377, 17, x_374);
lean_ctor_set_uint8(x_377, 18, x_375);
x_378 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_377);
x_379 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set(x_379, 1, x_351);
lean_ctor_set(x_379, 2, x_352);
lean_ctor_set(x_379, 3, x_353);
lean_ctor_set(x_379, 4, x_354);
lean_ctor_set(x_379, 5, x_355);
lean_ctor_set(x_379, 6, x_356);
lean_ctor_set_uint64(x_379, sizeof(void*)*7, x_378);
lean_ctor_set_uint8(x_379, sizeof(void*)*7 + 8, x_350);
lean_ctor_set_uint8(x_379, sizeof(void*)*7 + 9, x_357);
lean_ctor_set_uint8(x_379, sizeof(void*)*7 + 10, x_358);
lean_inc(x_239);
lean_inc_ref(x_238);
lean_inc(x_237);
lean_inc_ref(x_234);
lean_inc(x_345);
x_380 = l_Lean_Meta_kabstract(x_345, x_234, x_349, x_379, x_237, x_238, x_239, x_346);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; uint8_t x_383; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
lean_dec_ref(x_380);
x_383 = l_Lean_Expr_hasLooseBVars(x_381);
if (x_383 == 0)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
lean_dec(x_381);
lean_dec(x_345);
lean_dec_ref(x_235);
lean_dec_ref(x_232);
lean_dec_ref(x_231);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_50);
lean_dec_ref(x_3);
x_384 = l_Lean_MVarId_rewrite___lam__1___closed__28;
x_385 = l_Lean_indentExpr(x_234);
x_386 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_386, 0, x_384);
lean_ctor_set(x_386, 1, x_385);
x_387 = l_Lean_MVarId_rewrite___lam__1___closed__4;
x_388 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_387);
x_389 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_389, 0, x_388);
x_390 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_389, x_236, x_237, x_238, x_239, x_382);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 x_393 = x_390;
} else {
 lean_dec_ref(x_390);
 x_393 = lean_box(0);
}
if (lean_is_scalar(x_393)) {
 x_394 = lean_alloc_ctor(1, 2, 0);
} else {
 x_394 = x_393;
}
lean_ctor_set(x_394, 0, x_391);
lean_ctor_set(x_394, 1, x_392);
return x_394;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; 
x_395 = lean_expr_instantiate1(x_381, x_235);
x_396 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__0___redArg(x_395, x_237, x_382);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
lean_dec_ref(x_396);
x_399 = l_Lean_Expr_hasBinderNameHint(x_235);
if (x_399 == 0)
{
lean_inc(x_381);
x_201 = x_381;
x_202 = x_235;
x_203 = x_232;
x_204 = x_234;
x_205 = x_345;
x_206 = x_231;
x_207 = x_381;
x_208 = x_397;
x_209 = x_236;
x_210 = x_237;
x_211 = x_238;
x_212 = x_239;
x_213 = x_398;
goto block_230;
}
else
{
lean_object* x_400; 
lean_inc(x_239);
lean_inc_ref(x_238);
x_400 = l_Lean_Expr_resolveBinderNameHint(x_397, x_238, x_239, x_398);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; lean_object* x_402; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_400, 1);
lean_inc(x_402);
lean_dec_ref(x_400);
lean_inc(x_381);
x_201 = x_381;
x_202 = x_235;
x_203 = x_232;
x_204 = x_234;
x_205 = x_345;
x_206 = x_231;
x_207 = x_381;
x_208 = x_401;
x_209 = x_236;
x_210 = x_237;
x_211 = x_238;
x_212 = x_239;
x_213 = x_402;
goto block_230;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_381);
lean_dec(x_345);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_235);
lean_dec_ref(x_234);
lean_dec_ref(x_232);
lean_dec_ref(x_231);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_50);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_403 = lean_ctor_get(x_400, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_400, 1);
lean_inc(x_404);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 lean_ctor_release(x_400, 1);
 x_405 = x_400;
} else {
 lean_dec_ref(x_400);
 x_405 = lean_box(0);
}
if (lean_is_scalar(x_405)) {
 x_406 = lean_alloc_ctor(1, 2, 0);
} else {
 x_406 = x_405;
}
lean_ctor_set(x_406, 0, x_403);
lean_ctor_set(x_406, 1, x_404);
return x_406;
}
}
}
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
lean_dec(x_345);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_235);
lean_dec_ref(x_234);
lean_dec_ref(x_232);
lean_dec_ref(x_231);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_50);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_407 = lean_ctor_get(x_380, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_380, 1);
lean_inc(x_408);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_409 = x_380;
} else {
 lean_dec_ref(x_380);
 x_409 = lean_box(0);
}
if (lean_is_scalar(x_409)) {
 x_410 = lean_alloc_ctor(1, 2, 0);
} else {
 x_410 = x_409;
}
lean_ctor_set(x_410, 0, x_407);
lean_ctor_set(x_410, 1, x_408);
return x_410;
}
}
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; 
lean_dec_ref(x_235);
lean_dec_ref(x_232);
lean_dec_ref(x_231);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_50);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_411 = l_Lean_MVarId_rewrite___lam__1___closed__30;
x_412 = l_Lean_indentExpr(x_234);
x_413 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_412);
x_414 = l_Lean_MVarId_rewrite___lam__1___closed__32;
x_415 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_415, 0, x_413);
lean_ctor_set(x_415, 1, x_414);
x_416 = l_Lean_indentExpr(x_233);
x_417 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_417, 0, x_415);
lean_ctor_set(x_417, 1, x_416);
x_418 = l_Lean_MVarId_rewrite___lam__1___closed__4;
x_419 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_419, 0, x_417);
lean_ctor_set(x_419, 1, x_418);
x_420 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_420, 0, x_419);
x_421 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_420, x_236, x_237, x_238, x_239, x_240);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
x_422 = !lean_is_exclusive(x_421);
if (x_422 == 0)
{
return x_421;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_421, 0);
x_424 = lean_ctor_get(x_421, 1);
lean_inc(x_424);
lean_inc(x_423);
lean_dec(x_421);
x_425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_424);
return x_425;
}
}
}
block_472:
{
lean_object* x_434; 
lean_inc(x_432);
lean_inc_ref(x_431);
lean_inc(x_430);
lean_inc_ref(x_429);
lean_inc_ref(x_428);
x_434 = l_Lean_Meta_matchEq_x3f(x_428, x_429, x_430, x_431, x_432, x_433);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; 
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
lean_dec_ref(x_427);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_50);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_436 = lean_ctor_get(x_434, 1);
lean_inc(x_436);
lean_dec_ref(x_434);
x_437 = l_Lean_MVarId_rewrite___lam__1___closed__34;
x_438 = l_Lean_indentExpr(x_428);
x_439 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_439, 0, x_437);
lean_ctor_set(x_439, 1, x_438);
x_440 = l_Lean_MVarId_rewrite___lam__1___closed__4;
x_441 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_440);
x_442 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_442, 0, x_441);
x_443 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_442, x_429, x_430, x_431, x_432, x_436);
lean_dec(x_432);
lean_dec_ref(x_431);
lean_dec(x_430);
lean_dec_ref(x_429);
return x_443;
}
else
{
lean_object* x_444; lean_object* x_445; 
x_444 = lean_ctor_get(x_435, 0);
lean_inc(x_444);
lean_dec(x_435);
x_445 = lean_ctor_get(x_444, 1);
lean_inc(x_445);
if (x_6 == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_446 = lean_ctor_get(x_434, 1);
lean_inc(x_446);
lean_dec_ref(x_434);
x_447 = lean_ctor_get(x_444, 0);
lean_inc(x_447);
lean_dec(x_444);
x_448 = lean_ctor_get(x_445, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_445, 1);
lean_inc(x_449);
lean_dec(x_445);
x_231 = x_447;
x_232 = x_427;
x_233 = x_428;
x_234 = x_448;
x_235 = x_449;
x_236 = x_429;
x_237 = x_430;
x_238 = x_431;
x_239 = x_432;
x_240 = x_446;
goto block_426;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec_ref(x_428);
x_450 = lean_ctor_get(x_434, 1);
lean_inc(x_450);
lean_dec_ref(x_434);
x_451 = lean_ctor_get(x_444, 0);
lean_inc(x_451);
lean_dec(x_444);
x_452 = lean_ctor_get(x_445, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_445, 1);
lean_inc(x_453);
lean_dec(x_445);
lean_inc(x_432);
lean_inc_ref(x_431);
lean_inc(x_430);
lean_inc_ref(x_429);
x_454 = l_Lean_Meta_mkEqSymm(x_427, x_429, x_430, x_431, x_432, x_450);
if (lean_obj_tag(x_454) == 0)
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_455 = lean_ctor_get(x_454, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_454, 1);
lean_inc(x_456);
lean_dec_ref(x_454);
lean_inc(x_432);
lean_inc_ref(x_431);
lean_inc(x_430);
lean_inc_ref(x_429);
lean_inc(x_452);
lean_inc(x_453);
x_457 = l_Lean_Meta_mkEq(x_453, x_452, x_429, x_430, x_431, x_432, x_456);
if (lean_obj_tag(x_457) == 0)
{
lean_object* x_458; lean_object* x_459; 
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_457, 1);
lean_inc(x_459);
lean_dec_ref(x_457);
x_231 = x_451;
x_232 = x_455;
x_233 = x_458;
x_234 = x_453;
x_235 = x_452;
x_236 = x_429;
x_237 = x_430;
x_238 = x_431;
x_239 = x_432;
x_240 = x_459;
goto block_426;
}
else
{
uint8_t x_460; 
lean_dec(x_455);
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_432);
lean_dec_ref(x_431);
lean_dec(x_430);
lean_dec_ref(x_429);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_50);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_460 = !lean_is_exclusive(x_457);
if (x_460 == 0)
{
return x_457;
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_461 = lean_ctor_get(x_457, 0);
x_462 = lean_ctor_get(x_457, 1);
lean_inc(x_462);
lean_inc(x_461);
lean_dec(x_457);
x_463 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_463, 0, x_461);
lean_ctor_set(x_463, 1, x_462);
return x_463;
}
}
}
else
{
uint8_t x_464; 
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_432);
lean_dec_ref(x_431);
lean_dec(x_430);
lean_dec_ref(x_429);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_50);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_464 = !lean_is_exclusive(x_454);
if (x_464 == 0)
{
return x_454;
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_465 = lean_ctor_get(x_454, 0);
x_466 = lean_ctor_get(x_454, 1);
lean_inc(x_466);
lean_inc(x_465);
lean_dec(x_454);
x_467 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_467, 0, x_465);
lean_ctor_set(x_467, 1, x_466);
return x_467;
}
}
}
}
}
else
{
uint8_t x_468; 
lean_dec(x_432);
lean_dec_ref(x_431);
lean_dec(x_430);
lean_dec_ref(x_429);
lean_dec_ref(x_428);
lean_dec_ref(x_427);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_50);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_468 = !lean_is_exclusive(x_434);
if (x_468 == 0)
{
return x_434;
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_469 = lean_ctor_get(x_434, 0);
x_470 = lean_ctor_get(x_434, 1);
lean_inc(x_470);
lean_inc(x_469);
lean_dec(x_434);
x_471 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_471, 0, x_469);
lean_ctor_set(x_471, 1, x_470);
return x_471;
}
}
}
}
else
{
uint8_t x_489; 
lean_dec(x_50);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_489 = !lean_is_exclusive(x_53);
if (x_489 == 0)
{
return x_53;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_490 = lean_ctor_get(x_53, 0);
x_491 = lean_ctor_get(x_53, 1);
lean_inc(x_491);
lean_inc(x_490);
lean_dec(x_53);
x_492 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_492, 0, x_490);
lean_ctor_set(x_492, 1, x_491);
return x_492;
}
}
}
else
{
uint8_t x_493; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_493 = !lean_is_exclusive(x_44);
if (x_493 == 0)
{
return x_44;
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_494 = lean_ctor_get(x_44, 0);
x_495 = lean_ctor_get(x_44, 1);
lean_inc(x_495);
lean_inc(x_494);
lean_dec(x_44);
x_496 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_496, 0, x_494);
lean_ctor_set(x_496, 1, x_495);
return x_496;
}
}
}
else
{
uint8_t x_497; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_497 = !lean_is_exclusive(x_42);
if (x_497 == 0)
{
return x_42;
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_498 = lean_ctor_get(x_42, 0);
x_499 = lean_ctor_get(x_42, 1);
lean_inc(x_499);
lean_inc(x_498);
lean_dec(x_42);
x_500 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_500, 0, x_498);
lean_ctor_set(x_500, 1, x_499);
return x_500;
}
}
block_21:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = l_Array_append___redArg(x_13, x_16);
lean_dec_ref(x_16);
x_18 = lean_array_to_list(x_17);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
block_41:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = l_Lean_Meta_getMVarsNoDelayed(x_3, x_25, x_23, x_24, x_22, x_31);
lean_dec(x_22);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_25);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = lean_array_get_size(x_33);
x_36 = lean_mk_empty_array_with_capacity(x_27);
x_37 = lean_nat_dec_lt(x_27, x_35);
if (x_37 == 0)
{
lean_dec(x_35);
lean_dec(x_33);
x_12 = x_34;
x_13 = x_30;
x_14 = x_26;
x_15 = x_28;
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
x_13 = x_30;
x_14 = x_26;
x_15 = x_28;
x_16 = x_36;
goto block_21;
}
else
{
size_t x_39; lean_object* x_40; 
x_39 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_40 = l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__2(x_30, x_33, x_29, x_39, x_36);
lean_dec(x_33);
x_12 = x_34;
x_13 = x_30;
x_14 = x_26;
x_15 = x_28;
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
lean_dec_ref(x_2);
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_rewrite___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
x_13 = l_Lean_MVarId_rewrite___lam__1(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
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
