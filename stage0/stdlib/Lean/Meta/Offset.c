// Lean compiler output
// Module: Lean.Meta.Offset
// Imports: Init.Control.Option Lean.Data.LBool Lean.Meta.InferType Lean.Meta.NatInstTesters Lean.Util.SafeExponentiation
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
lean_object* l_Lean_Meta_isInstHMulNat___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstAddNat___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__39;
lean_object* l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
uint8_t l_Bool_toLBool(uint8_t);
static lean_object* l_Lean_Meta_evalNat_visit___closed__1;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat_evalPow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isOffset_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
extern lean_object* l_Lean_Nat_mkInstAdd;
uint8_t l_Lean_Expr_isApp(lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__18;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__5;
lean_object* l_OptionT_instMonad___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isDefEqOffset___lam__0___closed__0;
static lean_object* l_Lean_Meta_evalNat_visit___closed__45;
lean_object* l_Lean_Meta_isInstModNat___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstMulNat___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__46;
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstDivNat___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__41;
static lean_object* l_Lean_Meta_evalNat_visit___closed__6;
lean_object* l_Lean_Meta_isInstHPowNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_lift___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__48;
static lean_object* l_Lean_Meta_evalNat_visit___closed__22;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_checkExponent(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__33;
lean_object* l_OptionT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_is_expr_def_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__3;
uint8_t l_Lean_Expr_isMVar(lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__28;
lean_object* l_Lean_Meta_isExprDefEqAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__7;
static lean_object* l_Lean_Meta_evalNat_visit___closed__19;
static lean_object* l_Lean_Meta_evalNat_visit___closed__35;
static lean_object* l_Lean_Meta_evalNat_visit___closed__13;
static lean_object* l_Lean_Meta_evalNat_visit___closed__36;
static lean_object* l_Lean_Meta_evalNat_visit___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__4;
static lean_object* l_Lean_Meta_evalNat_visit___closed__43;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isDefEqOffset___lam__0___closed__1;
lean_object* l_Lean_Meta_isInstNatPowNat___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_lift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkInstHAdd;
static lean_object* l_Lean_Meta_evalNat_visit___closed__47;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0;
static lean_object* l_Lean_Meta_evalNat_visit___closed__17;
lean_object* l_OptionT_instMonad___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__0;
static lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6;
static lean_object* l_Lean_Meta_evalNat_visit___closed__20;
lean_object* l_Lean_Meta_isInstOfNatNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat_evalPow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_isInstSubNat___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__32;
static lean_object* l_Lean_Meta_evalNat_visit___closed__29;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__27;
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__15;
lean_object* l_Lean_Meta_isInstHAddNat___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_pure(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__42;
static lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5;
static lean_object* l_Lean_Meta_evalNat_visit___closed__9;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHModNat___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__24;
static lean_object* l_Lean_Meta_evalNat_visit___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__31;
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__34;
static lean_object* l_Lean_Meta_evalNat_visit___closed__12;
static lean_object* l_Lean_Meta_evalNat_visit___closed__21;
lean_object* l_OptionT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__37;
static lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2;
static lean_object* l_Lean_Meta_evalNat_visit___closed__11;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__44;
static lean_object* l_Lean_Meta_evalNat___closed__2;
static lean_object* l_Lean_Meta_evalNat_visit___closed__40;
static lean_object* l_Lean_Meta_evalNat_visit___closed__25;
static lean_object* l_Lean_Meta_evalNat_visit___closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat___closed__0;
static lean_object* l_Lean_Meta_evalNat_visit___closed__10;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMCtxMetaM;
static lean_object* l_Lean_Meta_evalNat_visit___closed__2;
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHSubNat___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHDivNat___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3;
static lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1;
lean_object* l_Lean_Meta_getConfig___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstPowNat___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_evalNat_visit___closed__30;
static lean_object* l_Lean_Meta_evalNat_visit___closed__23;
static lean_object* l_Lean_Meta_evalNat_visit___closed__26;
static lean_object* l_Lean_Meta_evalNat_visit___closed__38;
static lean_object* _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0;
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4;
x_2 = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1;
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 2);
x_15 = lean_ctor_get(x_10, 3);
x_16 = lean_ctor_get(x_10, 4);
x_17 = lean_ctor_get(x_10, 1);
lean_dec(x_17);
x_18 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2;
x_19 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3;
lean_inc_ref(x_13);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_20, 0, x_13);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_16);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_15);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_25, 0, x_14);
lean_ctor_set(x_10, 4, x_23);
lean_ctor_set(x_10, 3, x_24);
lean_ctor_set(x_10, 2, x_25);
lean_ctor_set(x_10, 1, x_18);
lean_ctor_set(x_10, 0, x_22);
lean_ctor_set(x_8, 1, x_19);
x_26 = l_ReaderT_instMonad___redArg(x_8);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_31 = lean_ctor_get(x_28, 0);
x_32 = lean_ctor_get(x_28, 2);
x_33 = lean_ctor_get(x_28, 3);
x_34 = lean_ctor_get(x_28, 4);
x_35 = lean_ctor_get(x_28, 1);
lean_dec(x_35);
x_36 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4;
x_37 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5;
lean_inc_ref(x_31);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_38, 0, x_31);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_31);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_34);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_42, 0, x_33);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_43, 0, x_32);
lean_ctor_set(x_28, 4, x_41);
lean_ctor_set(x_28, 3, x_42);
lean_ctor_set(x_28, 2, x_43);
lean_ctor_set(x_28, 1, x_36);
lean_ctor_set(x_28, 0, x_40);
lean_ctor_set(x_26, 1, x_37);
lean_inc_ref(x_26);
x_44 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(x_44, 0, x_26);
lean_inc_ref(x_26);
x_45 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_45, 0, x_26);
lean_inc_ref(x_26);
x_46 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(x_46, 0, x_26);
lean_inc_ref(x_26);
x_47 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(x_47, 0, x_26);
lean_inc_ref(x_26);
x_48 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(x_48, 0, x_26);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_45);
lean_inc_ref(x_26);
x_50 = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(x_50, 0, lean_box(0));
lean_closure_set(x_50, 1, x_26);
x_51 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_46);
lean_ctor_set(x_51, 3, x_47);
lean_ctor_set(x_51, 4, x_48);
lean_inc_ref(x_26);
x_52 = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(x_52, 0, lean_box(0));
lean_closure_set(x_52, 1, x_26);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Meta_instMonadMCtxMetaM;
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
x_58 = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(x_58, 0, lean_box(0));
lean_closure_set(x_58, 1, x_26);
x_59 = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_59, 0, x_57);
lean_closure_set(x_59, 1, x_58);
x_60 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6;
x_61 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 4);
lean_closure_set(x_61, 0, lean_box(0));
lean_closure_set(x_61, 1, lean_box(0));
lean_closure_set(x_61, 2, x_56);
lean_closure_set(x_61, 3, x_60);
lean_ctor_set(x_54, 1, x_59);
lean_ctor_set(x_54, 0, x_61);
x_62 = l_Lean_instantiateMVars___redArg(x_53, x_54, x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_63 = lean_apply_5(x_62, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_63, 0);
lean_dec(x_66);
x_67 = lean_box(0);
lean_ctor_set(x_63, 0, x_67);
return x_63;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_dec(x_63);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_63);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_72 = lean_ctor_get(x_63, 1);
x_73 = lean_ctor_get(x_63, 0);
lean_dec(x_73);
x_74 = lean_ctor_get(x_64, 0);
lean_inc(x_74);
lean_dec(x_64);
x_75 = l_Lean_Expr_getAppFn(x_74);
x_76 = l_Lean_Expr_isMVar(x_75);
lean_dec_ref(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
lean_free_object(x_63);
x_77 = lean_apply_6(x_2, x_74, x_3, x_4, x_5, x_6, x_72);
return x_77;
}
else
{
lean_object* x_78; 
lean_dec(x_74);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_78 = lean_box(0);
lean_ctor_set(x_63, 0, x_78);
return x_63;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_79 = lean_ctor_get(x_63, 1);
lean_inc(x_79);
lean_dec(x_63);
x_80 = lean_ctor_get(x_64, 0);
lean_inc(x_80);
lean_dec(x_64);
x_81 = l_Lean_Expr_getAppFn(x_80);
x_82 = l_Lean_Expr_isMVar(x_81);
lean_dec_ref(x_81);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_apply_6(x_2, x_80, x_3, x_4, x_5, x_6, x_79);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_80);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_79);
return x_85;
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_63);
if (x_86 == 0)
{
return x_63;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_63, 0);
x_88 = lean_ctor_get(x_63, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_63);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_90 = lean_ctor_get(x_54, 0);
x_91 = lean_ctor_get(x_54, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_54);
x_92 = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(x_92, 0, lean_box(0));
lean_closure_set(x_92, 1, x_26);
x_93 = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_93, 0, x_91);
lean_closure_set(x_93, 1, x_92);
x_94 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6;
x_95 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 4);
lean_closure_set(x_95, 0, lean_box(0));
lean_closure_set(x_95, 1, lean_box(0));
lean_closure_set(x_95, 2, x_90);
lean_closure_set(x_95, 3, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
x_97 = l_Lean_instantiateMVars___redArg(x_53, x_96, x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_98 = lean_apply_5(x_97, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
 x_101 = lean_box(0);
}
x_102 = lean_box(0);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_104 = lean_ctor_get(x_98, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_105 = x_98;
} else {
 lean_dec_ref(x_98);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_99, 0);
lean_inc(x_106);
lean_dec(x_99);
x_107 = l_Lean_Expr_getAppFn(x_106);
x_108 = l_Lean_Expr_isMVar(x_107);
lean_dec_ref(x_107);
if (x_108 == 0)
{
lean_object* x_109; 
lean_dec(x_105);
x_109 = lean_apply_6(x_2, x_106, x_3, x_4, x_5, x_6, x_104);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_106);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_110 = lean_box(0);
if (lean_is_scalar(x_105)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_105;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_104);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_112 = lean_ctor_get(x_98, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_98, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_114 = x_98;
} else {
 lean_dec_ref(x_98);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_116 = lean_ctor_get(x_28, 0);
x_117 = lean_ctor_get(x_28, 2);
x_118 = lean_ctor_get(x_28, 3);
x_119 = lean_ctor_get(x_28, 4);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_28);
x_120 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4;
x_121 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5;
lean_inc_ref(x_116);
x_122 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_122, 0, x_116);
x_123 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_123, 0, x_116);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_125, 0, x_119);
x_126 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_126, 0, x_118);
x_127 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_127, 0, x_117);
x_128 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_128, 0, x_124);
lean_ctor_set(x_128, 1, x_120);
lean_ctor_set(x_128, 2, x_127);
lean_ctor_set(x_128, 3, x_126);
lean_ctor_set(x_128, 4, x_125);
lean_ctor_set(x_26, 1, x_121);
lean_ctor_set(x_26, 0, x_128);
lean_inc_ref(x_26);
x_129 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(x_129, 0, x_26);
lean_inc_ref(x_26);
x_130 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_130, 0, x_26);
lean_inc_ref(x_26);
x_131 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(x_131, 0, x_26);
lean_inc_ref(x_26);
x_132 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(x_132, 0, x_26);
lean_inc_ref(x_26);
x_133 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(x_133, 0, x_26);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set(x_134, 1, x_130);
lean_inc_ref(x_26);
x_135 = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(x_135, 0, lean_box(0));
lean_closure_set(x_135, 1, x_26);
x_136 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set(x_136, 2, x_131);
lean_ctor_set(x_136, 3, x_132);
lean_ctor_set(x_136, 4, x_133);
lean_inc_ref(x_26);
x_137 = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(x_137, 0, lean_box(0));
lean_closure_set(x_137, 1, x_26);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = l_Lean_Meta_instMonadMCtxMetaM;
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_142 = x_139;
} else {
 lean_dec_ref(x_139);
 x_142 = lean_box(0);
}
x_143 = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(x_143, 0, lean_box(0));
lean_closure_set(x_143, 1, x_26);
x_144 = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_144, 0, x_141);
lean_closure_set(x_144, 1, x_143);
x_145 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6;
x_146 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 4);
lean_closure_set(x_146, 0, lean_box(0));
lean_closure_set(x_146, 1, lean_box(0));
lean_closure_set(x_146, 2, x_140);
lean_closure_set(x_146, 3, x_145);
if (lean_is_scalar(x_142)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_142;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_144);
x_148 = l_Lean_instantiateMVars___redArg(x_138, x_147, x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_149 = lean_apply_5(x_148, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
 x_152 = lean_box(0);
}
x_153 = lean_box(0);
if (lean_is_scalar(x_152)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_152;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_151);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_155 = lean_ctor_get(x_149, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_156 = x_149;
} else {
 lean_dec_ref(x_149);
 x_156 = lean_box(0);
}
x_157 = lean_ctor_get(x_150, 0);
lean_inc(x_157);
lean_dec(x_150);
x_158 = l_Lean_Expr_getAppFn(x_157);
x_159 = l_Lean_Expr_isMVar(x_158);
lean_dec_ref(x_158);
if (x_159 == 0)
{
lean_object* x_160; 
lean_dec(x_156);
x_160 = lean_apply_6(x_2, x_157, x_3, x_4, x_5, x_6, x_155);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_157);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_161 = lean_box(0);
if (lean_is_scalar(x_156)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_156;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_155);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_163 = lean_ctor_get(x_149, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_149, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_165 = x_149;
} else {
 lean_dec_ref(x_149);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_167 = lean_ctor_get(x_26, 0);
lean_inc(x_167);
lean_dec(x_26);
x_168 = lean_ctor_get(x_167, 0);
lean_inc_ref(x_168);
x_169 = lean_ctor_get(x_167, 2);
lean_inc(x_169);
x_170 = lean_ctor_get(x_167, 3);
lean_inc(x_170);
x_171 = lean_ctor_get(x_167, 4);
lean_inc(x_171);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 lean_ctor_release(x_167, 2);
 lean_ctor_release(x_167, 3);
 lean_ctor_release(x_167, 4);
 x_172 = x_167;
} else {
 lean_dec_ref(x_167);
 x_172 = lean_box(0);
}
x_173 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4;
x_174 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5;
lean_inc_ref(x_168);
x_175 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_175, 0, x_168);
x_176 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_176, 0, x_168);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_178, 0, x_171);
x_179 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_179, 0, x_170);
x_180 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_180, 0, x_169);
if (lean_is_scalar(x_172)) {
 x_181 = lean_alloc_ctor(0, 5, 0);
} else {
 x_181 = x_172;
}
lean_ctor_set(x_181, 0, x_177);
lean_ctor_set(x_181, 1, x_173);
lean_ctor_set(x_181, 2, x_180);
lean_ctor_set(x_181, 3, x_179);
lean_ctor_set(x_181, 4, x_178);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_174);
lean_inc_ref(x_182);
x_183 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(x_183, 0, x_182);
lean_inc_ref(x_182);
x_184 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_184, 0, x_182);
lean_inc_ref(x_182);
x_185 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(x_185, 0, x_182);
lean_inc_ref(x_182);
x_186 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(x_186, 0, x_182);
lean_inc_ref(x_182);
x_187 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(x_187, 0, x_182);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_183);
lean_ctor_set(x_188, 1, x_184);
lean_inc_ref(x_182);
x_189 = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(x_189, 0, lean_box(0));
lean_closure_set(x_189, 1, x_182);
x_190 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
lean_ctor_set(x_190, 2, x_185);
lean_ctor_set(x_190, 3, x_186);
lean_ctor_set(x_190, 4, x_187);
lean_inc_ref(x_182);
x_191 = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(x_191, 0, lean_box(0));
lean_closure_set(x_191, 1, x_182);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_193 = l_Lean_Meta_instMonadMCtxMetaM;
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
x_197 = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(x_197, 0, lean_box(0));
lean_closure_set(x_197, 1, x_182);
x_198 = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_198, 0, x_195);
lean_closure_set(x_198, 1, x_197);
x_199 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6;
x_200 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 4);
lean_closure_set(x_200, 0, lean_box(0));
lean_closure_set(x_200, 1, lean_box(0));
lean_closure_set(x_200, 2, x_194);
lean_closure_set(x_200, 3, x_199);
if (lean_is_scalar(x_196)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_196;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_198);
x_202 = l_Lean_instantiateMVars___redArg(x_192, x_201, x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_203 = lean_apply_5(x_202, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_206 = x_203;
} else {
 lean_dec_ref(x_203);
 x_206 = lean_box(0);
}
x_207 = lean_box(0);
if (lean_is_scalar(x_206)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_206;
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_205);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_209 = lean_ctor_get(x_203, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_210 = x_203;
} else {
 lean_dec_ref(x_203);
 x_210 = lean_box(0);
}
x_211 = lean_ctor_get(x_204, 0);
lean_inc(x_211);
lean_dec(x_204);
x_212 = l_Lean_Expr_getAppFn(x_211);
x_213 = l_Lean_Expr_isMVar(x_212);
lean_dec_ref(x_212);
if (x_213 == 0)
{
lean_object* x_214; 
lean_dec(x_210);
x_214 = lean_apply_6(x_2, x_211, x_3, x_4, x_5, x_6, x_209);
return x_214;
}
else
{
lean_object* x_215; lean_object* x_216; 
lean_dec(x_211);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_215 = lean_box(0);
if (lean_is_scalar(x_210)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_210;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_209);
return x_216;
}
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_217 = lean_ctor_get(x_203, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_203, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_219 = x_203;
} else {
 lean_dec_ref(x_203);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_217);
lean_ctor_set(x_220, 1, x_218);
return x_220;
}
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_221 = lean_ctor_get(x_10, 0);
x_222 = lean_ctor_get(x_10, 2);
x_223 = lean_ctor_get(x_10, 3);
x_224 = lean_ctor_get(x_10, 4);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_10);
x_225 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2;
x_226 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3;
lean_inc_ref(x_221);
x_227 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_227, 0, x_221);
x_228 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_228, 0, x_221);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_230, 0, x_224);
x_231 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_231, 0, x_223);
x_232 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_232, 0, x_222);
x_233 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_233, 0, x_229);
lean_ctor_set(x_233, 1, x_225);
lean_ctor_set(x_233, 2, x_232);
lean_ctor_set(x_233, 3, x_231);
lean_ctor_set(x_233, 4, x_230);
lean_ctor_set(x_8, 1, x_226);
lean_ctor_set(x_8, 0, x_233);
x_234 = l_ReaderT_instMonad___redArg(x_8);
x_235 = lean_ctor_get(x_234, 0);
lean_inc_ref(x_235);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_236 = x_234;
} else {
 lean_dec_ref(x_234);
 x_236 = lean_box(0);
}
x_237 = lean_ctor_get(x_235, 0);
lean_inc_ref(x_237);
x_238 = lean_ctor_get(x_235, 2);
lean_inc(x_238);
x_239 = lean_ctor_get(x_235, 3);
lean_inc(x_239);
x_240 = lean_ctor_get(x_235, 4);
lean_inc(x_240);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 lean_ctor_release(x_235, 4);
 x_241 = x_235;
} else {
 lean_dec_ref(x_235);
 x_241 = lean_box(0);
}
x_242 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4;
x_243 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5;
lean_inc_ref(x_237);
x_244 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_244, 0, x_237);
x_245 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_245, 0, x_237);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_247, 0, x_240);
x_248 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_248, 0, x_239);
x_249 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_249, 0, x_238);
if (lean_is_scalar(x_241)) {
 x_250 = lean_alloc_ctor(0, 5, 0);
} else {
 x_250 = x_241;
}
lean_ctor_set(x_250, 0, x_246);
lean_ctor_set(x_250, 1, x_242);
lean_ctor_set(x_250, 2, x_249);
lean_ctor_set(x_250, 3, x_248);
lean_ctor_set(x_250, 4, x_247);
if (lean_is_scalar(x_236)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_236;
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_243);
lean_inc_ref(x_251);
x_252 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(x_252, 0, x_251);
lean_inc_ref(x_251);
x_253 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_253, 0, x_251);
lean_inc_ref(x_251);
x_254 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(x_254, 0, x_251);
lean_inc_ref(x_251);
x_255 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(x_255, 0, x_251);
lean_inc_ref(x_251);
x_256 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(x_256, 0, x_251);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_252);
lean_ctor_set(x_257, 1, x_253);
lean_inc_ref(x_251);
x_258 = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(x_258, 0, lean_box(0));
lean_closure_set(x_258, 1, x_251);
x_259 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
lean_ctor_set(x_259, 2, x_254);
lean_ctor_set(x_259, 3, x_255);
lean_ctor_set(x_259, 4, x_256);
lean_inc_ref(x_251);
x_260 = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(x_260, 0, lean_box(0));
lean_closure_set(x_260, 1, x_251);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
x_262 = l_Lean_Meta_instMonadMCtxMetaM;
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_265 = x_262;
} else {
 lean_dec_ref(x_262);
 x_265 = lean_box(0);
}
x_266 = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(x_266, 0, lean_box(0));
lean_closure_set(x_266, 1, x_251);
x_267 = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_267, 0, x_264);
lean_closure_set(x_267, 1, x_266);
x_268 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6;
x_269 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 4);
lean_closure_set(x_269, 0, lean_box(0));
lean_closure_set(x_269, 1, lean_box(0));
lean_closure_set(x_269, 2, x_263);
lean_closure_set(x_269, 3, x_268);
if (lean_is_scalar(x_265)) {
 x_270 = lean_alloc_ctor(0, 2, 0);
} else {
 x_270 = x_265;
}
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_267);
x_271 = l_Lean_instantiateMVars___redArg(x_261, x_270, x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_272 = lean_apply_5(x_271, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_275 = x_272;
} else {
 lean_dec_ref(x_272);
 x_275 = lean_box(0);
}
x_276 = lean_box(0);
if (lean_is_scalar(x_275)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_275;
}
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_274);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
x_278 = lean_ctor_get(x_272, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_279 = x_272;
} else {
 lean_dec_ref(x_272);
 x_279 = lean_box(0);
}
x_280 = lean_ctor_get(x_273, 0);
lean_inc(x_280);
lean_dec(x_273);
x_281 = l_Lean_Expr_getAppFn(x_280);
x_282 = l_Lean_Expr_isMVar(x_281);
lean_dec_ref(x_281);
if (x_282 == 0)
{
lean_object* x_283; 
lean_dec(x_279);
x_283 = lean_apply_6(x_2, x_280, x_3, x_4, x_5, x_6, x_278);
return x_283;
}
else
{
lean_object* x_284; lean_object* x_285; 
lean_dec(x_280);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_284 = lean_box(0);
if (lean_is_scalar(x_279)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_279;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_278);
return x_285;
}
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_286 = lean_ctor_get(x_272, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_272, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_288 = x_272;
} else {
 lean_dec_ref(x_272);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(1, 2, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_287);
return x_289;
}
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_290 = lean_ctor_get(x_8, 0);
lean_inc(x_290);
lean_dec(x_8);
x_291 = lean_ctor_get(x_290, 0);
lean_inc_ref(x_291);
x_292 = lean_ctor_get(x_290, 2);
lean_inc(x_292);
x_293 = lean_ctor_get(x_290, 3);
lean_inc(x_293);
x_294 = lean_ctor_get(x_290, 4);
lean_inc(x_294);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 lean_ctor_release(x_290, 2);
 lean_ctor_release(x_290, 3);
 lean_ctor_release(x_290, 4);
 x_295 = x_290;
} else {
 lean_dec_ref(x_290);
 x_295 = lean_box(0);
}
x_296 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2;
x_297 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3;
lean_inc_ref(x_291);
x_298 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_298, 0, x_291);
x_299 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_299, 0, x_291);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_299);
x_301 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_301, 0, x_294);
x_302 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_302, 0, x_293);
x_303 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_303, 0, x_292);
if (lean_is_scalar(x_295)) {
 x_304 = lean_alloc_ctor(0, 5, 0);
} else {
 x_304 = x_295;
}
lean_ctor_set(x_304, 0, x_300);
lean_ctor_set(x_304, 1, x_296);
lean_ctor_set(x_304, 2, x_303);
lean_ctor_set(x_304, 3, x_302);
lean_ctor_set(x_304, 4, x_301);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_297);
x_306 = l_ReaderT_instMonad___redArg(x_305);
x_307 = lean_ctor_get(x_306, 0);
lean_inc_ref(x_307);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 x_308 = x_306;
} else {
 lean_dec_ref(x_306);
 x_308 = lean_box(0);
}
x_309 = lean_ctor_get(x_307, 0);
lean_inc_ref(x_309);
x_310 = lean_ctor_get(x_307, 2);
lean_inc(x_310);
x_311 = lean_ctor_get(x_307, 3);
lean_inc(x_311);
x_312 = lean_ctor_get(x_307, 4);
lean_inc(x_312);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 lean_ctor_release(x_307, 2);
 lean_ctor_release(x_307, 3);
 lean_ctor_release(x_307, 4);
 x_313 = x_307;
} else {
 lean_dec_ref(x_307);
 x_313 = lean_box(0);
}
x_314 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4;
x_315 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5;
lean_inc_ref(x_309);
x_316 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_316, 0, x_309);
x_317 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_317, 0, x_309);
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
x_319 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_319, 0, x_312);
x_320 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_320, 0, x_311);
x_321 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_321, 0, x_310);
if (lean_is_scalar(x_313)) {
 x_322 = lean_alloc_ctor(0, 5, 0);
} else {
 x_322 = x_313;
}
lean_ctor_set(x_322, 0, x_318);
lean_ctor_set(x_322, 1, x_314);
lean_ctor_set(x_322, 2, x_321);
lean_ctor_set(x_322, 3, x_320);
lean_ctor_set(x_322, 4, x_319);
if (lean_is_scalar(x_308)) {
 x_323 = lean_alloc_ctor(0, 2, 0);
} else {
 x_323 = x_308;
}
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_315);
lean_inc_ref(x_323);
x_324 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(x_324, 0, x_323);
lean_inc_ref(x_323);
x_325 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_325, 0, x_323);
lean_inc_ref(x_323);
x_326 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(x_326, 0, x_323);
lean_inc_ref(x_323);
x_327 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(x_327, 0, x_323);
lean_inc_ref(x_323);
x_328 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(x_328, 0, x_323);
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_324);
lean_ctor_set(x_329, 1, x_325);
lean_inc_ref(x_323);
x_330 = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(x_330, 0, lean_box(0));
lean_closure_set(x_330, 1, x_323);
x_331 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
lean_ctor_set(x_331, 2, x_326);
lean_ctor_set(x_331, 3, x_327);
lean_ctor_set(x_331, 4, x_328);
lean_inc_ref(x_323);
x_332 = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(x_332, 0, lean_box(0));
lean_closure_set(x_332, 1, x_323);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
x_334 = l_Lean_Meta_instMonadMCtxMetaM;
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_337 = x_334;
} else {
 lean_dec_ref(x_334);
 x_337 = lean_box(0);
}
x_338 = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(x_338, 0, lean_box(0));
lean_closure_set(x_338, 1, x_323);
x_339 = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_339, 0, x_336);
lean_closure_set(x_339, 1, x_338);
x_340 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6;
x_341 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 4);
lean_closure_set(x_341, 0, lean_box(0));
lean_closure_set(x_341, 1, lean_box(0));
lean_closure_set(x_341, 2, x_335);
lean_closure_set(x_341, 3, x_340);
if (lean_is_scalar(x_337)) {
 x_342 = lean_alloc_ctor(0, 2, 0);
} else {
 x_342 = x_337;
}
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_339);
x_343 = l_Lean_instantiateMVars___redArg(x_333, x_342, x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_344 = lean_apply_5(x_343, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; 
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_346 = lean_ctor_get(x_344, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_347 = x_344;
} else {
 lean_dec_ref(x_344);
 x_347 = lean_box(0);
}
x_348 = lean_box(0);
if (lean_is_scalar(x_347)) {
 x_349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_349 = x_347;
}
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_346);
return x_349;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; 
x_350 = lean_ctor_get(x_344, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_351 = x_344;
} else {
 lean_dec_ref(x_344);
 x_351 = lean_box(0);
}
x_352 = lean_ctor_get(x_345, 0);
lean_inc(x_352);
lean_dec(x_345);
x_353 = l_Lean_Expr_getAppFn(x_352);
x_354 = l_Lean_Expr_isMVar(x_353);
lean_dec_ref(x_353);
if (x_354 == 0)
{
lean_object* x_355; 
lean_dec(x_351);
x_355 = lean_apply_6(x_2, x_352, x_3, x_4, x_5, x_6, x_350);
return x_355;
}
else
{
lean_object* x_356; lean_object* x_357; 
lean_dec(x_352);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_356 = lean_box(0);
if (lean_is_scalar(x_351)) {
 x_357 = lean_alloc_ctor(0, 2, 0);
} else {
 x_357 = x_351;
}
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_350);
return x_357;
}
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_358 = lean_ctor_get(x_344, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_344, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_360 = x_344;
} else {
 lean_dec_ref(x_344);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 2, 0);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_358);
lean_ctor_set(x_361, 1, x_359);
return x_361;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1;
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 2);
x_16 = lean_ctor_get(x_11, 3);
x_17 = lean_ctor_get(x_11, 4);
x_18 = lean_ctor_get(x_11, 1);
lean_dec(x_18);
x_19 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2;
x_20 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3;
lean_inc_ref(x_14);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_21, 0, x_14);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_17);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_16);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_26, 0, x_15);
lean_ctor_set(x_11, 4, x_24);
lean_ctor_set(x_11, 3, x_25);
lean_ctor_set(x_11, 2, x_26);
lean_ctor_set(x_11, 1, x_19);
lean_ctor_set(x_11, 0, x_23);
lean_ctor_set(x_9, 1, x_20);
x_27 = l_ReaderT_instMonad___redArg(x_9);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 2);
x_34 = lean_ctor_get(x_29, 3);
x_35 = lean_ctor_get(x_29, 4);
x_36 = lean_ctor_get(x_29, 1);
lean_dec(x_36);
x_37 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4;
x_38 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5;
lean_inc_ref(x_32);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_39, 0, x_32);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_40, 0, x_32);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_35);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_43, 0, x_34);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_44, 0, x_33);
lean_ctor_set(x_29, 4, x_42);
lean_ctor_set(x_29, 3, x_43);
lean_ctor_set(x_29, 2, x_44);
lean_ctor_set(x_29, 1, x_37);
lean_ctor_set(x_29, 0, x_41);
lean_ctor_set(x_27, 1, x_38);
lean_inc_ref(x_27);
x_45 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(x_45, 0, x_27);
lean_inc_ref(x_27);
x_46 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_46, 0, x_27);
lean_inc_ref(x_27);
x_47 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(x_47, 0, x_27);
lean_inc_ref(x_27);
x_48 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(x_48, 0, x_27);
lean_inc_ref(x_27);
x_49 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(x_49, 0, x_27);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_46);
lean_inc_ref(x_27);
x_51 = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(x_51, 0, lean_box(0));
lean_closure_set(x_51, 1, x_27);
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_47);
lean_ctor_set(x_52, 3, x_48);
lean_ctor_set(x_52, 4, x_49);
lean_inc_ref(x_27);
x_53 = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(x_53, 0, lean_box(0));
lean_closure_set(x_53, 1, x_27);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_Meta_instMonadMCtxMetaM;
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
x_59 = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(x_59, 0, lean_box(0));
lean_closure_set(x_59, 1, x_27);
x_60 = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_60, 0, x_58);
lean_closure_set(x_60, 1, x_59);
x_61 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6;
x_62 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 4);
lean_closure_set(x_62, 0, lean_box(0));
lean_closure_set(x_62, 1, lean_box(0));
lean_closure_set(x_62, 2, x_57);
lean_closure_set(x_62, 3, x_61);
lean_ctor_set(x_55, 1, x_60);
lean_ctor_set(x_55, 0, x_62);
x_63 = l_Lean_instantiateMVars___redArg(x_54, x_55, x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_64 = lean_apply_5(x_63, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 0);
lean_dec(x_67);
x_68 = lean_box(0);
lean_ctor_set(x_64, 0, x_68);
return x_64;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
lean_dec(x_64);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_64);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_ctor_get(x_64, 1);
x_74 = lean_ctor_get(x_64, 0);
lean_dec(x_74);
x_75 = lean_ctor_get(x_65, 0);
lean_inc(x_75);
lean_dec(x_65);
x_76 = l_Lean_Expr_getAppFn(x_75);
x_77 = l_Lean_Expr_isMVar(x_76);
lean_dec_ref(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
lean_free_object(x_64);
x_78 = lean_apply_6(x_3, x_75, x_4, x_5, x_6, x_7, x_73);
return x_78;
}
else
{
lean_object* x_79; 
lean_dec(x_75);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_79 = lean_box(0);
lean_ctor_set(x_64, 0, x_79);
return x_64;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_ctor_get(x_64, 1);
lean_inc(x_80);
lean_dec(x_64);
x_81 = lean_ctor_get(x_65, 0);
lean_inc(x_81);
lean_dec(x_65);
x_82 = l_Lean_Expr_getAppFn(x_81);
x_83 = l_Lean_Expr_isMVar(x_82);
lean_dec_ref(x_82);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_apply_6(x_3, x_81, x_4, x_5, x_6, x_7, x_80);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_81);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_80);
return x_86;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_87 = !lean_is_exclusive(x_64);
if (x_87 == 0)
{
return x_64;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_64, 0);
x_89 = lean_ctor_get(x_64, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_64);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_91 = lean_ctor_get(x_55, 0);
x_92 = lean_ctor_get(x_55, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_55);
x_93 = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(x_93, 0, lean_box(0));
lean_closure_set(x_93, 1, x_27);
x_94 = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_94, 0, x_92);
lean_closure_set(x_94, 1, x_93);
x_95 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6;
x_96 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 4);
lean_closure_set(x_96, 0, lean_box(0));
lean_closure_set(x_96, 1, lean_box(0));
lean_closure_set(x_96, 2, x_91);
lean_closure_set(x_96, 3, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
x_98 = l_Lean_instantiateMVars___redArg(x_54, x_97, x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_99 = lean_apply_5(x_98, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_102 = x_99;
} else {
 lean_dec_ref(x_99);
 x_102 = lean_box(0);
}
x_103 = lean_box(0);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_105 = lean_ctor_get(x_99, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_106 = x_99;
} else {
 lean_dec_ref(x_99);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_100, 0);
lean_inc(x_107);
lean_dec(x_100);
x_108 = l_Lean_Expr_getAppFn(x_107);
x_109 = l_Lean_Expr_isMVar(x_108);
lean_dec_ref(x_108);
if (x_109 == 0)
{
lean_object* x_110; 
lean_dec(x_106);
x_110 = lean_apply_6(x_3, x_107, x_4, x_5, x_6, x_7, x_105);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_107);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_111 = lean_box(0);
if (lean_is_scalar(x_106)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_106;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_105);
return x_112;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_113 = lean_ctor_get(x_99, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_99, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_115 = x_99;
} else {
 lean_dec_ref(x_99);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_117 = lean_ctor_get(x_29, 0);
x_118 = lean_ctor_get(x_29, 2);
x_119 = lean_ctor_get(x_29, 3);
x_120 = lean_ctor_get(x_29, 4);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_29);
x_121 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4;
x_122 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5;
lean_inc_ref(x_117);
x_123 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_123, 0, x_117);
x_124 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_124, 0, x_117);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_126, 0, x_120);
x_127 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_127, 0, x_119);
x_128 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_128, 0, x_118);
x_129 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_129, 0, x_125);
lean_ctor_set(x_129, 1, x_121);
lean_ctor_set(x_129, 2, x_128);
lean_ctor_set(x_129, 3, x_127);
lean_ctor_set(x_129, 4, x_126);
lean_ctor_set(x_27, 1, x_122);
lean_ctor_set(x_27, 0, x_129);
lean_inc_ref(x_27);
x_130 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(x_130, 0, x_27);
lean_inc_ref(x_27);
x_131 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_131, 0, x_27);
lean_inc_ref(x_27);
x_132 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(x_132, 0, x_27);
lean_inc_ref(x_27);
x_133 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(x_133, 0, x_27);
lean_inc_ref(x_27);
x_134 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(x_134, 0, x_27);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_130);
lean_ctor_set(x_135, 1, x_131);
lean_inc_ref(x_27);
x_136 = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(x_136, 0, lean_box(0));
lean_closure_set(x_136, 1, x_27);
x_137 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
lean_ctor_set(x_137, 2, x_132);
lean_ctor_set(x_137, 3, x_133);
lean_ctor_set(x_137, 4, x_134);
lean_inc_ref(x_27);
x_138 = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(x_138, 0, lean_box(0));
lean_closure_set(x_138, 1, x_27);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = l_Lean_Meta_instMonadMCtxMetaM;
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_143 = x_140;
} else {
 lean_dec_ref(x_140);
 x_143 = lean_box(0);
}
x_144 = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(x_144, 0, lean_box(0));
lean_closure_set(x_144, 1, x_27);
x_145 = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_145, 0, x_142);
lean_closure_set(x_145, 1, x_144);
x_146 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6;
x_147 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 4);
lean_closure_set(x_147, 0, lean_box(0));
lean_closure_set(x_147, 1, lean_box(0));
lean_closure_set(x_147, 2, x_141);
lean_closure_set(x_147, 3, x_146);
if (lean_is_scalar(x_143)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_143;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_145);
x_149 = l_Lean_instantiateMVars___redArg(x_139, x_148, x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_150 = lean_apply_5(x_149, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_153 = x_150;
} else {
 lean_dec_ref(x_150);
 x_153 = lean_box(0);
}
x_154 = lean_box(0);
if (lean_is_scalar(x_153)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_153;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_152);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_156 = lean_ctor_get(x_150, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_157 = x_150;
} else {
 lean_dec_ref(x_150);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_151, 0);
lean_inc(x_158);
lean_dec(x_151);
x_159 = l_Lean_Expr_getAppFn(x_158);
x_160 = l_Lean_Expr_isMVar(x_159);
lean_dec_ref(x_159);
if (x_160 == 0)
{
lean_object* x_161; 
lean_dec(x_157);
x_161 = lean_apply_6(x_3, x_158, x_4, x_5, x_6, x_7, x_156);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_158);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_162 = lean_box(0);
if (lean_is_scalar(x_157)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_157;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_156);
return x_163;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_164 = lean_ctor_get(x_150, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_150, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_166 = x_150;
} else {
 lean_dec_ref(x_150);
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
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_168 = lean_ctor_get(x_27, 0);
lean_inc(x_168);
lean_dec(x_27);
x_169 = lean_ctor_get(x_168, 0);
lean_inc_ref(x_169);
x_170 = lean_ctor_get(x_168, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_168, 3);
lean_inc(x_171);
x_172 = lean_ctor_get(x_168, 4);
lean_inc(x_172);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 lean_ctor_release(x_168, 2);
 lean_ctor_release(x_168, 3);
 lean_ctor_release(x_168, 4);
 x_173 = x_168;
} else {
 lean_dec_ref(x_168);
 x_173 = lean_box(0);
}
x_174 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4;
x_175 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5;
lean_inc_ref(x_169);
x_176 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_176, 0, x_169);
x_177 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_177, 0, x_169);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_179, 0, x_172);
x_180 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_180, 0, x_171);
x_181 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_181, 0, x_170);
if (lean_is_scalar(x_173)) {
 x_182 = lean_alloc_ctor(0, 5, 0);
} else {
 x_182 = x_173;
}
lean_ctor_set(x_182, 0, x_178);
lean_ctor_set(x_182, 1, x_174);
lean_ctor_set(x_182, 2, x_181);
lean_ctor_set(x_182, 3, x_180);
lean_ctor_set(x_182, 4, x_179);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_175);
lean_inc_ref(x_183);
x_184 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(x_184, 0, x_183);
lean_inc_ref(x_183);
x_185 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_185, 0, x_183);
lean_inc_ref(x_183);
x_186 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(x_186, 0, x_183);
lean_inc_ref(x_183);
x_187 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(x_187, 0, x_183);
lean_inc_ref(x_183);
x_188 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(x_188, 0, x_183);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_184);
lean_ctor_set(x_189, 1, x_185);
lean_inc_ref(x_183);
x_190 = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(x_190, 0, lean_box(0));
lean_closure_set(x_190, 1, x_183);
x_191 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
lean_ctor_set(x_191, 2, x_186);
lean_ctor_set(x_191, 3, x_187);
lean_ctor_set(x_191, 4, x_188);
lean_inc_ref(x_183);
x_192 = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(x_192, 0, lean_box(0));
lean_closure_set(x_192, 1, x_183);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
x_194 = l_Lean_Meta_instMonadMCtxMetaM;
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_197 = x_194;
} else {
 lean_dec_ref(x_194);
 x_197 = lean_box(0);
}
x_198 = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(x_198, 0, lean_box(0));
lean_closure_set(x_198, 1, x_183);
x_199 = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_199, 0, x_196);
lean_closure_set(x_199, 1, x_198);
x_200 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6;
x_201 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 4);
lean_closure_set(x_201, 0, lean_box(0));
lean_closure_set(x_201, 1, lean_box(0));
lean_closure_set(x_201, 2, x_195);
lean_closure_set(x_201, 3, x_200);
if (lean_is_scalar(x_197)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_197;
}
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_199);
x_203 = l_Lean_instantiateMVars___redArg(x_193, x_202, x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_204 = lean_apply_5(x_203, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_207 = x_204;
} else {
 lean_dec_ref(x_204);
 x_207 = lean_box(0);
}
x_208 = lean_box(0);
if (lean_is_scalar(x_207)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_207;
}
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_206);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_210 = lean_ctor_get(x_204, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_211 = x_204;
} else {
 lean_dec_ref(x_204);
 x_211 = lean_box(0);
}
x_212 = lean_ctor_get(x_205, 0);
lean_inc(x_212);
lean_dec(x_205);
x_213 = l_Lean_Expr_getAppFn(x_212);
x_214 = l_Lean_Expr_isMVar(x_213);
lean_dec_ref(x_213);
if (x_214 == 0)
{
lean_object* x_215; 
lean_dec(x_211);
x_215 = lean_apply_6(x_3, x_212, x_4, x_5, x_6, x_7, x_210);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_212);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_216 = lean_box(0);
if (lean_is_scalar(x_211)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_211;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_210);
return x_217;
}
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_218 = lean_ctor_get(x_204, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_204, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_220 = x_204;
} else {
 lean_dec_ref(x_204);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(1, 2, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_219);
return x_221;
}
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_222 = lean_ctor_get(x_11, 0);
x_223 = lean_ctor_get(x_11, 2);
x_224 = lean_ctor_get(x_11, 3);
x_225 = lean_ctor_get(x_11, 4);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_11);
x_226 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2;
x_227 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3;
lean_inc_ref(x_222);
x_228 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_228, 0, x_222);
x_229 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_229, 0, x_222);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_231, 0, x_225);
x_232 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_232, 0, x_224);
x_233 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_233, 0, x_223);
x_234 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_234, 0, x_230);
lean_ctor_set(x_234, 1, x_226);
lean_ctor_set(x_234, 2, x_233);
lean_ctor_set(x_234, 3, x_232);
lean_ctor_set(x_234, 4, x_231);
lean_ctor_set(x_9, 1, x_227);
lean_ctor_set(x_9, 0, x_234);
x_235 = l_ReaderT_instMonad___redArg(x_9);
x_236 = lean_ctor_get(x_235, 0);
lean_inc_ref(x_236);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_237 = x_235;
} else {
 lean_dec_ref(x_235);
 x_237 = lean_box(0);
}
x_238 = lean_ctor_get(x_236, 0);
lean_inc_ref(x_238);
x_239 = lean_ctor_get(x_236, 2);
lean_inc(x_239);
x_240 = lean_ctor_get(x_236, 3);
lean_inc(x_240);
x_241 = lean_ctor_get(x_236, 4);
lean_inc(x_241);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 lean_ctor_release(x_236, 2);
 lean_ctor_release(x_236, 3);
 lean_ctor_release(x_236, 4);
 x_242 = x_236;
} else {
 lean_dec_ref(x_236);
 x_242 = lean_box(0);
}
x_243 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4;
x_244 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5;
lean_inc_ref(x_238);
x_245 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_245, 0, x_238);
x_246 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_246, 0, x_238);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
x_248 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_248, 0, x_241);
x_249 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_249, 0, x_240);
x_250 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_250, 0, x_239);
if (lean_is_scalar(x_242)) {
 x_251 = lean_alloc_ctor(0, 5, 0);
} else {
 x_251 = x_242;
}
lean_ctor_set(x_251, 0, x_247);
lean_ctor_set(x_251, 1, x_243);
lean_ctor_set(x_251, 2, x_250);
lean_ctor_set(x_251, 3, x_249);
lean_ctor_set(x_251, 4, x_248);
if (lean_is_scalar(x_237)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_237;
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_244);
lean_inc_ref(x_252);
x_253 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(x_253, 0, x_252);
lean_inc_ref(x_252);
x_254 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_254, 0, x_252);
lean_inc_ref(x_252);
x_255 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(x_255, 0, x_252);
lean_inc_ref(x_252);
x_256 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(x_256, 0, x_252);
lean_inc_ref(x_252);
x_257 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(x_257, 0, x_252);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_253);
lean_ctor_set(x_258, 1, x_254);
lean_inc_ref(x_252);
x_259 = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(x_259, 0, lean_box(0));
lean_closure_set(x_259, 1, x_252);
x_260 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
lean_ctor_set(x_260, 2, x_255);
lean_ctor_set(x_260, 3, x_256);
lean_ctor_set(x_260, 4, x_257);
lean_inc_ref(x_252);
x_261 = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(x_261, 0, lean_box(0));
lean_closure_set(x_261, 1, x_252);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
x_263 = l_Lean_Meta_instMonadMCtxMetaM;
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_266 = x_263;
} else {
 lean_dec_ref(x_263);
 x_266 = lean_box(0);
}
x_267 = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(x_267, 0, lean_box(0));
lean_closure_set(x_267, 1, x_252);
x_268 = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_268, 0, x_265);
lean_closure_set(x_268, 1, x_267);
x_269 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6;
x_270 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 4);
lean_closure_set(x_270, 0, lean_box(0));
lean_closure_set(x_270, 1, lean_box(0));
lean_closure_set(x_270, 2, x_264);
lean_closure_set(x_270, 3, x_269);
if (lean_is_scalar(x_266)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_266;
}
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_268);
x_272 = l_Lean_instantiateMVars___redArg(x_262, x_271, x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_273 = lean_apply_5(x_272, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_276 = x_273;
} else {
 lean_dec_ref(x_273);
 x_276 = lean_box(0);
}
x_277 = lean_box(0);
if (lean_is_scalar(x_276)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_276;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_275);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
x_279 = lean_ctor_get(x_273, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_280 = x_273;
} else {
 lean_dec_ref(x_273);
 x_280 = lean_box(0);
}
x_281 = lean_ctor_get(x_274, 0);
lean_inc(x_281);
lean_dec(x_274);
x_282 = l_Lean_Expr_getAppFn(x_281);
x_283 = l_Lean_Expr_isMVar(x_282);
lean_dec_ref(x_282);
if (x_283 == 0)
{
lean_object* x_284; 
lean_dec(x_280);
x_284 = lean_apply_6(x_3, x_281, x_4, x_5, x_6, x_7, x_279);
return x_284;
}
else
{
lean_object* x_285; lean_object* x_286; 
lean_dec(x_281);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_285 = lean_box(0);
if (lean_is_scalar(x_280)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_280;
}
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_279);
return x_286;
}
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_287 = lean_ctor_get(x_273, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_273, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_289 = x_273;
} else {
 lean_dec_ref(x_273);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(1, 2, 0);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_287);
lean_ctor_set(x_290, 1, x_288);
return x_290;
}
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_291 = lean_ctor_get(x_9, 0);
lean_inc(x_291);
lean_dec(x_9);
x_292 = lean_ctor_get(x_291, 0);
lean_inc_ref(x_292);
x_293 = lean_ctor_get(x_291, 2);
lean_inc(x_293);
x_294 = lean_ctor_get(x_291, 3);
lean_inc(x_294);
x_295 = lean_ctor_get(x_291, 4);
lean_inc(x_295);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 lean_ctor_release(x_291, 2);
 lean_ctor_release(x_291, 3);
 lean_ctor_release(x_291, 4);
 x_296 = x_291;
} else {
 lean_dec_ref(x_291);
 x_296 = lean_box(0);
}
x_297 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2;
x_298 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3;
lean_inc_ref(x_292);
x_299 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_299, 0, x_292);
x_300 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_300, 0, x_292);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
x_302 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_302, 0, x_295);
x_303 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_303, 0, x_294);
x_304 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_304, 0, x_293);
if (lean_is_scalar(x_296)) {
 x_305 = lean_alloc_ctor(0, 5, 0);
} else {
 x_305 = x_296;
}
lean_ctor_set(x_305, 0, x_301);
lean_ctor_set(x_305, 1, x_297);
lean_ctor_set(x_305, 2, x_304);
lean_ctor_set(x_305, 3, x_303);
lean_ctor_set(x_305, 4, x_302);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_298);
x_307 = l_ReaderT_instMonad___redArg(x_306);
x_308 = lean_ctor_get(x_307, 0);
lean_inc_ref(x_308);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_309 = x_307;
} else {
 lean_dec_ref(x_307);
 x_309 = lean_box(0);
}
x_310 = lean_ctor_get(x_308, 0);
lean_inc_ref(x_310);
x_311 = lean_ctor_get(x_308, 2);
lean_inc(x_311);
x_312 = lean_ctor_get(x_308, 3);
lean_inc(x_312);
x_313 = lean_ctor_get(x_308, 4);
lean_inc(x_313);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 lean_ctor_release(x_308, 2);
 lean_ctor_release(x_308, 3);
 lean_ctor_release(x_308, 4);
 x_314 = x_308;
} else {
 lean_dec_ref(x_308);
 x_314 = lean_box(0);
}
x_315 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4;
x_316 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5;
lean_inc_ref(x_310);
x_317 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_317, 0, x_310);
x_318 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_318, 0, x_310);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_318);
x_320 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_320, 0, x_313);
x_321 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_321, 0, x_312);
x_322 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_322, 0, x_311);
if (lean_is_scalar(x_314)) {
 x_323 = lean_alloc_ctor(0, 5, 0);
} else {
 x_323 = x_314;
}
lean_ctor_set(x_323, 0, x_319);
lean_ctor_set(x_323, 1, x_315);
lean_ctor_set(x_323, 2, x_322);
lean_ctor_set(x_323, 3, x_321);
lean_ctor_set(x_323, 4, x_320);
if (lean_is_scalar(x_309)) {
 x_324 = lean_alloc_ctor(0, 2, 0);
} else {
 x_324 = x_309;
}
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_316);
lean_inc_ref(x_324);
x_325 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(x_325, 0, x_324);
lean_inc_ref(x_324);
x_326 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_326, 0, x_324);
lean_inc_ref(x_324);
x_327 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(x_327, 0, x_324);
lean_inc_ref(x_324);
x_328 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(x_328, 0, x_324);
lean_inc_ref(x_324);
x_329 = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(x_329, 0, x_324);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_325);
lean_ctor_set(x_330, 1, x_326);
lean_inc_ref(x_324);
x_331 = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(x_331, 0, lean_box(0));
lean_closure_set(x_331, 1, x_324);
x_332 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
lean_ctor_set(x_332, 2, x_327);
lean_ctor_set(x_332, 3, x_328);
lean_ctor_set(x_332, 4, x_329);
lean_inc_ref(x_324);
x_333 = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(x_333, 0, lean_box(0));
lean_closure_set(x_333, 1, x_324);
x_334 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
x_335 = l_Lean_Meta_instMonadMCtxMetaM;
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_338 = x_335;
} else {
 lean_dec_ref(x_335);
 x_338 = lean_box(0);
}
x_339 = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(x_339, 0, lean_box(0));
lean_closure_set(x_339, 1, x_324);
x_340 = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_340, 0, x_337);
lean_closure_set(x_340, 1, x_339);
x_341 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6;
x_342 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 4);
lean_closure_set(x_342, 0, lean_box(0));
lean_closure_set(x_342, 1, lean_box(0));
lean_closure_set(x_342, 2, x_336);
lean_closure_set(x_342, 3, x_341);
if (lean_is_scalar(x_338)) {
 x_343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_343 = x_338;
}
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_340);
x_344 = l_Lean_instantiateMVars___redArg(x_334, x_343, x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_345 = lean_apply_5(x_344, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; 
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
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
x_349 = lean_box(0);
if (lean_is_scalar(x_348)) {
 x_350 = lean_alloc_ctor(0, 2, 0);
} else {
 x_350 = x_348;
}
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_347);
return x_350;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; 
x_351 = lean_ctor_get(x_345, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_352 = x_345;
} else {
 lean_dec_ref(x_345);
 x_352 = lean_box(0);
}
x_353 = lean_ctor_get(x_346, 0);
lean_inc(x_353);
lean_dec(x_346);
x_354 = l_Lean_Expr_getAppFn(x_353);
x_355 = l_Lean_Expr_isMVar(x_354);
lean_dec_ref(x_354);
if (x_355 == 0)
{
lean_object* x_356; 
lean_dec(x_352);
x_356 = lean_apply_6(x_3, x_353, x_4, x_5, x_6, x_7, x_351);
return x_356;
}
else
{
lean_object* x_357; lean_object* x_358; 
lean_dec(x_353);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_357 = lean_box(0);
if (lean_is_scalar(x_352)) {
 x_358 = lean_alloc_ctor(0, 2, 0);
} else {
 x_358 = x_352;
}
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_351);
return x_358;
}
}
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_359 = lean_ctor_get(x_345, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_345, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_361 = x_345;
} else {
 lean_dec_ref(x_345);
 x_361 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_362 = lean_alloc_ctor(1, 2, 0);
} else {
 x_362 = x_361;
}
lean_ctor_set(x_362, 0, x_359);
lean_ctor_set(x_362, 1, x_360);
return x_362;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat_evalPow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc_ref(x_5);
x_8 = l_Lean_Meta_evalNat(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc_ref(x_5);
lean_inc(x_11);
x_12 = l_Lean_checkExponent(x_11, x_5, x_6, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec_ref(x_12);
x_22 = l_Lean_Meta_evalNat(x_1, x_3, x_4, x_5, x_6, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_11);
return x_22;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_nat_pow(x_27, x_11);
lean_dec(x_11);
lean_dec(x_27);
lean_ctor_set(x_23, 0, x_28);
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_nat_pow(x_29, x_11);
lean_dec(x_11);
lean_dec(x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_22, 0, x_31);
return x_22;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_dec(x_22);
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_34 = x_23;
} else {
 lean_dec_ref(x_23);
 x_34 = lean_box(0);
}
x_35 = lean_nat_pow(x_33, x_11);
lean_dec(x_11);
lean_dec(x_33);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(1, 1, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_32);
return x_37;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_evalNat___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("zero", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_evalNat_visit(x_1, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
case 4:
{
lean_object* x_12; 
lean_dec_ref(x_4);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec_ref(x_1);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_16);
lean_dec(x_13);
x_17 = l_Lean_Meta_evalNat___closed__0;
x_18 = lean_string_dec_eq(x_16, x_17);
lean_dec_ref(x_16);
if (x_18 == 0)
{
lean_dec_ref(x_15);
x_7 = x_6;
goto block_10;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Meta_evalNat___closed__1;
x_20 = lean_string_dec_eq(x_15, x_19);
lean_dec_ref(x_15);
if (x_20 == 0)
{
x_7 = x_6;
goto block_10;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_Meta_evalNat___closed__2;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
return x_22;
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_7 = x_6;
goto block_10;
}
}
else
{
lean_dec(x_13);
lean_dec(x_12);
x_7 = x_6;
goto block_10;
}
}
else
{
lean_dec(x_12);
x_7 = x_6;
goto block_10;
}
}
case 5:
{
lean_object* x_23; 
x_23 = l_Lean_Meta_evalNat_visit(x_1, x_2, x_3, x_4, x_5, x_6);
return x_23;
}
case 9:
{
lean_object* x_24; 
lean_dec_ref(x_4);
x_24 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_24);
lean_dec_ref(x_1);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_ctor_set_tag(x_24, 1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_6);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_6);
return x_29;
}
}
else
{
lean_dec_ref(x_24);
x_7 = x_6;
goto block_10;
}
}
case 10:
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_30);
lean_dec_ref(x_1);
x_1 = x_30;
goto _start;
}
default: 
{
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_7 = x_6;
goto block_10;
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("succ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__0;
x_2 = l_Lean_Meta_evalNat___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pow", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__2;
x_2 = l_Lean_Meta_evalNat___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mod", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__4;
x_2 = l_Lean_Meta_evalNat___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("div", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__6;
x_2 = l_Lean_Meta_evalNat___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mul", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__8;
x_2 = l_Lean_Meta_evalNat___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sub", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__10;
x_2 = l_Lean_Meta_evalNat___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("add", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__12;
x_2 = l_Lean_Meta_evalNat___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("OfNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__15;
x_2 = l_Lean_Meta_evalNat_visit___closed__14;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("NatPow", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__2;
x_2 = l_Lean_Meta_evalNat_visit___closed__17;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Mod", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__4;
x_2 = l_Lean_Meta_evalNat_visit___closed__19;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Div", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__6;
x_2 = l_Lean_Meta_evalNat_visit___closed__21;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Mul", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__8;
x_2 = l_Lean_Meta_evalNat_visit___closed__23;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Sub", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__10;
x_2 = l_Lean_Meta_evalNat_visit___closed__25;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Add", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__12;
x_2 = l_Lean_Meta_evalNat_visit___closed__27;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Pow", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__2;
x_2 = l_Lean_Meta_evalNat_visit___closed__29;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HPow", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hPow", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__32;
x_2 = l_Lean_Meta_evalNat_visit___closed__31;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMod", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMod", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__35;
x_2 = l_Lean_Meta_evalNat_visit___closed__34;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HDiv", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hDiv", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__38;
x_2 = l_Lean_Meta_evalNat_visit___closed__37;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__41() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__41;
x_2 = l_Lean_Meta_evalNat_visit___closed__40;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__43() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HSub", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__44() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hSub", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__44;
x_2 = l_Lean_Meta_evalNat_visit___closed__43;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__46() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__47() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_evalNat_visit___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_evalNat_visit___closed__47;
x_2 = l_Lean_Meta_evalNat_visit___closed__46;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; uint8_t x_15; 
x_7 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_14 = l_Lean_Expr_cleanupAnnotations(x_8);
x_15 = l_Lean_Expr_isApp(x_14);
if (x_15 == 0)
{
lean_dec_ref(x_14);
lean_dec_ref(x_4);
goto block_13;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_16);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_18 = l_Lean_Meta_evalNat_visit___closed__1;
x_19 = l_Lean_Expr_isConstOf(x_17, x_18);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Expr_isApp(x_17);
if (x_20 == 0)
{
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_4);
goto block_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_21);
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_23 = l_Lean_Meta_evalNat_visit___closed__3;
x_24 = l_Lean_Expr_isConstOf(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Meta_evalNat_visit___closed__5;
x_26 = l_Lean_Expr_isConstOf(x_22, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_Meta_evalNat_visit___closed__7;
x_28 = l_Lean_Expr_isConstOf(x_22, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_Meta_evalNat_visit___closed__9;
x_30 = l_Lean_Expr_isConstOf(x_22, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Meta_evalNat_visit___closed__11;
x_32 = l_Lean_Expr_isConstOf(x_22, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Meta_evalNat_visit___closed__13;
x_34 = l_Lean_Expr_isConstOf(x_22, x_33);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_Expr_isApp(x_22);
if (x_35 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec_ref(x_4);
goto block_13;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_36);
x_37 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_38 = l_Lean_Meta_evalNat_visit___closed__16;
x_39 = l_Lean_Expr_isConstOf(x_37, x_38);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = l_Lean_Expr_isApp(x_37);
if (x_40 == 0)
{
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec_ref(x_4);
goto block_13;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = l_Lean_Expr_appFnCleanup___redArg(x_37);
x_42 = l_Lean_Meta_evalNat_visit___closed__18;
x_43 = l_Lean_Expr_isConstOf(x_41, x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = l_Lean_Meta_evalNat_visit___closed__20;
x_45 = l_Lean_Expr_isConstOf(x_41, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = l_Lean_Meta_evalNat_visit___closed__22;
x_47 = l_Lean_Expr_isConstOf(x_41, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = l_Lean_Meta_evalNat_visit___closed__24;
x_49 = l_Lean_Expr_isConstOf(x_41, x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = l_Lean_Meta_evalNat_visit___closed__26;
x_51 = l_Lean_Expr_isConstOf(x_41, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = l_Lean_Meta_evalNat_visit___closed__28;
x_53 = l_Lean_Expr_isConstOf(x_41, x_52);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = l_Lean_Expr_isApp(x_41);
if (x_54 == 0)
{
lean_dec_ref(x_41);
lean_dec_ref(x_36);
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec_ref(x_4);
goto block_13;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = l_Lean_Expr_appFnCleanup___redArg(x_41);
x_56 = l_Lean_Meta_evalNat_visit___closed__30;
x_57 = l_Lean_Expr_isConstOf(x_55, x_56);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = l_Lean_Expr_isApp(x_55);
if (x_58 == 0)
{
lean_dec_ref(x_55);
lean_dec_ref(x_36);
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec_ref(x_4);
goto block_13;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = l_Lean_Expr_appFnCleanup___redArg(x_55);
x_60 = l_Lean_Meta_evalNat_visit___closed__33;
x_61 = l_Lean_Expr_isConstOf(x_59, x_60);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = l_Lean_Meta_evalNat_visit___closed__36;
x_63 = l_Lean_Expr_isConstOf(x_59, x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = l_Lean_Meta_evalNat_visit___closed__39;
x_65 = l_Lean_Expr_isConstOf(x_59, x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = l_Lean_Meta_evalNat_visit___closed__42;
x_67 = l_Lean_Expr_isConstOf(x_59, x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = l_Lean_Meta_evalNat_visit___closed__45;
x_69 = l_Lean_Expr_isConstOf(x_59, x_68);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = l_Lean_Meta_evalNat_visit___closed__48;
x_71 = l_Lean_Expr_isConstOf(x_59, x_70);
lean_dec_ref(x_59);
if (x_71 == 0)
{
lean_dec_ref(x_36);
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec_ref(x_4);
goto block_13;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_10);
x_72 = l_Lean_Meta_isInstHAddNat___redArg(x_36, x_3, x_9);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
uint8_t x_75; 
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec_ref(x_4);
x_75 = !lean_is_exclusive(x_72);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_72, 0);
lean_dec(x_76);
x_77 = lean_box(0);
lean_ctor_set(x_72, 0, x_77);
return x_72;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
lean_dec(x_72);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_72, 1);
lean_inc(x_81);
lean_dec_ref(x_72);
lean_inc_ref(x_4);
x_82 = l_Lean_Meta_evalNat(x_21, x_2, x_3, x_4, x_5, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
lean_dec_ref(x_16);
lean_dec_ref(x_4);
return x_82;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec_ref(x_82);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_84);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_obj_tag(x_87) == 0)
{
lean_dec(x_85);
return x_86;
}
else
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_86);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_86, 0);
lean_dec(x_89);
x_90 = !lean_is_exclusive(x_87);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_87, 0);
x_92 = lean_nat_add(x_85, x_91);
lean_dec(x_91);
lean_dec(x_85);
lean_ctor_set(x_87, 0, x_92);
return x_86;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_87, 0);
lean_inc(x_93);
lean_dec(x_87);
x_94 = lean_nat_add(x_85, x_93);
lean_dec(x_93);
lean_dec(x_85);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_86, 0, x_95);
return x_86;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_96 = lean_ctor_get(x_86, 1);
lean_inc(x_96);
lean_dec(x_86);
x_97 = lean_ctor_get(x_87, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_98 = x_87;
} else {
 lean_dec_ref(x_87);
 x_98 = lean_box(0);
}
x_99 = lean_nat_add(x_85, x_97);
lean_dec(x_97);
lean_dec(x_85);
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(1, 1, 0);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_96);
return x_101;
}
}
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
lean_dec_ref(x_59);
lean_dec(x_10);
x_102 = l_Lean_Meta_isInstHSubNat___redArg(x_36, x_3, x_9);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_unbox(x_103);
lean_dec(x_103);
if (x_104 == 0)
{
uint8_t x_105; 
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec_ref(x_4);
x_105 = !lean_is_exclusive(x_102);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_102, 0);
lean_dec(x_106);
x_107 = lean_box(0);
lean_ctor_set(x_102, 0, x_107);
return x_102;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_102, 1);
lean_inc(x_108);
lean_dec(x_102);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_102, 1);
lean_inc(x_111);
lean_dec_ref(x_102);
lean_inc_ref(x_4);
x_112 = l_Lean_Meta_evalNat(x_21, x_2, x_3, x_4, x_5, x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 0)
{
lean_dec_ref(x_16);
lean_dec_ref(x_4);
return x_112;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec_ref(x_112);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_114);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
lean_dec(x_115);
return x_116;
}
else
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_116);
if (x_118 == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_116, 0);
lean_dec(x_119);
x_120 = !lean_is_exclusive(x_117);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_117, 0);
x_122 = lean_nat_sub(x_115, x_121);
lean_dec(x_121);
lean_dec(x_115);
lean_ctor_set(x_117, 0, x_122);
return x_116;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_117, 0);
lean_inc(x_123);
lean_dec(x_117);
x_124 = lean_nat_sub(x_115, x_123);
lean_dec(x_123);
lean_dec(x_115);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_116, 0, x_125);
return x_116;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_126 = lean_ctor_get(x_116, 1);
lean_inc(x_126);
lean_dec(x_116);
x_127 = lean_ctor_get(x_117, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_128 = x_117;
} else {
 lean_dec_ref(x_117);
 x_128 = lean_box(0);
}
x_129 = lean_nat_sub(x_115, x_127);
lean_dec(x_127);
lean_dec(x_115);
if (lean_is_scalar(x_128)) {
 x_130 = lean_alloc_ctor(1, 1, 0);
} else {
 x_130 = x_128;
}
lean_ctor_set(x_130, 0, x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_126);
return x_131;
}
}
}
}
}
}
else
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
lean_dec_ref(x_59);
lean_dec(x_10);
x_132 = l_Lean_Meta_isInstHMulNat___redArg(x_36, x_3, x_9);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_unbox(x_133);
lean_dec(x_133);
if (x_134 == 0)
{
uint8_t x_135; 
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec_ref(x_4);
x_135 = !lean_is_exclusive(x_132);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_132, 0);
lean_dec(x_136);
x_137 = lean_box(0);
lean_ctor_set(x_132, 0, x_137);
return x_132;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_132, 1);
lean_inc(x_138);
lean_dec(x_132);
x_139 = lean_box(0);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_132, 1);
lean_inc(x_141);
lean_dec_ref(x_132);
lean_inc_ref(x_4);
x_142 = l_Lean_Meta_evalNat(x_21, x_2, x_3, x_4, x_5, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
if (lean_obj_tag(x_143) == 0)
{
lean_dec_ref(x_16);
lean_dec_ref(x_4);
return x_142;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec_ref(x_142);
x_145 = lean_ctor_get(x_143, 0);
lean_inc(x_145);
lean_dec(x_143);
x_146 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_144);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
lean_dec(x_145);
return x_146;
}
else
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_146);
if (x_148 == 0)
{
lean_object* x_149; uint8_t x_150; 
x_149 = lean_ctor_get(x_146, 0);
lean_dec(x_149);
x_150 = !lean_is_exclusive(x_147);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_147, 0);
x_152 = lean_nat_mul(x_145, x_151);
lean_dec(x_151);
lean_dec(x_145);
lean_ctor_set(x_147, 0, x_152);
return x_146;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_147, 0);
lean_inc(x_153);
lean_dec(x_147);
x_154 = lean_nat_mul(x_145, x_153);
lean_dec(x_153);
lean_dec(x_145);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_146, 0, x_155);
return x_146;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_156 = lean_ctor_get(x_146, 1);
lean_inc(x_156);
lean_dec(x_146);
x_157 = lean_ctor_get(x_147, 0);
lean_inc(x_157);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 x_158 = x_147;
} else {
 lean_dec_ref(x_147);
 x_158 = lean_box(0);
}
x_159 = lean_nat_mul(x_145, x_157);
lean_dec(x_157);
lean_dec(x_145);
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(1, 1, 0);
} else {
 x_160 = x_158;
}
lean_ctor_set(x_160, 0, x_159);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_156);
return x_161;
}
}
}
}
}
}
else
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; 
lean_dec_ref(x_59);
lean_dec(x_10);
x_162 = l_Lean_Meta_isInstHDivNat___redArg(x_36, x_3, x_9);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_unbox(x_163);
lean_dec(x_163);
if (x_164 == 0)
{
uint8_t x_165; 
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec_ref(x_4);
x_165 = !lean_is_exclusive(x_162);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_162, 0);
lean_dec(x_166);
x_167 = lean_box(0);
lean_ctor_set(x_162, 0, x_167);
return x_162;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_162, 1);
lean_inc(x_168);
lean_dec(x_162);
x_169 = lean_box(0);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_162, 1);
lean_inc(x_171);
lean_dec_ref(x_162);
lean_inc_ref(x_4);
x_172 = l_Lean_Meta_evalNat(x_21, x_2, x_3, x_4, x_5, x_171);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
if (lean_obj_tag(x_173) == 0)
{
lean_dec_ref(x_16);
lean_dec_ref(x_4);
return x_172;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec_ref(x_172);
x_175 = lean_ctor_get(x_173, 0);
lean_inc(x_175);
lean_dec(x_173);
x_176 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_174);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
if (lean_obj_tag(x_177) == 0)
{
lean_dec(x_175);
return x_176;
}
else
{
uint8_t x_178; 
x_178 = !lean_is_exclusive(x_176);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; 
x_179 = lean_ctor_get(x_176, 0);
lean_dec(x_179);
x_180 = !lean_is_exclusive(x_177);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_177, 0);
x_182 = lean_nat_div(x_175, x_181);
lean_dec(x_181);
lean_dec(x_175);
lean_ctor_set(x_177, 0, x_182);
return x_176;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_177, 0);
lean_inc(x_183);
lean_dec(x_177);
x_184 = lean_nat_div(x_175, x_183);
lean_dec(x_183);
lean_dec(x_175);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_176, 0, x_185);
return x_176;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_186 = lean_ctor_get(x_176, 1);
lean_inc(x_186);
lean_dec(x_176);
x_187 = lean_ctor_get(x_177, 0);
lean_inc(x_187);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 x_188 = x_177;
} else {
 lean_dec_ref(x_177);
 x_188 = lean_box(0);
}
x_189 = lean_nat_div(x_175, x_187);
lean_dec(x_187);
lean_dec(x_175);
if (lean_is_scalar(x_188)) {
 x_190 = lean_alloc_ctor(1, 1, 0);
} else {
 x_190 = x_188;
}
lean_ctor_set(x_190, 0, x_189);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_186);
return x_191;
}
}
}
}
}
}
else
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; 
lean_dec_ref(x_59);
lean_dec(x_10);
x_192 = l_Lean_Meta_isInstHModNat___redArg(x_36, x_3, x_9);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_unbox(x_193);
lean_dec(x_193);
if (x_194 == 0)
{
uint8_t x_195; 
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec_ref(x_4);
x_195 = !lean_is_exclusive(x_192);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_192, 0);
lean_dec(x_196);
x_197 = lean_box(0);
lean_ctor_set(x_192, 0, x_197);
return x_192;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_192, 1);
lean_inc(x_198);
lean_dec(x_192);
x_199 = lean_box(0);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_192, 1);
lean_inc(x_201);
lean_dec_ref(x_192);
lean_inc_ref(x_4);
x_202 = l_Lean_Meta_evalNat(x_21, x_2, x_3, x_4, x_5, x_201);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
if (lean_obj_tag(x_203) == 0)
{
lean_dec_ref(x_16);
lean_dec_ref(x_4);
return x_202;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec_ref(x_202);
x_205 = lean_ctor_get(x_203, 0);
lean_inc(x_205);
lean_dec(x_203);
x_206 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_204);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_dec(x_205);
return x_206;
}
else
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_206);
if (x_208 == 0)
{
lean_object* x_209; uint8_t x_210; 
x_209 = lean_ctor_get(x_206, 0);
lean_dec(x_209);
x_210 = !lean_is_exclusive(x_207);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_207, 0);
x_212 = lean_nat_mod(x_205, x_211);
lean_dec(x_211);
lean_dec(x_205);
lean_ctor_set(x_207, 0, x_212);
return x_206;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_207, 0);
lean_inc(x_213);
lean_dec(x_207);
x_214 = lean_nat_mod(x_205, x_213);
lean_dec(x_213);
lean_dec(x_205);
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_206, 0, x_215);
return x_206;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_216 = lean_ctor_get(x_206, 1);
lean_inc(x_216);
lean_dec(x_206);
x_217 = lean_ctor_get(x_207, 0);
lean_inc(x_217);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 x_218 = x_207;
} else {
 lean_dec_ref(x_207);
 x_218 = lean_box(0);
}
x_219 = lean_nat_mod(x_205, x_217);
lean_dec(x_217);
lean_dec(x_205);
if (lean_is_scalar(x_218)) {
 x_220 = lean_alloc_ctor(1, 1, 0);
} else {
 x_220 = x_218;
}
lean_ctor_set(x_220, 0, x_219);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_216);
return x_221;
}
}
}
}
}
}
else
{
lean_object* x_222; lean_object* x_223; uint8_t x_224; 
lean_dec_ref(x_59);
lean_dec(x_10);
x_222 = l_Lean_Meta_isInstHPowNat___redArg(x_36, x_3, x_9);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_unbox(x_223);
lean_dec(x_223);
if (x_224 == 0)
{
uint8_t x_225; 
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec_ref(x_4);
x_225 = !lean_is_exclusive(x_222);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_222, 0);
lean_dec(x_226);
x_227 = lean_box(0);
lean_ctor_set(x_222, 0, x_227);
return x_222;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_222, 1);
lean_inc(x_228);
lean_dec(x_222);
x_229 = lean_box(0);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
}
else
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_222, 1);
lean_inc(x_231);
lean_dec_ref(x_222);
x_232 = l_Lean_Meta_evalNat_evalPow(x_21, x_16, x_2, x_3, x_4, x_5, x_231);
return x_232;
}
}
}
}
else
{
lean_object* x_233; lean_object* x_234; uint8_t x_235; 
lean_dec_ref(x_55);
lean_dec(x_10);
x_233 = l_Lean_Meta_isInstPowNat___redArg(x_36, x_3, x_9);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_unbox(x_234);
lean_dec(x_234);
if (x_235 == 0)
{
uint8_t x_236; 
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec_ref(x_4);
x_236 = !lean_is_exclusive(x_233);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_ctor_get(x_233, 0);
lean_dec(x_237);
x_238 = lean_box(0);
lean_ctor_set(x_233, 0, x_238);
return x_233;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_233, 1);
lean_inc(x_239);
lean_dec(x_233);
x_240 = lean_box(0);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
else
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_ctor_get(x_233, 1);
lean_inc(x_242);
lean_dec_ref(x_233);
x_243 = l_Lean_Meta_evalNat_evalPow(x_21, x_16, x_2, x_3, x_4, x_5, x_242);
return x_243;
}
}
}
}
else
{
lean_object* x_244; lean_object* x_245; uint8_t x_246; 
lean_dec_ref(x_41);
lean_dec(x_10);
x_244 = l_Lean_Meta_isInstAddNat___redArg(x_36, x_3, x_9);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_unbox(x_245);
lean_dec(x_245);
if (x_246 == 0)
{
uint8_t x_247; 
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec_ref(x_4);
x_247 = !lean_is_exclusive(x_244);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_ctor_get(x_244, 0);
lean_dec(x_248);
x_249 = lean_box(0);
lean_ctor_set(x_244, 0, x_249);
return x_244;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_244, 1);
lean_inc(x_250);
lean_dec(x_244);
x_251 = lean_box(0);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_244, 1);
lean_inc(x_253);
lean_dec_ref(x_244);
lean_inc_ref(x_4);
x_254 = l_Lean_Meta_evalNat(x_21, x_2, x_3, x_4, x_5, x_253);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
if (lean_obj_tag(x_255) == 0)
{
lean_dec_ref(x_16);
lean_dec_ref(x_4);
return x_254;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
lean_dec_ref(x_254);
x_257 = lean_ctor_get(x_255, 0);
lean_inc(x_257);
lean_dec(x_255);
x_258 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_256);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
if (lean_obj_tag(x_259) == 0)
{
lean_dec(x_257);
return x_258;
}
else
{
uint8_t x_260; 
x_260 = !lean_is_exclusive(x_258);
if (x_260 == 0)
{
lean_object* x_261; uint8_t x_262; 
x_261 = lean_ctor_get(x_258, 0);
lean_dec(x_261);
x_262 = !lean_is_exclusive(x_259);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; 
x_263 = lean_ctor_get(x_259, 0);
x_264 = lean_nat_add(x_257, x_263);
lean_dec(x_263);
lean_dec(x_257);
lean_ctor_set(x_259, 0, x_264);
return x_258;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_259, 0);
lean_inc(x_265);
lean_dec(x_259);
x_266 = lean_nat_add(x_257, x_265);
lean_dec(x_265);
lean_dec(x_257);
x_267 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_258, 0, x_267);
return x_258;
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_268 = lean_ctor_get(x_258, 1);
lean_inc(x_268);
lean_dec(x_258);
x_269 = lean_ctor_get(x_259, 0);
lean_inc(x_269);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 x_270 = x_259;
} else {
 lean_dec_ref(x_259);
 x_270 = lean_box(0);
}
x_271 = lean_nat_add(x_257, x_269);
lean_dec(x_269);
lean_dec(x_257);
if (lean_is_scalar(x_270)) {
 x_272 = lean_alloc_ctor(1, 1, 0);
} else {
 x_272 = x_270;
}
lean_ctor_set(x_272, 0, x_271);
x_273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_268);
return x_273;
}
}
}
}
}
}
else
{
lean_object* x_274; lean_object* x_275; uint8_t x_276; 
lean_dec_ref(x_41);
lean_dec(x_10);
x_274 = l_Lean_Meta_isInstSubNat___redArg(x_36, x_3, x_9);
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_unbox(x_275);
lean_dec(x_275);
if (x_276 == 0)
{
uint8_t x_277; 
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec_ref(x_4);
x_277 = !lean_is_exclusive(x_274);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_274, 0);
lean_dec(x_278);
x_279 = lean_box(0);
lean_ctor_set(x_274, 0, x_279);
return x_274;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_274, 1);
lean_inc(x_280);
lean_dec(x_274);
x_281 = lean_box(0);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_274, 1);
lean_inc(x_283);
lean_dec_ref(x_274);
lean_inc_ref(x_4);
x_284 = l_Lean_Meta_evalNat(x_21, x_2, x_3, x_4, x_5, x_283);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
if (lean_obj_tag(x_285) == 0)
{
lean_dec_ref(x_16);
lean_dec_ref(x_4);
return x_284;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec_ref(x_284);
x_287 = lean_ctor_get(x_285, 0);
lean_inc(x_287);
lean_dec(x_285);
x_288 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_286);
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
if (lean_obj_tag(x_289) == 0)
{
lean_dec(x_287);
return x_288;
}
else
{
uint8_t x_290; 
x_290 = !lean_is_exclusive(x_288);
if (x_290 == 0)
{
lean_object* x_291; uint8_t x_292; 
x_291 = lean_ctor_get(x_288, 0);
lean_dec(x_291);
x_292 = !lean_is_exclusive(x_289);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_289, 0);
x_294 = lean_nat_sub(x_287, x_293);
lean_dec(x_293);
lean_dec(x_287);
lean_ctor_set(x_289, 0, x_294);
return x_288;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_289, 0);
lean_inc(x_295);
lean_dec(x_289);
x_296 = lean_nat_sub(x_287, x_295);
lean_dec(x_295);
lean_dec(x_287);
x_297 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_288, 0, x_297);
return x_288;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_298 = lean_ctor_get(x_288, 1);
lean_inc(x_298);
lean_dec(x_288);
x_299 = lean_ctor_get(x_289, 0);
lean_inc(x_299);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 x_300 = x_289;
} else {
 lean_dec_ref(x_289);
 x_300 = lean_box(0);
}
x_301 = lean_nat_sub(x_287, x_299);
lean_dec(x_299);
lean_dec(x_287);
if (lean_is_scalar(x_300)) {
 x_302 = lean_alloc_ctor(1, 1, 0);
} else {
 x_302 = x_300;
}
lean_ctor_set(x_302, 0, x_301);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_298);
return x_303;
}
}
}
}
}
}
else
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; 
lean_dec_ref(x_41);
lean_dec(x_10);
x_304 = l_Lean_Meta_isInstMulNat___redArg(x_36, x_3, x_9);
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_unbox(x_305);
lean_dec(x_305);
if (x_306 == 0)
{
uint8_t x_307; 
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec_ref(x_4);
x_307 = !lean_is_exclusive(x_304);
if (x_307 == 0)
{
lean_object* x_308; lean_object* x_309; 
x_308 = lean_ctor_get(x_304, 0);
lean_dec(x_308);
x_309 = lean_box(0);
lean_ctor_set(x_304, 0, x_309);
return x_304;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_ctor_get(x_304, 1);
lean_inc(x_310);
lean_dec(x_304);
x_311 = lean_box(0);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_310);
return x_312;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_304, 1);
lean_inc(x_313);
lean_dec_ref(x_304);
lean_inc_ref(x_4);
x_314 = l_Lean_Meta_evalNat(x_21, x_2, x_3, x_4, x_5, x_313);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
if (lean_obj_tag(x_315) == 0)
{
lean_dec_ref(x_16);
lean_dec_ref(x_4);
return x_314;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec_ref(x_314);
x_317 = lean_ctor_get(x_315, 0);
lean_inc(x_317);
lean_dec(x_315);
x_318 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_316);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
if (lean_obj_tag(x_319) == 0)
{
lean_dec(x_317);
return x_318;
}
else
{
uint8_t x_320; 
x_320 = !lean_is_exclusive(x_318);
if (x_320 == 0)
{
lean_object* x_321; uint8_t x_322; 
x_321 = lean_ctor_get(x_318, 0);
lean_dec(x_321);
x_322 = !lean_is_exclusive(x_319);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; 
x_323 = lean_ctor_get(x_319, 0);
x_324 = lean_nat_mul(x_317, x_323);
lean_dec(x_323);
lean_dec(x_317);
lean_ctor_set(x_319, 0, x_324);
return x_318;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_319, 0);
lean_inc(x_325);
lean_dec(x_319);
x_326 = lean_nat_mul(x_317, x_325);
lean_dec(x_325);
lean_dec(x_317);
x_327 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_318, 0, x_327);
return x_318;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_328 = lean_ctor_get(x_318, 1);
lean_inc(x_328);
lean_dec(x_318);
x_329 = lean_ctor_get(x_319, 0);
lean_inc(x_329);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 x_330 = x_319;
} else {
 lean_dec_ref(x_319);
 x_330 = lean_box(0);
}
x_331 = lean_nat_mul(x_317, x_329);
lean_dec(x_329);
lean_dec(x_317);
if (lean_is_scalar(x_330)) {
 x_332 = lean_alloc_ctor(1, 1, 0);
} else {
 x_332 = x_330;
}
lean_ctor_set(x_332, 0, x_331);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_328);
return x_333;
}
}
}
}
}
}
else
{
lean_object* x_334; lean_object* x_335; uint8_t x_336; 
lean_dec_ref(x_41);
lean_dec(x_10);
x_334 = l_Lean_Meta_isInstDivNat___redArg(x_36, x_3, x_9);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_unbox(x_335);
lean_dec(x_335);
if (x_336 == 0)
{
uint8_t x_337; 
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec_ref(x_4);
x_337 = !lean_is_exclusive(x_334);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; 
x_338 = lean_ctor_get(x_334, 0);
lean_dec(x_338);
x_339 = lean_box(0);
lean_ctor_set(x_334, 0, x_339);
return x_334;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_334, 1);
lean_inc(x_340);
lean_dec(x_334);
x_341 = lean_box(0);
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_340);
return x_342;
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_343 = lean_ctor_get(x_334, 1);
lean_inc(x_343);
lean_dec_ref(x_334);
lean_inc_ref(x_4);
x_344 = l_Lean_Meta_evalNat(x_21, x_2, x_3, x_4, x_5, x_343);
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
if (lean_obj_tag(x_345) == 0)
{
lean_dec_ref(x_16);
lean_dec_ref(x_4);
return x_344;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_346 = lean_ctor_get(x_344, 1);
lean_inc(x_346);
lean_dec_ref(x_344);
x_347 = lean_ctor_get(x_345, 0);
lean_inc(x_347);
lean_dec(x_345);
x_348 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_346);
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
if (lean_obj_tag(x_349) == 0)
{
lean_dec(x_347);
return x_348;
}
else
{
uint8_t x_350; 
x_350 = !lean_is_exclusive(x_348);
if (x_350 == 0)
{
lean_object* x_351; uint8_t x_352; 
x_351 = lean_ctor_get(x_348, 0);
lean_dec(x_351);
x_352 = !lean_is_exclusive(x_349);
if (x_352 == 0)
{
lean_object* x_353; lean_object* x_354; 
x_353 = lean_ctor_get(x_349, 0);
x_354 = lean_nat_div(x_347, x_353);
lean_dec(x_353);
lean_dec(x_347);
lean_ctor_set(x_349, 0, x_354);
return x_348;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_355 = lean_ctor_get(x_349, 0);
lean_inc(x_355);
lean_dec(x_349);
x_356 = lean_nat_div(x_347, x_355);
lean_dec(x_355);
lean_dec(x_347);
x_357 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_348, 0, x_357);
return x_348;
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_358 = lean_ctor_get(x_348, 1);
lean_inc(x_358);
lean_dec(x_348);
x_359 = lean_ctor_get(x_349, 0);
lean_inc(x_359);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 x_360 = x_349;
} else {
 lean_dec_ref(x_349);
 x_360 = lean_box(0);
}
x_361 = lean_nat_div(x_347, x_359);
lean_dec(x_359);
lean_dec(x_347);
if (lean_is_scalar(x_360)) {
 x_362 = lean_alloc_ctor(1, 1, 0);
} else {
 x_362 = x_360;
}
lean_ctor_set(x_362, 0, x_361);
x_363 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_358);
return x_363;
}
}
}
}
}
}
else
{
lean_object* x_364; lean_object* x_365; uint8_t x_366; 
lean_dec_ref(x_41);
lean_dec(x_10);
x_364 = l_Lean_Meta_isInstModNat___redArg(x_36, x_3, x_9);
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_unbox(x_365);
lean_dec(x_365);
if (x_366 == 0)
{
uint8_t x_367; 
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec_ref(x_4);
x_367 = !lean_is_exclusive(x_364);
if (x_367 == 0)
{
lean_object* x_368; lean_object* x_369; 
x_368 = lean_ctor_get(x_364, 0);
lean_dec(x_368);
x_369 = lean_box(0);
lean_ctor_set(x_364, 0, x_369);
return x_364;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_370 = lean_ctor_get(x_364, 1);
lean_inc(x_370);
lean_dec(x_364);
x_371 = lean_box(0);
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_370);
return x_372;
}
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_373 = lean_ctor_get(x_364, 1);
lean_inc(x_373);
lean_dec_ref(x_364);
lean_inc_ref(x_4);
x_374 = l_Lean_Meta_evalNat(x_21, x_2, x_3, x_4, x_5, x_373);
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
if (lean_obj_tag(x_375) == 0)
{
lean_dec_ref(x_16);
lean_dec_ref(x_4);
return x_374;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_376 = lean_ctor_get(x_374, 1);
lean_inc(x_376);
lean_dec_ref(x_374);
x_377 = lean_ctor_get(x_375, 0);
lean_inc(x_377);
lean_dec(x_375);
x_378 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_376);
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
if (lean_obj_tag(x_379) == 0)
{
lean_dec(x_377);
return x_378;
}
else
{
uint8_t x_380; 
x_380 = !lean_is_exclusive(x_378);
if (x_380 == 0)
{
lean_object* x_381; uint8_t x_382; 
x_381 = lean_ctor_get(x_378, 0);
lean_dec(x_381);
x_382 = !lean_is_exclusive(x_379);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; 
x_383 = lean_ctor_get(x_379, 0);
x_384 = lean_nat_mod(x_377, x_383);
lean_dec(x_383);
lean_dec(x_377);
lean_ctor_set(x_379, 0, x_384);
return x_378;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_385 = lean_ctor_get(x_379, 0);
lean_inc(x_385);
lean_dec(x_379);
x_386 = lean_nat_mod(x_377, x_385);
lean_dec(x_385);
lean_dec(x_377);
x_387 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_378, 0, x_387);
return x_378;
}
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_388 = lean_ctor_get(x_378, 1);
lean_inc(x_388);
lean_dec(x_378);
x_389 = lean_ctor_get(x_379, 0);
lean_inc(x_389);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 x_390 = x_379;
} else {
 lean_dec_ref(x_379);
 x_390 = lean_box(0);
}
x_391 = lean_nat_mod(x_377, x_389);
lean_dec(x_389);
lean_dec(x_377);
if (lean_is_scalar(x_390)) {
 x_392 = lean_alloc_ctor(1, 1, 0);
} else {
 x_392 = x_390;
}
lean_ctor_set(x_392, 0, x_391);
x_393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_388);
return x_393;
}
}
}
}
}
}
else
{
lean_object* x_394; lean_object* x_395; uint8_t x_396; 
lean_dec_ref(x_41);
lean_dec(x_10);
x_394 = l_Lean_Meta_isInstNatPowNat___redArg(x_36, x_3, x_9);
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_unbox(x_395);
lean_dec(x_395);
if (x_396 == 0)
{
uint8_t x_397; 
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec_ref(x_4);
x_397 = !lean_is_exclusive(x_394);
if (x_397 == 0)
{
lean_object* x_398; lean_object* x_399; 
x_398 = lean_ctor_get(x_394, 0);
lean_dec(x_398);
x_399 = lean_box(0);
lean_ctor_set(x_394, 0, x_399);
return x_394;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_400 = lean_ctor_get(x_394, 1);
lean_inc(x_400);
lean_dec(x_394);
x_401 = lean_box(0);
x_402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_400);
return x_402;
}
}
else
{
lean_object* x_403; lean_object* x_404; 
x_403 = lean_ctor_get(x_394, 1);
lean_inc(x_403);
lean_dec_ref(x_394);
x_404 = l_Lean_Meta_evalNat_evalPow(x_21, x_16, x_2, x_3, x_4, x_5, x_403);
return x_404;
}
}
}
}
else
{
lean_object* x_405; lean_object* x_406; uint8_t x_407; 
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec(x_10);
x_405 = l_Lean_Meta_isInstOfNatNat___redArg(x_16, x_3, x_9);
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_unbox(x_406);
lean_dec(x_406);
if (x_407 == 0)
{
uint8_t x_408; 
lean_dec_ref(x_21);
lean_dec_ref(x_4);
x_408 = !lean_is_exclusive(x_405);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; 
x_409 = lean_ctor_get(x_405, 0);
lean_dec(x_409);
x_410 = lean_box(0);
lean_ctor_set(x_405, 0, x_410);
return x_405;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_411 = lean_ctor_get(x_405, 1);
lean_inc(x_411);
lean_dec(x_405);
x_412 = lean_box(0);
x_413 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_411);
return x_413;
}
}
else
{
lean_object* x_414; lean_object* x_415; 
x_414 = lean_ctor_get(x_405, 1);
lean_inc(x_414);
lean_dec_ref(x_405);
x_415 = l_Lean_Meta_evalNat(x_21, x_2, x_3, x_4, x_5, x_414);
return x_415;
}
}
}
}
else
{
lean_object* x_416; lean_object* x_417; 
lean_dec_ref(x_22);
lean_dec(x_10);
lean_inc_ref(x_4);
x_416 = l_Lean_Meta_evalNat(x_21, x_2, x_3, x_4, x_5, x_9);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
if (lean_obj_tag(x_417) == 0)
{
lean_dec_ref(x_16);
lean_dec_ref(x_4);
return x_416;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
lean_dec_ref(x_416);
x_419 = lean_ctor_get(x_417, 0);
lean_inc(x_419);
lean_dec(x_417);
x_420 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_418);
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
if (lean_obj_tag(x_421) == 0)
{
lean_dec(x_419);
return x_420;
}
else
{
uint8_t x_422; 
x_422 = !lean_is_exclusive(x_420);
if (x_422 == 0)
{
lean_object* x_423; uint8_t x_424; 
x_423 = lean_ctor_get(x_420, 0);
lean_dec(x_423);
x_424 = !lean_is_exclusive(x_421);
if (x_424 == 0)
{
lean_object* x_425; lean_object* x_426; 
x_425 = lean_ctor_get(x_421, 0);
x_426 = lean_nat_add(x_419, x_425);
lean_dec(x_425);
lean_dec(x_419);
lean_ctor_set(x_421, 0, x_426);
return x_420;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_421, 0);
lean_inc(x_427);
lean_dec(x_421);
x_428 = lean_nat_add(x_419, x_427);
lean_dec(x_427);
lean_dec(x_419);
x_429 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_429, 0, x_428);
lean_ctor_set(x_420, 0, x_429);
return x_420;
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_430 = lean_ctor_get(x_420, 1);
lean_inc(x_430);
lean_dec(x_420);
x_431 = lean_ctor_get(x_421, 0);
lean_inc(x_431);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 x_432 = x_421;
} else {
 lean_dec_ref(x_421);
 x_432 = lean_box(0);
}
x_433 = lean_nat_add(x_419, x_431);
lean_dec(x_431);
lean_dec(x_419);
if (lean_is_scalar(x_432)) {
 x_434 = lean_alloc_ctor(1, 1, 0);
} else {
 x_434 = x_432;
}
lean_ctor_set(x_434, 0, x_433);
x_435 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_435, 0, x_434);
lean_ctor_set(x_435, 1, x_430);
return x_435;
}
}
}
}
}
else
{
lean_object* x_436; lean_object* x_437; 
lean_dec_ref(x_22);
lean_dec(x_10);
lean_inc_ref(x_4);
x_436 = l_Lean_Meta_evalNat(x_21, x_2, x_3, x_4, x_5, x_9);
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
if (lean_obj_tag(x_437) == 0)
{
lean_dec_ref(x_16);
lean_dec_ref(x_4);
return x_436;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_438 = lean_ctor_get(x_436, 1);
lean_inc(x_438);
lean_dec_ref(x_436);
x_439 = lean_ctor_get(x_437, 0);
lean_inc(x_439);
lean_dec(x_437);
x_440 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_438);
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
if (lean_obj_tag(x_441) == 0)
{
lean_dec(x_439);
return x_440;
}
else
{
uint8_t x_442; 
x_442 = !lean_is_exclusive(x_440);
if (x_442 == 0)
{
lean_object* x_443; uint8_t x_444; 
x_443 = lean_ctor_get(x_440, 0);
lean_dec(x_443);
x_444 = !lean_is_exclusive(x_441);
if (x_444 == 0)
{
lean_object* x_445; lean_object* x_446; 
x_445 = lean_ctor_get(x_441, 0);
x_446 = lean_nat_sub(x_439, x_445);
lean_dec(x_445);
lean_dec(x_439);
lean_ctor_set(x_441, 0, x_446);
return x_440;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_447 = lean_ctor_get(x_441, 0);
lean_inc(x_447);
lean_dec(x_441);
x_448 = lean_nat_sub(x_439, x_447);
lean_dec(x_447);
lean_dec(x_439);
x_449 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_449, 0, x_448);
lean_ctor_set(x_440, 0, x_449);
return x_440;
}
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_450 = lean_ctor_get(x_440, 1);
lean_inc(x_450);
lean_dec(x_440);
x_451 = lean_ctor_get(x_441, 0);
lean_inc(x_451);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 x_452 = x_441;
} else {
 lean_dec_ref(x_441);
 x_452 = lean_box(0);
}
x_453 = lean_nat_sub(x_439, x_451);
lean_dec(x_451);
lean_dec(x_439);
if (lean_is_scalar(x_452)) {
 x_454 = lean_alloc_ctor(1, 1, 0);
} else {
 x_454 = x_452;
}
lean_ctor_set(x_454, 0, x_453);
x_455 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_455, 0, x_454);
lean_ctor_set(x_455, 1, x_450);
return x_455;
}
}
}
}
}
else
{
lean_object* x_456; lean_object* x_457; 
lean_dec_ref(x_22);
lean_dec(x_10);
lean_inc_ref(x_4);
x_456 = l_Lean_Meta_evalNat(x_21, x_2, x_3, x_4, x_5, x_9);
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
if (lean_obj_tag(x_457) == 0)
{
lean_dec_ref(x_16);
lean_dec_ref(x_4);
return x_456;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_458 = lean_ctor_get(x_456, 1);
lean_inc(x_458);
lean_dec_ref(x_456);
x_459 = lean_ctor_get(x_457, 0);
lean_inc(x_459);
lean_dec(x_457);
x_460 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_458);
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
if (lean_obj_tag(x_461) == 0)
{
lean_dec(x_459);
return x_460;
}
else
{
uint8_t x_462; 
x_462 = !lean_is_exclusive(x_460);
if (x_462 == 0)
{
lean_object* x_463; uint8_t x_464; 
x_463 = lean_ctor_get(x_460, 0);
lean_dec(x_463);
x_464 = !lean_is_exclusive(x_461);
if (x_464 == 0)
{
lean_object* x_465; lean_object* x_466; 
x_465 = lean_ctor_get(x_461, 0);
x_466 = lean_nat_mul(x_459, x_465);
lean_dec(x_465);
lean_dec(x_459);
lean_ctor_set(x_461, 0, x_466);
return x_460;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_467 = lean_ctor_get(x_461, 0);
lean_inc(x_467);
lean_dec(x_461);
x_468 = lean_nat_mul(x_459, x_467);
lean_dec(x_467);
lean_dec(x_459);
x_469 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_469, 0, x_468);
lean_ctor_set(x_460, 0, x_469);
return x_460;
}
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_470 = lean_ctor_get(x_460, 1);
lean_inc(x_470);
lean_dec(x_460);
x_471 = lean_ctor_get(x_461, 0);
lean_inc(x_471);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 x_472 = x_461;
} else {
 lean_dec_ref(x_461);
 x_472 = lean_box(0);
}
x_473 = lean_nat_mul(x_459, x_471);
lean_dec(x_471);
lean_dec(x_459);
if (lean_is_scalar(x_472)) {
 x_474 = lean_alloc_ctor(1, 1, 0);
} else {
 x_474 = x_472;
}
lean_ctor_set(x_474, 0, x_473);
x_475 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_475, 0, x_474);
lean_ctor_set(x_475, 1, x_470);
return x_475;
}
}
}
}
}
else
{
lean_object* x_476; lean_object* x_477; 
lean_dec_ref(x_22);
lean_dec(x_10);
lean_inc_ref(x_4);
x_476 = l_Lean_Meta_evalNat(x_21, x_2, x_3, x_4, x_5, x_9);
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
if (lean_obj_tag(x_477) == 0)
{
lean_dec_ref(x_16);
lean_dec_ref(x_4);
return x_476;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_478 = lean_ctor_get(x_476, 1);
lean_inc(x_478);
lean_dec_ref(x_476);
x_479 = lean_ctor_get(x_477, 0);
lean_inc(x_479);
lean_dec(x_477);
x_480 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_478);
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
if (lean_obj_tag(x_481) == 0)
{
lean_dec(x_479);
return x_480;
}
else
{
uint8_t x_482; 
x_482 = !lean_is_exclusive(x_480);
if (x_482 == 0)
{
lean_object* x_483; uint8_t x_484; 
x_483 = lean_ctor_get(x_480, 0);
lean_dec(x_483);
x_484 = !lean_is_exclusive(x_481);
if (x_484 == 0)
{
lean_object* x_485; lean_object* x_486; 
x_485 = lean_ctor_get(x_481, 0);
x_486 = lean_nat_div(x_479, x_485);
lean_dec(x_485);
lean_dec(x_479);
lean_ctor_set(x_481, 0, x_486);
return x_480;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_487 = lean_ctor_get(x_481, 0);
lean_inc(x_487);
lean_dec(x_481);
x_488 = lean_nat_div(x_479, x_487);
lean_dec(x_487);
lean_dec(x_479);
x_489 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_480, 0, x_489);
return x_480;
}
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_490 = lean_ctor_get(x_480, 1);
lean_inc(x_490);
lean_dec(x_480);
x_491 = lean_ctor_get(x_481, 0);
lean_inc(x_491);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 x_492 = x_481;
} else {
 lean_dec_ref(x_481);
 x_492 = lean_box(0);
}
x_493 = lean_nat_div(x_479, x_491);
lean_dec(x_491);
lean_dec(x_479);
if (lean_is_scalar(x_492)) {
 x_494 = lean_alloc_ctor(1, 1, 0);
} else {
 x_494 = x_492;
}
lean_ctor_set(x_494, 0, x_493);
x_495 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_495, 0, x_494);
lean_ctor_set(x_495, 1, x_490);
return x_495;
}
}
}
}
}
else
{
lean_object* x_496; lean_object* x_497; 
lean_dec_ref(x_22);
lean_dec(x_10);
lean_inc_ref(x_4);
x_496 = l_Lean_Meta_evalNat(x_21, x_2, x_3, x_4, x_5, x_9);
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
if (lean_obj_tag(x_497) == 0)
{
lean_dec_ref(x_16);
lean_dec_ref(x_4);
return x_496;
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_498 = lean_ctor_get(x_496, 1);
lean_inc(x_498);
lean_dec_ref(x_496);
x_499 = lean_ctor_get(x_497, 0);
lean_inc(x_499);
lean_dec(x_497);
x_500 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_498);
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
if (lean_obj_tag(x_501) == 0)
{
lean_dec(x_499);
return x_500;
}
else
{
uint8_t x_502; 
x_502 = !lean_is_exclusive(x_500);
if (x_502 == 0)
{
lean_object* x_503; uint8_t x_504; 
x_503 = lean_ctor_get(x_500, 0);
lean_dec(x_503);
x_504 = !lean_is_exclusive(x_501);
if (x_504 == 0)
{
lean_object* x_505; lean_object* x_506; 
x_505 = lean_ctor_get(x_501, 0);
x_506 = lean_nat_mod(x_499, x_505);
lean_dec(x_505);
lean_dec(x_499);
lean_ctor_set(x_501, 0, x_506);
return x_500;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_507 = lean_ctor_get(x_501, 0);
lean_inc(x_507);
lean_dec(x_501);
x_508 = lean_nat_mod(x_499, x_507);
lean_dec(x_507);
lean_dec(x_499);
x_509 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_509, 0, x_508);
lean_ctor_set(x_500, 0, x_509);
return x_500;
}
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_510 = lean_ctor_get(x_500, 1);
lean_inc(x_510);
lean_dec(x_500);
x_511 = lean_ctor_get(x_501, 0);
lean_inc(x_511);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 x_512 = x_501;
} else {
 lean_dec_ref(x_501);
 x_512 = lean_box(0);
}
x_513 = lean_nat_mod(x_499, x_511);
lean_dec(x_511);
lean_dec(x_499);
if (lean_is_scalar(x_512)) {
 x_514 = lean_alloc_ctor(1, 1, 0);
} else {
 x_514 = x_512;
}
lean_ctor_set(x_514, 0, x_513);
x_515 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_515, 0, x_514);
lean_ctor_set(x_515, 1, x_510);
return x_515;
}
}
}
}
}
else
{
lean_object* x_516; 
lean_dec_ref(x_22);
lean_dec(x_10);
x_516 = l_Lean_Meta_evalNat_evalPow(x_21, x_16, x_2, x_3, x_4, x_5, x_9);
return x_516;
}
}
}
else
{
lean_object* x_517; lean_object* x_518; 
lean_dec_ref(x_17);
lean_dec(x_10);
x_517 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_9);
x_518 = lean_ctor_get(x_517, 0);
lean_inc(x_518);
if (lean_obj_tag(x_518) == 0)
{
return x_517;
}
else
{
uint8_t x_519; 
x_519 = !lean_is_exclusive(x_517);
if (x_519 == 0)
{
lean_object* x_520; uint8_t x_521; 
x_520 = lean_ctor_get(x_517, 0);
lean_dec(x_520);
x_521 = !lean_is_exclusive(x_518);
if (x_521 == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_522 = lean_ctor_get(x_518, 0);
x_523 = lean_unsigned_to_nat(1u);
x_524 = lean_nat_add(x_522, x_523);
lean_dec(x_522);
lean_ctor_set(x_518, 0, x_524);
return x_517;
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_525 = lean_ctor_get(x_518, 0);
lean_inc(x_525);
lean_dec(x_518);
x_526 = lean_unsigned_to_nat(1u);
x_527 = lean_nat_add(x_525, x_526);
lean_dec(x_525);
x_528 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_517, 0, x_528);
return x_517;
}
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_529 = lean_ctor_get(x_517, 1);
lean_inc(x_529);
lean_dec(x_517);
x_530 = lean_ctor_get(x_518, 0);
lean_inc(x_530);
if (lean_is_exclusive(x_518)) {
 lean_ctor_release(x_518, 0);
 x_531 = x_518;
} else {
 lean_dec_ref(x_518);
 x_531 = lean_box(0);
}
x_532 = lean_unsigned_to_nat(1u);
x_533 = lean_nat_add(x_530, x_532);
lean_dec(x_530);
if (lean_is_scalar(x_531)) {
 x_534 = lean_alloc_ctor(1, 1, 0);
} else {
 x_534 = x_531;
}
lean_ctor_set(x_534, 0, x_533);
x_535 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_535, 0, x_534);
lean_ctor_set(x_535, 1, x_529);
return x_535;
}
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
if (lean_is_scalar(x_10)) {
 x_12 = lean_alloc_ctor(0, 2, 0);
} else {
 x_12 = x_10;
}
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat_evalPow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_evalNat_evalPow(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_evalNat(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_evalNat_visit(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___redArg(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; lean_object* x_18; 
x_12 = lean_ctor_get_uint64(x_4, sizeof(void*)*7);
lean_ctor_set_uint8(x_10, 9, x_1);
x_13 = 2;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_shift_left(x_14, x_13);
x_16 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_17 = lean_uint64_lor(x_15, x_16);
lean_ctor_set_uint64(x_4, sizeof(void*)*7, x_17);
x_18 = l_Lean_Meta_isExprDefEq(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
else
{
uint64_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; lean_object* x_44; 
x_19 = lean_ctor_get_uint64(x_4, sizeof(void*)*7);
x_20 = lean_ctor_get_uint8(x_10, 0);
x_21 = lean_ctor_get_uint8(x_10, 1);
x_22 = lean_ctor_get_uint8(x_10, 2);
x_23 = lean_ctor_get_uint8(x_10, 3);
x_24 = lean_ctor_get_uint8(x_10, 4);
x_25 = lean_ctor_get_uint8(x_10, 5);
x_26 = lean_ctor_get_uint8(x_10, 6);
x_27 = lean_ctor_get_uint8(x_10, 7);
x_28 = lean_ctor_get_uint8(x_10, 8);
x_29 = lean_ctor_get_uint8(x_10, 10);
x_30 = lean_ctor_get_uint8(x_10, 11);
x_31 = lean_ctor_get_uint8(x_10, 12);
x_32 = lean_ctor_get_uint8(x_10, 13);
x_33 = lean_ctor_get_uint8(x_10, 14);
x_34 = lean_ctor_get_uint8(x_10, 15);
x_35 = lean_ctor_get_uint8(x_10, 16);
x_36 = lean_ctor_get_uint8(x_10, 17);
x_37 = lean_ctor_get_uint8(x_10, 18);
lean_dec(x_10);
x_38 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_38, 0, x_20);
lean_ctor_set_uint8(x_38, 1, x_21);
lean_ctor_set_uint8(x_38, 2, x_22);
lean_ctor_set_uint8(x_38, 3, x_23);
lean_ctor_set_uint8(x_38, 4, x_24);
lean_ctor_set_uint8(x_38, 5, x_25);
lean_ctor_set_uint8(x_38, 6, x_26);
lean_ctor_set_uint8(x_38, 7, x_27);
lean_ctor_set_uint8(x_38, 8, x_28);
lean_ctor_set_uint8(x_38, 9, x_1);
lean_ctor_set_uint8(x_38, 10, x_29);
lean_ctor_set_uint8(x_38, 11, x_30);
lean_ctor_set_uint8(x_38, 12, x_31);
lean_ctor_set_uint8(x_38, 13, x_32);
lean_ctor_set_uint8(x_38, 14, x_33);
lean_ctor_set_uint8(x_38, 15, x_34);
lean_ctor_set_uint8(x_38, 16, x_35);
lean_ctor_set_uint8(x_38, 17, x_36);
lean_ctor_set_uint8(x_38, 18, x_37);
x_39 = 2;
x_40 = lean_uint64_shift_right(x_19, x_39);
x_41 = lean_uint64_shift_left(x_40, x_39);
x_42 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_43 = lean_uint64_lor(x_41, x_42);
lean_ctor_set(x_4, 0, x_38);
lean_ctor_set_uint64(x_4, sizeof(void*)*7, x_43);
x_44 = l_Lean_Meta_isExprDefEq(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_44;
}
}
else
{
lean_object* x_45; uint64_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; lean_object* x_81; lean_object* x_82; 
x_45 = lean_ctor_get(x_4, 0);
x_46 = lean_ctor_get_uint64(x_4, sizeof(void*)*7);
x_47 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_48 = lean_ctor_get(x_4, 1);
x_49 = lean_ctor_get(x_4, 2);
x_50 = lean_ctor_get(x_4, 3);
x_51 = lean_ctor_get(x_4, 4);
x_52 = lean_ctor_get(x_4, 5);
x_53 = lean_ctor_get(x_4, 6);
x_54 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_55 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_45);
lean_dec(x_4);
x_56 = lean_ctor_get_uint8(x_45, 0);
x_57 = lean_ctor_get_uint8(x_45, 1);
x_58 = lean_ctor_get_uint8(x_45, 2);
x_59 = lean_ctor_get_uint8(x_45, 3);
x_60 = lean_ctor_get_uint8(x_45, 4);
x_61 = lean_ctor_get_uint8(x_45, 5);
x_62 = lean_ctor_get_uint8(x_45, 6);
x_63 = lean_ctor_get_uint8(x_45, 7);
x_64 = lean_ctor_get_uint8(x_45, 8);
x_65 = lean_ctor_get_uint8(x_45, 10);
x_66 = lean_ctor_get_uint8(x_45, 11);
x_67 = lean_ctor_get_uint8(x_45, 12);
x_68 = lean_ctor_get_uint8(x_45, 13);
x_69 = lean_ctor_get_uint8(x_45, 14);
x_70 = lean_ctor_get_uint8(x_45, 15);
x_71 = lean_ctor_get_uint8(x_45, 16);
x_72 = lean_ctor_get_uint8(x_45, 17);
x_73 = lean_ctor_get_uint8(x_45, 18);
if (lean_is_exclusive(x_45)) {
 x_74 = x_45;
} else {
 lean_dec_ref(x_45);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 0, 19);
} else {
 x_75 = x_74;
}
lean_ctor_set_uint8(x_75, 0, x_56);
lean_ctor_set_uint8(x_75, 1, x_57);
lean_ctor_set_uint8(x_75, 2, x_58);
lean_ctor_set_uint8(x_75, 3, x_59);
lean_ctor_set_uint8(x_75, 4, x_60);
lean_ctor_set_uint8(x_75, 5, x_61);
lean_ctor_set_uint8(x_75, 6, x_62);
lean_ctor_set_uint8(x_75, 7, x_63);
lean_ctor_set_uint8(x_75, 8, x_64);
lean_ctor_set_uint8(x_75, 9, x_1);
lean_ctor_set_uint8(x_75, 10, x_65);
lean_ctor_set_uint8(x_75, 11, x_66);
lean_ctor_set_uint8(x_75, 12, x_67);
lean_ctor_set_uint8(x_75, 13, x_68);
lean_ctor_set_uint8(x_75, 14, x_69);
lean_ctor_set_uint8(x_75, 15, x_70);
lean_ctor_set_uint8(x_75, 16, x_71);
lean_ctor_set_uint8(x_75, 17, x_72);
lean_ctor_set_uint8(x_75, 18, x_73);
x_76 = 2;
x_77 = lean_uint64_shift_right(x_46, x_76);
x_78 = lean_uint64_shift_left(x_77, x_76);
x_79 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_80 = lean_uint64_lor(x_78, x_79);
x_81 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_48);
lean_ctor_set(x_81, 2, x_49);
lean_ctor_set(x_81, 3, x_50);
lean_ctor_set(x_81, 4, x_51);
lean_ctor_set(x_81, 5, x_52);
lean_ctor_set(x_81, 6, x_53);
lean_ctor_set_uint64(x_81, sizeof(void*)*7, x_80);
lean_ctor_set_uint8(x_81, sizeof(void*)*7 + 8, x_47);
lean_ctor_set_uint8(x_81, sizeof(void*)*7 + 9, x_54);
lean_ctor_set_uint8(x_81, sizeof(void*)*7 + 10, x_55);
x_82 = l_Lean_Meta_isExprDefEq(x_2, x_3, x_81, x_5, x_6, x_7, x_8);
return x_82;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = 3;
x_9 = lean_box(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_matchesInstance___lam__0___boxed), 8, 3);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_2);
x_11 = 0;
x_12 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_10, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Meta_matchesInstance___lam__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc_ref(x_1);
x_7 = l_Lean_Meta_isOffset_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec_ref(x_1);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_7, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
lean_dec(x_8);
lean_ctor_set(x_7, 0, x_19);
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_dec(x_7);
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
lean_dec(x_8);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec_ref(x_1);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isOffset_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; uint8_t x_15; 
x_7 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_14 = l_Lean_Expr_cleanupAnnotations(x_8);
x_15 = l_Lean_Expr_isApp(x_14);
if (x_15 == 0)
{
lean_dec_ref(x_14);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_13;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_16);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_18 = l_Lean_Meta_evalNat_visit___closed__1;
x_19 = l_Lean_Expr_isConstOf(x_17, x_18);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Expr_isApp(x_17);
if (x_20 == 0)
{
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_21);
x_78 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_79 = l_Lean_Meta_evalNat_visit___closed__13;
x_80 = l_Lean_Expr_isConstOf(x_78, x_79);
if (x_80 == 0)
{
uint8_t x_81; 
x_81 = l_Lean_Expr_isApp(x_78);
if (x_81 == 0)
{
lean_dec_ref(x_78);
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_13;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_78, 1);
lean_inc_ref(x_82);
x_83 = l_Lean_Expr_appFnCleanup___redArg(x_78);
x_84 = l_Lean_Expr_isApp(x_83);
if (x_84 == 0)
{
lean_dec_ref(x_83);
lean_dec_ref(x_82);
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_13;
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = l_Lean_Expr_appFnCleanup___redArg(x_83);
x_86 = l_Lean_Meta_evalNat_visit___closed__28;
x_87 = l_Lean_Expr_isConstOf(x_85, x_86);
if (x_87 == 0)
{
uint8_t x_88; 
x_88 = l_Lean_Expr_isApp(x_85);
if (x_88 == 0)
{
lean_dec_ref(x_85);
lean_dec_ref(x_82);
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_13;
}
else
{
lean_object* x_89; uint8_t x_90; 
x_89 = l_Lean_Expr_appFnCleanup___redArg(x_85);
x_90 = l_Lean_Expr_isApp(x_89);
if (x_90 == 0)
{
lean_dec_ref(x_89);
lean_dec_ref(x_82);
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_13;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = l_Lean_Expr_appFnCleanup___redArg(x_89);
x_92 = l_Lean_Meta_evalNat_visit___closed__48;
x_93 = l_Lean_Expr_isConstOf(x_91, x_92);
lean_dec_ref(x_91);
if (x_93 == 0)
{
lean_dec_ref(x_82);
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_13;
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_10);
x_94 = l_Lean_Nat_mkInstHAdd;
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_95 = l_Lean_Meta_matchesInstance(x_82, x_94, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_unbox(x_96);
lean_dec(x_96);
if (x_97 == 0)
{
uint8_t x_98; 
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_98 = !lean_is_exclusive(x_95);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_95, 0);
lean_dec(x_99);
x_100 = lean_box(0);
lean_ctor_set(x_95, 0, x_100);
return x_95;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
lean_dec(x_95);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
else
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_95, 1);
lean_inc(x_104);
lean_dec_ref(x_95);
x_22 = x_16;
x_23 = x_2;
x_24 = x_3;
x_25 = x_4;
x_26 = x_5;
x_27 = x_104;
goto block_77;
}
}
else
{
uint8_t x_105; 
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_105 = !lean_is_exclusive(x_95);
if (x_105 == 0)
{
return x_95;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_95, 0);
x_107 = lean_ctor_get(x_95, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_95);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec_ref(x_85);
lean_dec(x_10);
x_109 = l_Lean_Nat_mkInstAdd;
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_110 = l_Lean_Meta_matchesInstance(x_82, x_109, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
lean_dec(x_111);
if (x_112 == 0)
{
uint8_t x_113; 
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_113 = !lean_is_exclusive(x_110);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_110, 0);
lean_dec(x_114);
x_115 = lean_box(0);
lean_ctor_set(x_110, 0, x_115);
return x_110;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_110, 1);
lean_inc(x_116);
lean_dec(x_110);
x_117 = lean_box(0);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
else
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_110, 1);
lean_inc(x_119);
lean_dec_ref(x_110);
x_22 = x_16;
x_23 = x_2;
x_24 = x_3;
x_25 = x_4;
x_26 = x_5;
x_27 = x_119;
goto block_77;
}
}
else
{
uint8_t x_120; 
lean_dec_ref(x_21);
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_120 = !lean_is_exclusive(x_110);
if (x_120 == 0)
{
return x_110;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_110, 0);
x_122 = lean_ctor_get(x_110, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_110);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
}
}
else
{
lean_dec_ref(x_78);
lean_dec(x_10);
x_22 = x_16;
x_23 = x_2;
x_24 = x_3;
x_25 = x_4;
x_26 = x_5;
x_27 = x_9;
goto block_77;
}
block_77:
{
lean_object* x_28; lean_object* x_29; 
lean_inc_ref(x_25);
x_28 = l_Lean_Meta_evalNat(x_22, x_23, x_24, x_25, x_26, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_21);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_dec_ref(x_28);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(x_21, x_23, x_24, x_25, x_26, x_36);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 1);
x_44 = lean_nat_add(x_43, x_38);
lean_dec(x_38);
lean_dec(x_43);
lean_ctor_set(x_41, 1, x_44);
lean_ctor_set(x_29, 0, x_41);
lean_ctor_set(x_39, 0, x_29);
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_41, 0);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_41);
x_47 = lean_nat_add(x_46, x_38);
lean_dec(x_38);
lean_dec(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_29, 0, x_48);
lean_ctor_set(x_39, 0, x_29);
return x_39;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_39, 0);
x_50 = lean_ctor_get(x_39, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_39);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_53 = x_49;
} else {
 lean_dec_ref(x_49);
 x_53 = lean_box(0);
}
x_54 = lean_nat_add(x_52, x_38);
lean_dec(x_38);
lean_dec(x_52);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_29, 0, x_55);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_29);
lean_ctor_set(x_56, 1, x_50);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_free_object(x_29);
lean_dec(x_38);
x_57 = !lean_is_exclusive(x_39);
if (x_57 == 0)
{
return x_39;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_39, 0);
x_59 = lean_ctor_get(x_39, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_39);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_29, 0);
lean_inc(x_61);
lean_dec(x_29);
x_62 = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(x_21, x_23, x_24, x_25, x_26, x_36);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
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
x_66 = lean_ctor_get(x_63, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_68 = x_63;
} else {
 lean_dec_ref(x_63);
 x_68 = lean_box(0);
}
x_69 = lean_nat_add(x_67, x_61);
lean_dec(x_61);
lean_dec(x_67);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
if (lean_is_scalar(x_65)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_65;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_64);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_61);
x_73 = lean_ctor_get(x_62, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_62, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_75 = x_62;
} else {
 lean_dec_ref(x_62);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
}
}
}
else
{
lean_object* x_124; 
lean_dec_ref(x_17);
lean_dec(x_10);
x_124 = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(x_16, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_124) == 0)
{
uint8_t x_125; 
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; uint8_t x_127; 
x_126 = lean_ctor_get(x_124, 0);
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_126, 1);
x_129 = lean_unsigned_to_nat(1u);
x_130 = lean_nat_add(x_128, x_129);
lean_dec(x_128);
lean_ctor_set(x_126, 1, x_130);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_126);
lean_ctor_set(x_124, 0, x_131);
return x_124;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_132 = lean_ctor_get(x_126, 0);
x_133 = lean_ctor_get(x_126, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_126);
x_134 = lean_unsigned_to_nat(1u);
x_135 = lean_nat_add(x_133, x_134);
lean_dec(x_133);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_132);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_124, 0, x_137);
return x_124;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_138 = lean_ctor_get(x_124, 0);
x_139 = lean_ctor_get(x_124, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_124);
x_140 = lean_ctor_get(x_138, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_142 = x_138;
} else {
 lean_dec_ref(x_138);
 x_142 = lean_box(0);
}
x_143 = lean_unsigned_to_nat(1u);
x_144 = lean_nat_add(x_141, x_143);
lean_dec(x_141);
if (lean_is_scalar(x_142)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_142;
}
lean_ctor_set(x_145, 0, x_140);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_139);
return x_147;
}
}
else
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_124);
if (x_148 == 0)
{
return x_124;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_124, 0);
x_150 = lean_ctor_get(x_124, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_124);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
if (lean_is_scalar(x_10)) {
 x_12 = lean_alloc_ctor(0, 2, 0);
} else {
 x_12 = x_10;
}
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_evalNat(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = 0;
x_12 = lean_box(x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_7, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_19);
x_22 = lean_box(x_21);
lean_ctor_set(x_7, 0, x_22);
return x_7;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_dec(x_7);
x_24 = lean_ctor_get(x_8, 0);
lean_inc(x_24);
lean_dec(x_8);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_eq(x_24, x_25);
lean_dec(x_24);
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc_ref(x_1);
x_10 = l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(x_1, x_3, x_4, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = l_Lean_mkNatLit(x_2);
x_16 = l_Lean_mkNatAdd(x_1, x_15);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = l_Lean_mkNatLit(x_2);
x_19 = l_Lean_mkNatAdd(x_1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec_ref(x_1);
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_10, 0);
lean_dec(x_22);
x_23 = l_Lean_mkNatLit(x_2);
lean_ctor_set(x_10, 0, x_23);
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
x_25 = l_Lean_mkNatLit(x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
else
{
lean_object* x_27; 
lean_dec_ref(x_5);
lean_dec(x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_7);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_isDefEqOffset___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_evalNat___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_isDefEqOffset___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isDefEqOffset___lam__0___closed__0;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Lean_Meta_isDefEqOffset___lam__0___closed__1;
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux___boxed), 7, 2);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_11);
x_13 = 0;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_14 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_12, x_13, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = 2;
x_20 = lean_box(x_19);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = 2;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec_ref(x_14);
x_26 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
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
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_is_expr_def_eq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
x_12 = l_Bool_toLBool(x_11);
x_13 = lean_box(x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_unbox(x_14);
lean_dec(x_14);
x_17 = l_Bool_toLBool(x_16);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Meta_getConfig___redArg(x_3, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_9, 8);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = 2;
x_14 = lean_box(x_13);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = 2;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec_ref(x_8);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_20 = l_Lean_Meta_isOffset_x3f(x_1, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_33 = l_Lean_Meta_evalNat(x_1, x_3, x_4, x_5, x_6, x_22);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_37 = 2;
x_38 = lean_box(x_37);
lean_ctor_set(x_33, 0, x_38);
return x_33;
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = 2;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
lean_dec_ref(x_33);
x_44 = lean_ctor_get(x_34, 0);
lean_inc(x_44);
lean_dec(x_34);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_45 = l_Lean_Meta_isOffset_x3f(x_2, x_3, x_4, x_5, x_6, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
lean_inc_ref(x_5);
x_48 = l_Lean_Meta_evalNat(x_2, x_3, x_4, x_5, x_6, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
lean_dec(x_44);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_48, 0);
lean_dec(x_51);
x_52 = 2;
x_53 = lean_box(x_52);
lean_ctor_set(x_48, 0, x_53);
return x_48;
}
else
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_dec(x_48);
x_55 = 2;
x_56 = lean_box(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_48, 1);
lean_inc(x_58);
lean_dec_ref(x_48);
x_59 = lean_ctor_get(x_49, 0);
lean_inc(x_59);
lean_dec(x_49);
x_60 = lean_nat_dec_eq(x_44, x_59);
lean_dec(x_59);
lean_dec(x_44);
x_61 = l_Bool_toLBool(x_60);
x_62 = lean_box(x_61);
x_63 = lean_alloc_closure((void*)(l_Lean_Meta_isDefEqOffset___lam__2___boxed), 6, 1);
lean_closure_set(x_63, 0, x_62);
x_64 = l_Lean_Meta_isDefEqOffset___lam__0(x_1, x_63, x_3, x_4, x_5, x_6, x_58);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_dec_ref(x_2);
x_65 = lean_ctor_get(x_46, 0);
lean_inc(x_65);
lean_dec(x_46);
x_66 = lean_ctor_get(x_45, 1);
lean_inc(x_66);
lean_dec_ref(x_45);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = lean_nat_dec_le(x_68, x_44);
if (x_69 == 0)
{
uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_44);
x_70 = 0;
x_71 = lean_box(x_70);
x_72 = lean_alloc_closure((void*)(l_Lean_Meta_isDefEqOffset___lam__2___boxed), 6, 1);
lean_closure_set(x_72, 0, x_71);
x_73 = l_Lean_Meta_isDefEqOffset___lam__0(x_1, x_72, x_3, x_4, x_5, x_6, x_66);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_nat_sub(x_44, x_68);
lean_dec(x_68);
lean_dec(x_44);
x_75 = l_Lean_mkNatLit(x_74);
x_23 = x_75;
x_24 = x_67;
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
x_29 = x_66;
goto block_32;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_44);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_76 = !lean_is_exclusive(x_45);
if (x_76 == 0)
{
return x_45;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_45, 0);
x_78 = lean_ctor_get(x_45, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_45);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_21, 0);
lean_inc(x_80);
lean_dec(x_21);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_83 = l_Lean_Meta_isOffset_x3f(x_2, x_3, x_4, x_5, x_6, x_22);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec_ref(x_83);
lean_inc_ref(x_5);
x_86 = l_Lean_Meta_evalNat(x_2, x_3, x_4, x_5, x_6, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_88 = !lean_is_exclusive(x_86);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_86, 0);
lean_dec(x_89);
x_90 = 2;
x_91 = lean_box(x_90);
lean_ctor_set(x_86, 0, x_91);
return x_86;
}
else
{
lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_86, 1);
lean_inc(x_92);
lean_dec(x_86);
x_93 = 2;
x_94 = lean_box(x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_92);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = lean_ctor_get(x_86, 1);
lean_inc(x_96);
lean_dec_ref(x_86);
x_97 = lean_ctor_get(x_87, 0);
lean_inc(x_97);
lean_dec(x_87);
x_98 = lean_nat_dec_le(x_82, x_97);
if (x_98 == 0)
{
uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_97);
lean_dec(x_82);
lean_dec(x_81);
x_99 = 0;
x_100 = lean_box(x_99);
x_101 = lean_alloc_closure((void*)(l_Lean_Meta_isDefEqOffset___lam__2___boxed), 6, 1);
lean_closure_set(x_101, 0, x_100);
x_102 = l_Lean_Meta_isDefEqOffset___lam__0(x_1, x_101, x_3, x_4, x_5, x_6, x_96);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_nat_sub(x_97, x_82);
lean_dec(x_82);
lean_dec(x_97);
x_104 = l_Lean_mkNatLit(x_103);
x_23 = x_81;
x_24 = x_104;
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
x_29 = x_96;
goto block_32;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
lean_dec_ref(x_2);
x_105 = lean_ctor_get(x_84, 0);
lean_inc(x_105);
lean_dec(x_84);
x_106 = lean_ctor_get(x_83, 1);
lean_inc(x_106);
lean_dec_ref(x_83);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_dec(x_105);
x_109 = lean_nat_dec_eq(x_82, x_108);
if (x_109 == 0)
{
uint8_t x_110; 
x_110 = lean_nat_dec_lt(x_82, x_108);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_nat_sub(x_82, x_108);
lean_dec(x_108);
lean_dec(x_82);
lean_inc_ref(x_5);
x_112 = l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(x_81, x_111, x_3, x_4, x_5, x_6, x_106);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec_ref(x_112);
x_23 = x_113;
x_24 = x_107;
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
x_29 = x_114;
goto block_32;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_nat_sub(x_108, x_82);
lean_dec(x_82);
lean_dec(x_108);
lean_inc_ref(x_5);
x_116 = l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(x_107, x_115, x_3, x_4, x_5, x_6, x_106);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec_ref(x_116);
x_23 = x_81;
x_24 = x_117;
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
x_29 = x_118;
goto block_32;
}
}
else
{
lean_dec(x_108);
lean_dec(x_82);
x_23 = x_81;
x_24 = x_107;
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
x_29 = x_106;
goto block_32;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_119 = !lean_is_exclusive(x_83);
if (x_119 == 0)
{
return x_83;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_83, 0);
x_121 = lean_ctor_get(x_83, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_83);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
block_32:
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_alloc_closure((void*)(l_Lean_Meta_isDefEqOffset___lam__1), 7, 2);
lean_closure_set(x_30, 0, x_23);
lean_closure_set(x_30, 1, x_24);
x_31 = l_Lean_Meta_isDefEqOffset___lam__0(x_1, x_30, x_25, x_26, x_27, x_28, x_29);
return x_31;
}
}
else
{
uint8_t x_123; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_123 = !lean_is_exclusive(x_20);
if (x_123 == 0)
{
return x_20;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_20, 0);
x_125 = lean_ctor_get(x_20, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_20);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l_Lean_Meta_isDefEqOffset___lam__2(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
lean_object* initialize_Init_Control_Option(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_LBool(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_SafeExponentiation(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Offset(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Option(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_LBool(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_SafeExponentiation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0 = _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__0);
l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1 = _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__1);
l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2 = _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__2);
l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3 = _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__3);
l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4 = _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__4);
l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5 = _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__5);
l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6 = _init_l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___closed__6);
l_Lean_Meta_evalNat___closed__0 = _init_l_Lean_Meta_evalNat___closed__0();
lean_mark_persistent(l_Lean_Meta_evalNat___closed__0);
l_Lean_Meta_evalNat___closed__1 = _init_l_Lean_Meta_evalNat___closed__1();
lean_mark_persistent(l_Lean_Meta_evalNat___closed__1);
l_Lean_Meta_evalNat___closed__2 = _init_l_Lean_Meta_evalNat___closed__2();
lean_mark_persistent(l_Lean_Meta_evalNat___closed__2);
l_Lean_Meta_evalNat_visit___closed__0 = _init_l_Lean_Meta_evalNat_visit___closed__0();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__0);
l_Lean_Meta_evalNat_visit___closed__1 = _init_l_Lean_Meta_evalNat_visit___closed__1();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__1);
l_Lean_Meta_evalNat_visit___closed__2 = _init_l_Lean_Meta_evalNat_visit___closed__2();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__2);
l_Lean_Meta_evalNat_visit___closed__3 = _init_l_Lean_Meta_evalNat_visit___closed__3();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__3);
l_Lean_Meta_evalNat_visit___closed__4 = _init_l_Lean_Meta_evalNat_visit___closed__4();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__4);
l_Lean_Meta_evalNat_visit___closed__5 = _init_l_Lean_Meta_evalNat_visit___closed__5();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__5);
l_Lean_Meta_evalNat_visit___closed__6 = _init_l_Lean_Meta_evalNat_visit___closed__6();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__6);
l_Lean_Meta_evalNat_visit___closed__7 = _init_l_Lean_Meta_evalNat_visit___closed__7();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__7);
l_Lean_Meta_evalNat_visit___closed__8 = _init_l_Lean_Meta_evalNat_visit___closed__8();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__8);
l_Lean_Meta_evalNat_visit___closed__9 = _init_l_Lean_Meta_evalNat_visit___closed__9();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__9);
l_Lean_Meta_evalNat_visit___closed__10 = _init_l_Lean_Meta_evalNat_visit___closed__10();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__10);
l_Lean_Meta_evalNat_visit___closed__11 = _init_l_Lean_Meta_evalNat_visit___closed__11();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__11);
l_Lean_Meta_evalNat_visit___closed__12 = _init_l_Lean_Meta_evalNat_visit___closed__12();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__12);
l_Lean_Meta_evalNat_visit___closed__13 = _init_l_Lean_Meta_evalNat_visit___closed__13();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__13);
l_Lean_Meta_evalNat_visit___closed__14 = _init_l_Lean_Meta_evalNat_visit___closed__14();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__14);
l_Lean_Meta_evalNat_visit___closed__15 = _init_l_Lean_Meta_evalNat_visit___closed__15();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__15);
l_Lean_Meta_evalNat_visit___closed__16 = _init_l_Lean_Meta_evalNat_visit___closed__16();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__16);
l_Lean_Meta_evalNat_visit___closed__17 = _init_l_Lean_Meta_evalNat_visit___closed__17();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__17);
l_Lean_Meta_evalNat_visit___closed__18 = _init_l_Lean_Meta_evalNat_visit___closed__18();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__18);
l_Lean_Meta_evalNat_visit___closed__19 = _init_l_Lean_Meta_evalNat_visit___closed__19();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__19);
l_Lean_Meta_evalNat_visit___closed__20 = _init_l_Lean_Meta_evalNat_visit___closed__20();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__20);
l_Lean_Meta_evalNat_visit___closed__21 = _init_l_Lean_Meta_evalNat_visit___closed__21();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__21);
l_Lean_Meta_evalNat_visit___closed__22 = _init_l_Lean_Meta_evalNat_visit___closed__22();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__22);
l_Lean_Meta_evalNat_visit___closed__23 = _init_l_Lean_Meta_evalNat_visit___closed__23();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__23);
l_Lean_Meta_evalNat_visit___closed__24 = _init_l_Lean_Meta_evalNat_visit___closed__24();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__24);
l_Lean_Meta_evalNat_visit___closed__25 = _init_l_Lean_Meta_evalNat_visit___closed__25();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__25);
l_Lean_Meta_evalNat_visit___closed__26 = _init_l_Lean_Meta_evalNat_visit___closed__26();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__26);
l_Lean_Meta_evalNat_visit___closed__27 = _init_l_Lean_Meta_evalNat_visit___closed__27();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__27);
l_Lean_Meta_evalNat_visit___closed__28 = _init_l_Lean_Meta_evalNat_visit___closed__28();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__28);
l_Lean_Meta_evalNat_visit___closed__29 = _init_l_Lean_Meta_evalNat_visit___closed__29();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__29);
l_Lean_Meta_evalNat_visit___closed__30 = _init_l_Lean_Meta_evalNat_visit___closed__30();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__30);
l_Lean_Meta_evalNat_visit___closed__31 = _init_l_Lean_Meta_evalNat_visit___closed__31();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__31);
l_Lean_Meta_evalNat_visit___closed__32 = _init_l_Lean_Meta_evalNat_visit___closed__32();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__32);
l_Lean_Meta_evalNat_visit___closed__33 = _init_l_Lean_Meta_evalNat_visit___closed__33();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__33);
l_Lean_Meta_evalNat_visit___closed__34 = _init_l_Lean_Meta_evalNat_visit___closed__34();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__34);
l_Lean_Meta_evalNat_visit___closed__35 = _init_l_Lean_Meta_evalNat_visit___closed__35();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__35);
l_Lean_Meta_evalNat_visit___closed__36 = _init_l_Lean_Meta_evalNat_visit___closed__36();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__36);
l_Lean_Meta_evalNat_visit___closed__37 = _init_l_Lean_Meta_evalNat_visit___closed__37();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__37);
l_Lean_Meta_evalNat_visit___closed__38 = _init_l_Lean_Meta_evalNat_visit___closed__38();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__38);
l_Lean_Meta_evalNat_visit___closed__39 = _init_l_Lean_Meta_evalNat_visit___closed__39();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__39);
l_Lean_Meta_evalNat_visit___closed__40 = _init_l_Lean_Meta_evalNat_visit___closed__40();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__40);
l_Lean_Meta_evalNat_visit___closed__41 = _init_l_Lean_Meta_evalNat_visit___closed__41();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__41);
l_Lean_Meta_evalNat_visit___closed__42 = _init_l_Lean_Meta_evalNat_visit___closed__42();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__42);
l_Lean_Meta_evalNat_visit___closed__43 = _init_l_Lean_Meta_evalNat_visit___closed__43();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__43);
l_Lean_Meta_evalNat_visit___closed__44 = _init_l_Lean_Meta_evalNat_visit___closed__44();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__44);
l_Lean_Meta_evalNat_visit___closed__45 = _init_l_Lean_Meta_evalNat_visit___closed__45();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__45);
l_Lean_Meta_evalNat_visit___closed__46 = _init_l_Lean_Meta_evalNat_visit___closed__46();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__46);
l_Lean_Meta_evalNat_visit___closed__47 = _init_l_Lean_Meta_evalNat_visit___closed__47();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__47);
l_Lean_Meta_evalNat_visit___closed__48 = _init_l_Lean_Meta_evalNat_visit___closed__48();
lean_mark_persistent(l_Lean_Meta_evalNat_visit___closed__48);
l_Lean_Meta_isDefEqOffset___lam__0___closed__0 = _init_l_Lean_Meta_isDefEqOffset___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_isDefEqOffset___lam__0___closed__0);
l_Lean_Meta_isDefEqOffset___lam__0___closed__1 = _init_l_Lean_Meta_isDefEqOffset___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_isDefEqOffset___lam__0___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
