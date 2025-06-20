// Lean compiler output
// Module: Lean.Compiler.LCNF.OtherDecl
// Imports: Lean.Compiler.LCNF.BaseTypes Lean.Compiler.LCNF.MonoTypes
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
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0___closed__1;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getOtherDeclType___closed__0;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getOtherDeclType___closed__1;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0___closed__2;
lean_object* l_Lean_Compiler_LCNF_getOtherDeclBaseType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getOtherDeclType___closed__3;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getOtherDeclType___closed__2;
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0___closed__0;
x_8 = l_ReaderT_instMonad___redArg(x_7);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 2);
x_15 = lean_ctor_get(x_10, 3);
x_16 = lean_ctor_get(x_10, 4);
x_17 = lean_ctor_get(x_10, 1);
lean_dec(x_17);
x_18 = l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0___closed__1;
x_19 = l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0___closed__2;
lean_inc(x_13);
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
x_27 = l_Lean_instInhabitedExpr;
x_28 = l_instInhabitedOfMonad___redArg(x_26, x_27);
x_29 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = lean_panic_fn(x_29, x_1);
x_31 = lean_apply_5(x_30, x_2, x_3, x_4, x_5, x_6);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_32 = lean_ctor_get(x_10, 0);
x_33 = lean_ctor_get(x_10, 2);
x_34 = lean_ctor_get(x_10, 3);
x_35 = lean_ctor_get(x_10, 4);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_10);
x_36 = l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0___closed__1;
x_37 = l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0___closed__2;
lean_inc(x_32);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_38, 0, x_32);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_32);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_35);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_42, 0, x_34);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_43, 0, x_33);
x_44 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set(x_44, 3, x_42);
lean_ctor_set(x_44, 4, x_41);
lean_ctor_set(x_8, 1, x_37);
lean_ctor_set(x_8, 0, x_44);
x_45 = l_ReaderT_instMonad___redArg(x_8);
x_46 = l_Lean_instInhabitedExpr;
x_47 = l_instInhabitedOfMonad___redArg(x_45, x_46);
x_48 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_48, 0, x_47);
x_49 = lean_panic_fn(x_48, x_1);
x_50 = lean_apply_5(x_49, x_2, x_3, x_4, x_5, x_6);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_51 = lean_ctor_get(x_8, 0);
lean_inc(x_51);
lean_dec(x_8);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_51, 4);
lean_inc(x_55);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 lean_ctor_release(x_51, 3);
 lean_ctor_release(x_51, 4);
 x_56 = x_51;
} else {
 lean_dec_ref(x_51);
 x_56 = lean_box(0);
}
x_57 = l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0___closed__1;
x_58 = l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0___closed__2;
lean_inc(x_52);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_59, 0, x_52);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_60, 0, x_52);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_62, 0, x_55);
x_63 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_63, 0, x_54);
x_64 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_64, 0, x_53);
if (lean_is_scalar(x_56)) {
 x_65 = lean_alloc_ctor(0, 5, 0);
} else {
 x_65 = x_56;
}
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_57);
lean_ctor_set(x_65, 2, x_64);
lean_ctor_set(x_65, 3, x_63);
lean_ctor_set(x_65, 4, x_62);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_58);
x_67 = l_ReaderT_instMonad___redArg(x_66);
x_68 = l_Lean_instInhabitedExpr;
x_69 = l_instInhabitedOfMonad___redArg(x_67, x_68);
x_70 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_70, 0, x_69);
x_71 = lean_panic_fn(x_70, x_1);
x_72 = lean_apply_5(x_71, x_2, x_3, x_4, x_5, x_6);
return x_72;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getOtherDeclType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.OtherDecl", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getOtherDeclType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.getOtherDeclType", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getOtherDeclType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getOtherDeclType___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_getOtherDeclType___closed__2;
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(19u);
x_4 = l_Lean_Compiler_LCNF_getOtherDeclType___closed__1;
x_5 = l_Lean_Compiler_LCNF_getOtherDeclType___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Compiler_LCNF_getPhase___redArg(x_3, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
switch (x_10) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_Compiler_LCNF_getOtherDeclBaseType(x_1, x_2, x_5, x_6, x_11);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Lean_Compiler_LCNF_getOtherDeclMonoType(x_1, x_5, x_6, x_13);
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = l_Lean_Compiler_LCNF_getOtherDeclType___closed__3;
x_17 = l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0(x_16, x_3, x_4, x_5, x_6, x_15);
return x_17;
}
}
}
}
lean_object* initialize_Lean_Compiler_LCNF_BaseTypes(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_OtherDecl(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_BaseTypes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_MonoTypes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0___closed__0 = _init_l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0___closed__0();
lean_mark_persistent(l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0___closed__0);
l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0___closed__1 = _init_l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0___closed__1();
lean_mark_persistent(l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0___closed__1);
l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0___closed__2 = _init_l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0___closed__2();
lean_mark_persistent(l_panic___at___Lean_Compiler_LCNF_getOtherDeclType_spec__0___closed__2);
l_Lean_Compiler_LCNF_getOtherDeclType___closed__0 = _init_l_Lean_Compiler_LCNF_getOtherDeclType___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_getOtherDeclType___closed__0);
l_Lean_Compiler_LCNF_getOtherDeclType___closed__1 = _init_l_Lean_Compiler_LCNF_getOtherDeclType___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_getOtherDeclType___closed__1);
l_Lean_Compiler_LCNF_getOtherDeclType___closed__2 = _init_l_Lean_Compiler_LCNF_getOtherDeclType___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_getOtherDeclType___closed__2);
l_Lean_Compiler_LCNF_getOtherDeclType___closed__3 = _init_l_Lean_Compiler_LCNF_getOtherDeclType___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_getOtherDeclType___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
