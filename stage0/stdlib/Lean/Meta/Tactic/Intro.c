// Lean compiler output
// Module: Lean.Meta.Tactic.Intro
// Imports: Init Lean.Meta.Tactic.Util
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
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_intro1Core___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_getIntrosSize(lean_object*);
lean_object* lean_local_ctx_get_unused_name(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_tactic_hygienic;
LEAN_EXPORT lean_object* l_Lean_Meta_introN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__4;
lean_object* l_Lean_MVarId_assign___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1P(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg___lambda__1___closed__1;
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_introN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_intro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLiftReaderT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__4;
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_introNP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_introN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_monadNameGeneratorLift___rarg(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
static lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___closed__2;
static lean_object* l_Lean_MVarId_intro___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_introN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_intro1P(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__3;
extern lean_object* l_Lean_Core_instMonadNameGeneratorCoreM;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_introNP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeReaderT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshFVarId___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMetaM;
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_intro___closed__4;
LEAN_EXPORT lean_object* l_Lean_MVarId_intro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__3;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_intro___closed__1;
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_59____spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMCtxMetaM;
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
extern lean_object* l_Lean_Core_instMonadCoreM;
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__3;
static lean_object* l_Lean_MVarId_intro___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1(size_t, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_getIntrosSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_intro1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__5;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__1;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__2;
lean_object* l_panic___at_Lean_Expr_fvarId_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlT__1___rarg(lean_object*);
uint8_t l_Lean_Expr_isLet(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__5;
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("introN", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("insufficient number of binders", 30);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_Meta_instMonadMetaM;
x_15 = l_Lean_Meta_instMonadMCtxMetaM;
x_16 = l_Lean_instantiateMVars___rarg(x_14, x_15, x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_17 = lean_apply_5(x_16, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Expr_cleanupAnnotations(x_18);
x_21 = l_Lean_Expr_isForall(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Expr_isLet(x_20);
if (x_22 == 0)
{
lean_object* x_23; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_23 = lean_whnf(x_20, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Expr_isForall(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__2;
x_28 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__5;
x_29 = l_Lean_Meta_throwTacticEx___rarg(x_27, x_2, x_28, x_9, x_10, x_11, x_12, x_25);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_3, x_30);
lean_dec(x_3);
x_32 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg(x_2, x_4, x_31, x_5, x_6, x_7, x_8, x_24, x_9, x_10, x_11, x_12, x_25);
return x_32;
}
}
else
{
uint8_t x_33; 
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
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_3, x_37);
lean_dec(x_3);
x_39 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg(x_2, x_4, x_38, x_5, x_6, x_7, x_8, x_20, x_9, x_10, x_11, x_12, x_19);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_3, x_40);
lean_dec(x_3);
x_42 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg(x_2, x_4, x_41, x_5, x_6, x_7, x_8, x_20, x_9, x_10, x_11, x_12, x_19);
return x_42;
}
}
else
{
uint8_t x_43; 
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
x_43 = !lean_is_exclusive(x_17);
if (x_43 == 0)
{
return x_17;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_17, 0);
x_45 = lean_ctor_get(x_17, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_17);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_headBeta(x_2);
lean_inc(x_4);
x_13 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_12, x_10, x_4, x_5, x_6, x_7, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 0;
x_17 = 1;
x_18 = 1;
lean_inc(x_14);
lean_inc(x_3);
x_19 = l_Lean_Meta_mkLambdaFVars(x_3, x_14, x_16, x_17, x_18, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_instMonadMCtxMetaM;
x_23 = l_Lean_MVarId_assign___rarg(x_22, x_1, x_20);
x_24 = lean_apply_5(x_23, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = l_Lean_Expr_mvarId_x21(x_14);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_3);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = l_Lean_Expr_mvarId_x21(x_14);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_14);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
return x_24;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_ctor_get(x_24, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_24);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_19);
if (x_37 == 0)
{
return x_19;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_19, 0);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_19);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_9);
if (x_41 == 0)
{
return x_9;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_9, 0);
x_43 = lean_ctor_get(x_9, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_9);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__1;
x_2 = l_ReaderT_instApplicativeReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__2;
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_instMonadControlT__1___rarg(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_instMonadLiftReaderT), 3, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__5() {
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__5;
x_2 = l_Lean_Core_instMonadNameGeneratorCoreM;
x_3 = l_Lean_monadNameGeneratorLift___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__4;
x_2 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__6;
x_3 = l_Lean_monadNameGeneratorLift___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_3, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_3, x_16);
lean_dec(x_3);
switch (lean_obj_tag(x_8)) {
case 7:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_8, 2);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_22 = lean_array_get_size(x_5);
x_23 = lean_expr_instantiate_rev_range(x_19, x_6, x_22, x_5);
lean_dec(x_22);
lean_dec(x_19);
x_24 = l_Lean_Expr_headBeta(x_23);
x_25 = l_Lean_Meta_instMonadMetaM;
x_26 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__7;
x_27 = l_Lean_mkFreshFVarId___rarg(x_25, x_26);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_28 = lean_apply_5(x_27, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_BinderInfo_isExplicit(x_21);
x_32 = lean_box(x_31);
lean_inc(x_2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_33 = lean_apply_9(x_2, x_4, x_18, x_32, x_7, x_9, x_10, x_11, x_12, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
lean_inc(x_29);
x_38 = lean_local_ctx_mk_local_decl(x_4, x_29, x_36, x_24, x_21);
x_39 = l_Lean_Expr_fvar___override(x_29);
x_40 = lean_array_push(x_5, x_39);
x_3 = x_17;
x_4 = x_38;
x_5 = x_40;
x_7 = x_37;
x_8 = x_20;
x_13 = x_35;
goto _start;
}
else
{
uint8_t x_42; 
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_33);
if (x_42 == 0)
{
return x_33;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_33, 0);
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_33);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_28);
if (x_46 == 0)
{
return x_28;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_28, 0);
x_48 = lean_ctor_get(x_28, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_28);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
case 8:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_50 = lean_ctor_get(x_8, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_8, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_8, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_8, 3);
lean_inc(x_53);
lean_dec(x_8);
x_54 = lean_array_get_size(x_5);
x_55 = lean_expr_instantiate_rev_range(x_51, x_6, x_54, x_5);
lean_dec(x_51);
x_56 = l_Lean_Expr_headBeta(x_55);
x_57 = lean_expr_instantiate_rev_range(x_52, x_6, x_54, x_5);
lean_dec(x_54);
lean_dec(x_52);
x_58 = l_Lean_Meta_instMonadMetaM;
x_59 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__7;
x_60 = l_Lean_mkFreshFVarId___rarg(x_58, x_59);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_61 = lean_apply_5(x_60, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = 1;
x_65 = lean_box(x_64);
lean_inc(x_2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_66 = lean_apply_9(x_2, x_4, x_50, x_65, x_7, x_9, x_10, x_11, x_12, x_63);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = 0;
lean_inc(x_62);
x_72 = lean_local_ctx_mk_let_decl(x_4, x_62, x_69, x_56, x_57, x_71);
x_73 = l_Lean_Expr_fvar___override(x_62);
x_74 = lean_array_push(x_5, x_73);
x_3 = x_17;
x_4 = x_72;
x_5 = x_74;
x_7 = x_70;
x_8 = x_53;
x_13 = x_68;
goto _start;
}
else
{
uint8_t x_76; 
lean_dec(x_62);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_66);
if (x_76 == 0)
{
return x_66;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_66, 0);
x_78 = lean_ctor_get(x_66, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_66);
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
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_61);
if (x_80 == 0)
{
return x_61;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_61, 0);
x_82 = lean_ctor_get(x_61, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_61);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
default: 
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_84 = lean_array_get_size(x_5);
x_85 = lean_expr_instantiate_rev_range(x_8, x_6, x_84, x_5);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
x_86 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1), 13, 8);
lean_closure_set(x_86, 0, x_85);
lean_closure_set(x_86, 1, x_1);
lean_closure_set(x_86, 2, x_17);
lean_closure_set(x_86, 3, x_2);
lean_closure_set(x_86, 4, x_4);
lean_closure_set(x_86, 5, x_5);
lean_closure_set(x_86, 6, x_84);
lean_closure_set(x_86, 7, x_7);
x_87 = lean_ctor_get(x_9, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_9, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_9, 3);
lean_inc(x_89);
x_90 = lean_ctor_get(x_9, 4);
lean_inc(x_90);
x_91 = lean_ctor_get(x_9, 5);
lean_inc(x_91);
lean_dec(x_9);
x_92 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_92, 0, x_87);
lean_ctor_set(x_92, 1, x_4);
lean_ctor_set(x_92, 2, x_88);
lean_ctor_set(x_92, 3, x_89);
lean_ctor_set(x_92, 4, x_90);
lean_ctor_set(x_92, 5, x_91);
x_93 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__3;
x_94 = l_Lean_Meta_instMonadMetaM;
x_95 = l_Lean_Meta_withNewLocalInstances___rarg(x_93, x_94, lean_box(0), x_5, x_6, x_86);
x_96 = lean_apply_5(x_95, x_92, x_10, x_11, x_12, x_13);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_97 = lean_array_get_size(x_5);
x_98 = lean_expr_instantiate_rev_range(x_8, x_6, x_97, x_5);
lean_dec(x_97);
lean_dec(x_8);
lean_inc(x_5);
x_99 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2), 8, 3);
lean_closure_set(x_99, 0, x_1);
lean_closure_set(x_99, 1, x_98);
lean_closure_set(x_99, 2, x_5);
x_100 = !lean_is_exclusive(x_9);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_9, 1);
lean_dec(x_101);
lean_ctor_set(x_9, 1, x_4);
x_102 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__3;
x_103 = l_Lean_Meta_instMonadMetaM;
x_104 = l_Lean_Meta_withNewLocalInstances___rarg(x_102, x_103, lean_box(0), x_5, x_6, x_99);
x_105 = lean_apply_5(x_104, x_9, x_10, x_11, x_12, x_13);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_106 = lean_ctor_get(x_9, 0);
x_107 = lean_ctor_get(x_9, 2);
x_108 = lean_ctor_get(x_9, 3);
x_109 = lean_ctor_get(x_9, 4);
x_110 = lean_ctor_get(x_9, 5);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_9);
x_111 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_111, 0, x_106);
lean_ctor_set(x_111, 1, x_4);
lean_ctor_set(x_111, 2, x_107);
lean_ctor_set(x_111, 3, x_108);
lean_ctor_set(x_111, 4, x_109);
lean_ctor_set(x_111, 5, x_110);
x_112 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__3;
x_113 = l_Lean_Meta_instMonadMetaM;
x_114 = l_Lean_Meta_withNewLocalInstances___rarg(x_112, x_113, lean_box(0), x_5, x_6, x_99);
x_115 = lean_apply_5(x_114, x_111, x_10, x_11, x_12, x_13);
return x_115;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg), 13, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l_Lean_Expr_fvarId_x21(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_11 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_1);
x_13 = l_Lean_MVarId_getType(x_1, x_6, x_7, x_8, x_9, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
x_17 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg___lambda__1___closed__1;
x_18 = lean_unsigned_to_nat(0u);
x_19 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop(lean_box(0));
x_20 = lean_apply_13(x_19, x_1, x_3, x_4, x_16, x_17, x_18, x_5, x_14, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_array_get_size(x_24);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = 0;
x_28 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1(x_26, x_27, x_24);
lean_ctor_set(x_22, 0, x_28);
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
x_31 = lean_array_get_size(x_29);
x_32 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_33 = 0;
x_34 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1(x_32, x_33, x_29);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_20, 0, x_35);
return x_20;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_20);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_40 = x_36;
} else {
 lean_dec_ref(x_36);
 x_40 = lean_box(0);
}
x_41 = lean_array_get_size(x_38);
x_42 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_43 = 0;
x_44 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1(x_42, x_43, x_38);
if (lean_is_scalar(x_40)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_40;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_39);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_37);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_20);
if (x_47 == 0)
{
return x_20;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_20, 0);
x_49 = lean_ctor_get(x_20, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_20);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
return x_13;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_13, 0);
x_53 = lean_ctor_get(x_13, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_13);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_11);
if (x_55 == 0)
{
return x_11;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_11, 0);
x_57 = lean_ctor_get(x_11, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_11);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__2;
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg___lambda__1), 10, 5);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_2);
lean_closure_set(x_11, 4, x_4);
x_12 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hygienic", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__2;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("make sure tactics are hygienic", 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__1;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__5;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__4;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__6;
x_4 = l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_59____spec__1(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_3 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_local_ctx_get_unused_name(x_1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_2, x_6, x_7, x_8);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_mkFreshBinderNameForTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_tactic_hygienic;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 2);
x_9 = l_Lean_Meta_mkFreshBinderNameForTactic___closed__1;
x_10 = l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(x_8, x_9);
x_11 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore(x_7, x_1, x_10, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_mkFreshBinderNameForTactic(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_1 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore(x_3, x_4, x_2, x_6, x_7, x_8, x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_10);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(x_1, x_2, x_4, x_5, x_13, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
else
{
if (x_3 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___closed__2;
x_18 = lean_name_eq(x_15, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
lean_dec(x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_15);
x_21 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(x_1, x_2, x_4, x_5, x_16, x_8, x_9, x_10, x_11, x_12);
return x_21;
}
}
else
{
if (x_6 == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(x_1, x_2, x_4, x_5, x_7, x_8, x_9, x_10, x_11, x_12);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(x_1, x_2, x_4, x_5, x_26, x_8, x_9, x_10, x_11, x_12);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_7, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
lean_dec(x_7);
x_30 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___closed__2;
x_31 = lean_name_eq(x_28, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_5);
lean_dec(x_4);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_12);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_28);
x_34 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(x_1, x_2, x_4, x_5, x_29, x_8, x_9, x_10, x_11, x_12);
return x_34;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = lean_unbox(x_6);
lean_dec(x_6);
x_17 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(x_13, x_14, x_15, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
x_12 = l_Lean_Meta_mkFreshBinderNameForTactic___closed__1;
x_13 = l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(x_11, x_12);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_box(x_5);
x_17 = lean_box(x_13);
x_18 = lean_box(x_4);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___boxed), 12, 3);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_17);
lean_closure_set(x_19, 2, x_18);
x_20 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp(lean_box(0));
x_21 = lean_apply_9(x_20, x_1, x_2, x_19, x_3, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_22 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg___lambda__1___closed__1;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_10);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Meta_introNCore(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introN(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
x_11 = l_Lean_Meta_introNCore(x_1, x_2, x_3, x_4, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introN___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_MVarId_introN(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introN(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
x_11 = l_Lean_Meta_introNCore(x_1, x_2, x_3, x_4, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introN___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_introN(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_introNP(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_box(0);
x_9 = 0;
x_10 = 1;
x_11 = l_Lean_Meta_introNCore(x_1, x_2, x_8, x_9, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNP(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_box(0);
x_9 = 0;
x_10 = 1;
x_11 = l_Lean_Meta_introNCore(x_1, x_2, x_8, x_9, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
static lean_object* _init_l_Lean_MVarId_intro___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Util", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_intro___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("getElem!", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_intro___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index out of bounds", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_intro___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_MVarId_intro___closed__1;
x_2 = l_Lean_MVarId_intro___closed__2;
x_3 = lean_unsigned_to_nat(77u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l_Lean_MVarId_intro___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = 0;
x_12 = l_Lean_Meta_introNCore(x_1, x_10, x_9, x_11, x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_array_get_size(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_lt(x_18, x_17);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_16);
x_20 = l_Lean_MVarId_intro___closed__4;
x_21 = l_panic___at_Lean_Expr_fvarId_x21___spec__1(x_20);
lean_ctor_set(x_14, 0, x_21);
return x_12;
}
else
{
lean_object* x_22; 
x_22 = lean_array_fget(x_16, x_18);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_22);
return x_12;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_array_get_size(x_23);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_lt(x_26, x_25);
lean_dec(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_23);
x_28 = l_Lean_MVarId_intro___closed__4;
x_29 = l_panic___at_Lean_Expr_fvarId_x21___spec__1(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_12, 0, x_30);
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_array_fget(x_23, x_26);
lean_dec(x_23);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_12, 0, x_32);
return x_12;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_33 = lean_ctor_get(x_12, 0);
x_34 = lean_ctor_get(x_12, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_12);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_37 = x_33;
} else {
 lean_dec_ref(x_33);
 x_37 = lean_box(0);
}
x_38 = lean_array_get_size(x_35);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_nat_dec_lt(x_39, x_38);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_35);
x_41 = l_Lean_MVarId_intro___closed__4;
x_42 = l_panic___at_Lean_Expr_fvarId_x21___spec__1(x_41);
if (lean_is_scalar(x_37)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_37;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_34);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_array_fget(x_35, x_39);
lean_dec(x_35);
if (lean_is_scalar(x_37)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_37;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_36);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_34);
return x_47;
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_12);
if (x_48 == 0)
{
return x_12;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_12, 0);
x_50 = lean_ctor_get(x_12, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_12);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_intro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_intro(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_intro1Core(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_box(0);
x_9 = lean_unsigned_to_nat(1u);
x_10 = 0;
x_11 = l_Lean_Meta_introNCore(x_1, x_9, x_8, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_array_get_size(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_16);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
x_19 = l_Lean_MVarId_intro___closed__4;
x_20 = l_panic___at_Lean_Expr_fvarId_x21___spec__1(x_19);
lean_ctor_set(x_13, 0, x_20);
return x_11;
}
else
{
lean_object* x_21; 
x_21 = lean_array_fget(x_15, x_17);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_21);
return x_11;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_array_get_size(x_22);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_lt(x_25, x_24);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_22);
x_27 = l_Lean_MVarId_intro___closed__4;
x_28 = l_panic___at_Lean_Expr_fvarId_x21___spec__1(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
lean_ctor_set(x_11, 0, x_29);
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_array_fget(x_22, x_25);
lean_dec(x_22);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_11, 0, x_31);
return x_11;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_32 = lean_ctor_get(x_11, 0);
x_33 = lean_ctor_get(x_11, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_11);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_36 = x_32;
} else {
 lean_dec_ref(x_32);
 x_36 = lean_box(0);
}
x_37 = lean_array_get_size(x_34);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_lt(x_38, x_37);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_34);
x_40 = l_Lean_MVarId_intro___closed__4;
x_41 = l_panic___at_Lean_Expr_fvarId_x21___spec__1(x_40);
if (lean_is_scalar(x_36)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_36;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_33);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_array_fget(x_34, x_38);
lean_dec(x_34);
if (lean_is_scalar(x_36)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_36;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_35);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_33);
return x_46;
}
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_11);
if (x_47 == 0)
{
return x_11;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_11, 0);
x_49 = lean_ctor_get(x_11, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_11);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_intro1Core___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_intro1Core(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 0;
x_8 = l_Lean_Meta_intro1Core(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_intro1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 0;
x_8 = l_Lean_Meta_intro1Core(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intro1P(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
x_8 = l_Lean_Meta_intro1Core(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_intro1P(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
x_8 = l_Lean_Meta_intro1Core(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_getIntrosSize(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 7:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_getIntrosSize(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
return x_5;
}
case 8:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 3);
x_7 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_getIntrosSize(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_7);
return x_9;
}
case 10:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 1);
x_1 = x_10;
goto _start;
}
default: 
{
lean_object* x_12; 
x_12 = lean_unsigned_to_nat(0u);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_getIntrosSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_getIntrosSize(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_intros(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_8, x_2, x_3, x_4, x_5, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_getIntrosSize(x_12);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
lean_free_object(x_10);
x_17 = lean_box(0);
x_18 = 0;
x_19 = l_Lean_Meta_introNCore(x_1, x_14, x_17, x_18, x_18, x_2, x_3, x_4, x_5, x_13);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg___lambda__1___closed__1;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_24 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_getIntrosSize(x_22);
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_eq(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_box(0);
x_28 = 0;
x_29 = l_Lean_Meta_introNCore(x_1, x_24, x_27, x_28, x_28, x_2, x_3, x_4, x_5, x_23);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg___lambda__1___closed__1;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_23);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_7);
if (x_33 == 0)
{
return x_7;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_7, 0);
x_35 = lean_ctor_get(x_7, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_7);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_intros(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_intros(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__2 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__2);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__3 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__3);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__4 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__4);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__5 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__5);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__1 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__1);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__2 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__2);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__3 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__3);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__4 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__4);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__5 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__5);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__6 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__6);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__7 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__7);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg___lambda__1___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737____closed__6);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_737_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_tactic_hygienic = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_tactic_hygienic);
lean_dec_ref(res);
}l_Lean_Meta_mkFreshBinderNameForTactic___closed__1 = _init_l_Lean_Meta_mkFreshBinderNameForTactic___closed__1();
lean_mark_persistent(l_Lean_Meta_mkFreshBinderNameForTactic___closed__1);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___closed__1 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___closed__1);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___closed__2 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___closed__2);
l_Lean_MVarId_intro___closed__1 = _init_l_Lean_MVarId_intro___closed__1();
lean_mark_persistent(l_Lean_MVarId_intro___closed__1);
l_Lean_MVarId_intro___closed__2 = _init_l_Lean_MVarId_intro___closed__2();
lean_mark_persistent(l_Lean_MVarId_intro___closed__2);
l_Lean_MVarId_intro___closed__3 = _init_l_Lean_MVarId_intro___closed__3();
lean_mark_persistent(l_Lean_MVarId_intro___closed__3);
l_Lean_MVarId_intro___closed__4 = _init_l_Lean_MVarId_intro___closed__4();
lean_mark_persistent(l_Lean_MVarId_intro___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
