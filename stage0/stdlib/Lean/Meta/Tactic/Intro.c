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
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_intro1Core___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_getIntrosSize(lean_object*);
lean_object* lean_local_ctx_get_unused_name(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tactic_hygienic;
LEAN_EXPORT lean_object* l_Lean_Meta_introN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__4;
lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg___lambda__1___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__12;
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__16;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_intro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLiftReaderT(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLiftReaderT___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__4;
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_introNP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_monadNameGeneratorLift___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_54____spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___closed__2;
lean_object* l_ReaderT_instMonadFunctorReaderT___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_introN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_intro1P(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__3;
extern lean_object* l_Lean_Core_instMonadTraceCoreM;
extern lean_object* l_Lean_Core_instMonadNameGeneratorCoreM;
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__4;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshFVarId___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMetaM;
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__11;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__14;
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__15;
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFVarId;
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__13;
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__2;
lean_object* l_Lean_instMonadTrace___rarg(lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
extern lean_object* l_Lean_Core_instMonadCoreM;
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__3;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_instMonadQuotation___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__17;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__2;
lean_object* l_Lean_Expr_consumeMDataAndTypeAnnotations(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_getIntrosSize___boxed(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_intro1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_introNCore___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlT__1___rarg(lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
uint8_t l_Lean_Expr_isLet(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__7;
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
x_3 = lean_name_mk_string(x_1, x_2);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
lean_dec(x_9);
x_15 = l_Lean_Expr_isForall(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__2;
x_17 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1___closed__5;
x_18 = l_Lean_Meta_throwTacticEx___rarg(x_16, x_2, x_17, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_11);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_3, x_19);
lean_dec(x_3);
x_21 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg(x_2, x_4, x_20, x_5, x_6, x_7, x_8, x_1, x_10, x_11, x_12, x_13, x_14);
return x_21;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("debug", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_instMonadLiftReaderT), 3, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__6() {
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__6;
x_2 = l_Lean_Core_instMonadTraceCoreM;
x_3 = l_Lean_instMonadTrace___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__5;
x_2 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__7;
x_3 = l_Lean_instMonadTrace___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadOptionsCoreM___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__9;
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__10;
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadLiftReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadFunctorReaderT___boxed), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__12;
x_2 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__6;
x_3 = l_Lean_Core_instMonadQuotationCoreM;
x_4 = l_Lean_instMonadQuotation___rarg(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("newType whnf: ", 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__14;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__16;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_inc(x_11);
x_15 = l_Lean_Meta_instantiateMVars(x_1, x_10, x_11, x_12, x_13, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Expr_consumeMDataAndTypeAnnotations(x_16);
x_19 = l_Lean_Expr_isForall(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Expr_isLet(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_21 = lean_whnf(x_18, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__4;
x_52 = lean_st_ref_get(x_13, x_23);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 3);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get_uint8(x_54, sizeof(void*)*1);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_dec(x_52);
x_57 = 0;
x_25 = x_57;
x_26 = x_56;
goto block_51;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_dec(x_52);
x_59 = l_Lean_Meta_instMonadMetaM;
x_60 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__11;
x_61 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___rarg(x_59, x_60, x_24);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_62 = lean_apply_5(x_61, x_10, x_11, x_12, x_13, x_58);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_unbox(x_63);
lean_dec(x_63);
x_25 = x_65;
x_26 = x_64;
goto block_51;
}
else
{
uint8_t x_66; 
lean_dec(x_22);
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
x_66 = !lean_is_exclusive(x_62);
if (x_66 == 0)
{
return x_62;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_62, 0);
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_62);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
block_51:
{
if (x_25 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_9);
x_27 = lean_box(0);
x_28 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27, x_10, x_11, x_12, x_13, x_26);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_29 = lean_alloc_closure((void*)(l_ReaderT_instMonadFunctorReaderT___boxed), 4, 3);
lean_closure_set(x_29, 0, lean_box(0));
lean_closure_set(x_29, 1, lean_box(0));
lean_closure_set(x_29, 2, x_9);
x_30 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__5;
x_31 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__13;
x_32 = l_Lean_instMonadQuotation___rarg(x_29, x_30, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
lean_inc(x_22);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_22);
x_35 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__15;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__17;
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Meta_instMonadMetaM;
x_40 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__8;
x_41 = l_Lean_Meta_instAddMessageContextMetaM;
x_42 = l_Lean_addTrace___rarg(x_39, x_40, x_33, x_41, x_24, x_38);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_43 = lean_apply_5(x_42, x_10, x_11, x_12, x_13, x_26);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__1(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_44, x_10, x_11, x_12, x_13, x_45);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_22);
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
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_43, 0);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_43);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
else
{
uint8_t x_70; 
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
x_70 = !lean_is_exclusive(x_21);
if (x_70 == 0)
{
return x_21;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_21, 0);
x_72 = lean_ctor_get(x_21, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_21);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_9);
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_add(x_3, x_74);
lean_dec(x_3);
x_76 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg(x_2, x_4, x_75, x_5, x_6, x_7, x_8, x_18, x_10, x_11, x_12, x_13, x_17);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_9);
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_add(x_3, x_77);
lean_dec(x_3);
x_79 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg(x_2, x_4, x_78, x_5, x_6, x_7, x_8, x_18, x_10, x_11, x_12, x_13, x_17);
return x_79;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_Meta_getMVarTag(x_1, x_4, x_5, x_6, x_7, x_8);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_assignExprMVar(x_1, x_20, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = l_Lean_Expr_mvarId_x21(x_14);
lean_dec(x_14);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = l_Lean_Expr_mvarId_x21(x_14);
lean_dec(x_14);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_9);
if (x_35 == 0)
{
return x_9;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_9, 0);
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_9);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_instMonadControlT__1___rarg(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__6;
x_2 = l_Lean_Core_instMonadNameGeneratorCoreM;
x_3 = l_Lean_monadNameGeneratorLift___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__5;
x_2 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__3;
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_8, 2);
lean_inc(x_20);
x_21 = lean_ctor_get_uint64(x_8, sizeof(void*)*3);
lean_dec(x_8);
x_22 = lean_array_get_size(x_5);
x_23 = lean_expr_instantiate_rev_range(x_19, x_6, x_22, x_5);
lean_dec(x_22);
lean_dec(x_19);
x_24 = l_Lean_Expr_headBeta(x_23);
x_25 = l_Lean_Meta_instMonadMetaM;
x_26 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__4;
x_27 = l_Lean_mkFreshFVarId___rarg(x_25, x_26);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_28 = lean_apply_5(x_27, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = (uint8_t)((x_21 << 24) >> 61);
x_32 = l_Lean_BinderInfo_isExplicit(x_31);
x_33 = lean_box(x_32);
lean_inc(x_2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_34 = lean_apply_9(x_2, x_4, x_18, x_33, x_7, x_9, x_10, x_11, x_12, x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
lean_inc(x_29);
x_39 = lean_local_ctx_mk_local_decl(x_4, x_29, x_37, x_24, x_31);
x_40 = l_Lean_mkFVar(x_29);
x_41 = lean_array_push(x_5, x_40);
x_3 = x_17;
x_4 = x_39;
x_5 = x_41;
x_7 = x_38;
x_8 = x_20;
x_13 = x_36;
goto _start;
}
else
{
uint8_t x_43; 
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
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
return x_34;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_34, 0);
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_34);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
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
case 8:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_51 = lean_ctor_get(x_8, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_8, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_8, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_8, 3);
lean_inc(x_54);
lean_dec(x_8);
x_55 = lean_array_get_size(x_5);
x_56 = lean_expr_instantiate_rev_range(x_52, x_6, x_55, x_5);
lean_dec(x_52);
x_57 = l_Lean_Expr_headBeta(x_56);
x_58 = lean_expr_instantiate_rev_range(x_53, x_6, x_55, x_5);
lean_dec(x_55);
lean_dec(x_53);
x_59 = l_Lean_Meta_instMonadMetaM;
x_60 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__4;
x_61 = l_Lean_mkFreshFVarId___rarg(x_59, x_60);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_62 = lean_apply_5(x_61, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = 1;
x_66 = lean_box(x_65);
lean_inc(x_2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_67 = lean_apply_9(x_2, x_4, x_51, x_66, x_7, x_9, x_10, x_11, x_12, x_64);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = 0;
lean_inc(x_63);
x_73 = lean_local_ctx_mk_let_decl(x_4, x_63, x_70, x_57, x_58, x_72);
x_74 = l_Lean_mkFVar(x_63);
x_75 = lean_array_push(x_5, x_74);
x_3 = x_17;
x_4 = x_73;
x_5 = x_75;
x_7 = x_71;
x_8 = x_54;
x_13 = x_69;
goto _start;
}
else
{
uint8_t x_77; 
lean_dec(x_63);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_54);
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
x_77 = !lean_is_exclusive(x_67);
if (x_77 == 0)
{
return x_67;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_67, 0);
x_79 = lean_ctor_get(x_67, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_67);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_54);
lean_dec(x_51);
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
x_81 = !lean_is_exclusive(x_62);
if (x_81 == 0)
{
return x_62;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_62, 0);
x_83 = lean_ctor_get(x_62, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_62);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
default: 
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_array_get_size(x_5);
x_86 = lean_expr_instantiate_rev_range(x_8, x_6, x_85, x_5);
lean_dec(x_8);
x_87 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__1;
lean_inc(x_5);
lean_inc(x_4);
x_88 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2), 14, 9);
lean_closure_set(x_88, 0, x_86);
lean_closure_set(x_88, 1, x_1);
lean_closure_set(x_88, 2, x_17);
lean_closure_set(x_88, 3, x_2);
lean_closure_set(x_88, 4, x_4);
lean_closure_set(x_88, 5, x_5);
lean_closure_set(x_88, 6, x_85);
lean_closure_set(x_88, 7, x_7);
lean_closure_set(x_88, 8, x_87);
x_89 = !lean_is_exclusive(x_9);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_9, 1);
lean_dec(x_90);
lean_ctor_set(x_9, 1, x_4);
x_91 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__2;
x_92 = l_Lean_Meta_instMonadMetaM;
x_93 = l_Lean_Meta_withNewLocalInstances___rarg(x_91, x_92, lean_box(0), x_5, x_6, x_88);
x_94 = lean_apply_5(x_93, x_9, x_10, x_11, x_12, x_13);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_95 = lean_ctor_get(x_9, 0);
x_96 = lean_ctor_get(x_9, 2);
x_97 = lean_ctor_get(x_9, 3);
x_98 = lean_ctor_get(x_9, 4);
x_99 = lean_ctor_get(x_9, 5);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_9);
x_100 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_100, 0, x_95);
lean_ctor_set(x_100, 1, x_4);
lean_ctor_set(x_100, 2, x_96);
lean_ctor_set(x_100, 3, x_97);
lean_ctor_set(x_100, 4, x_98);
lean_ctor_set(x_100, 5, x_99);
x_101 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__2;
x_102 = l_Lean_Meta_instMonadMetaM;
x_103 = l_Lean_Meta_withNewLocalInstances___rarg(x_101, x_102, lean_box(0), x_5, x_6, x_88);
x_104 = lean_apply_5(x_103, x_100, x_10, x_11, x_12, x_13);
return x_104;
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_105 = lean_array_get_size(x_5);
x_106 = lean_expr_instantiate_rev_range(x_8, x_6, x_105, x_5);
lean_dec(x_105);
lean_dec(x_8);
lean_inc(x_5);
x_107 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__3___boxed), 8, 3);
lean_closure_set(x_107, 0, x_1);
lean_closure_set(x_107, 1, x_106);
lean_closure_set(x_107, 2, x_5);
x_108 = !lean_is_exclusive(x_9);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_109 = lean_ctor_get(x_9, 1);
lean_dec(x_109);
lean_ctor_set(x_9, 1, x_4);
x_110 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__2;
x_111 = l_Lean_Meta_instMonadMetaM;
x_112 = l_Lean_Meta_withNewLocalInstances___rarg(x_110, x_111, lean_box(0), x_5, x_6, x_107);
x_113 = lean_apply_5(x_112, x_9, x_10, x_11, x_12, x_13);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_114 = lean_ctor_get(x_9, 0);
x_115 = lean_ctor_get(x_9, 2);
x_116 = lean_ctor_get(x_9, 3);
x_117 = lean_ctor_get(x_9, 4);
x_118 = lean_ctor_get(x_9, 5);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_9);
x_119 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_119, 0, x_114);
lean_ctor_set(x_119, 1, x_4);
lean_ctor_set(x_119, 2, x_115);
lean_ctor_set(x_119, 3, x_116);
lean_ctor_set(x_119, 4, x_117);
lean_ctor_set(x_119, 5, x_118);
x_120 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__2;
x_121 = l_Lean_Meta_instMonadMetaM;
x_122 = l_Lean_Meta_withNewLocalInstances___rarg(x_120, x_121, lean_box(0), x_5, x_6, x_107);
x_123 = lean_apply_5(x_122, x_119, x_10, x_11, x_12, x_13);
return x_123;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_9;
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
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_11 = l_Lean_Meta_checkNotAssigned(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_1);
x_13 = l_Lean_Meta_getMVarType(x_1, x_6, x_7, x_8, x_9, x_12);
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
x_12 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_1, x_11, x_5, x_6, x_7, x_8, x_9);
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
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hygienic", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__2;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("make sure tactics are hygienic", 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__1;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__5;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__4;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__6;
x_4 = l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_54____spec__1(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_1 == 0)
{
if (x_2 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_local_ctx_get_unused_name(x_3, x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_3);
x_14 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_4, x_8, x_9, x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_3);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
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
x_3 = lean_name_mk_string(x_1, x_2);
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
static lean_object* _init_l_Lean_Meta_introNCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_tactic_hygienic;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introNCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
x_12 = l_Lean_Meta_introNCore___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Meta_intro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_instInhabitedFVarId;
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_get(x_17, x_16, x_18);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = l_Lean_instInhabitedFVarId;
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_get(x_22, x_20, x_23);
lean_dec(x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_12, 0, x_25);
return x_12;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_30 = x_26;
} else {
 lean_dec_ref(x_26);
 x_30 = lean_box(0);
}
x_31 = l_Lean_instInhabitedFVarId;
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_array_get(x_31, x_28, x_32);
lean_dec(x_28);
if (lean_is_scalar(x_30)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_30;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_27);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_12);
if (x_36 == 0)
{
return x_12;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_12, 0);
x_38 = lean_ctor_get(x_12, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_12);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_instInhabitedFVarId;
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get(x_16, x_15, x_17);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = l_Lean_instInhabitedFVarId;
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get(x_21, x_19, x_22);
lean_dec(x_19);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_11, 0, x_24);
return x_11;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_29 = x_25;
} else {
 lean_dec_ref(x_25);
 x_29 = lean_box(0);
}
x_30 = l_Lean_instInhabitedFVarId;
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_array_get(x_30, x_27, x_31);
lean_dec(x_27);
if (lean_is_scalar(x_29)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_29;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_11);
if (x_35 == 0)
{
return x_11;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_11, 0);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_11);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
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
LEAN_EXPORT lean_object* l_Lean_Meta_intro1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 0;
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
LEAN_EXPORT lean_object* l_Lean_Meta_intros(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_getMVarType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_3);
x_10 = l_Lean_Meta_instantiateMVars(x_8, x_2, x_3, x_4, x_5, x_9);
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
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__1 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__1);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__2 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__2);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__3 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__3);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__4 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__4);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__5 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__5);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__6 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__6);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__7 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__7);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__8 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__8);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__9 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__9);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__10 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__10);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__11 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__11);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__12 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__12);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__13 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__13);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__14 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__14();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__14);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__15 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__15();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__15);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__16 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__16();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__16);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__17 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__17();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___lambda__2___closed__17);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__1 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__1);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__2 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__2);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__3 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__3);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__4 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__4);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___rarg___lambda__1___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778____closed__6);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Intro___hyg_778_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_tactic_hygienic = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_tactic_hygienic);
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___closed__1 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___closed__1);
l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___closed__2 = _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___closed__2);
l_Lean_Meta_introNCore___closed__1 = _init_l_Lean_Meta_introNCore___closed__1();
lean_mark_persistent(l_Lean_Meta_introNCore___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
