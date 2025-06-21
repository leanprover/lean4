// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.Preprocess
// Imports: Lean.Meta.Transform Lean.Elab.RecAppSyntax
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
static lean_object* l_Lean_Elab_Structural_preprocess___lam__1___closed__4;
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Structural_preprocess_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_preprocess___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___lam__0(uint8_t, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Elab_Structural_preprocess_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_preprocess___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_preprocess___lam__0___closed__0;
uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*, uint8_t);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
static lean_object* l_Lean_Elab_Structural_preprocess___lam__1___closed__2;
lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_preprocess___lam__1___closed__3;
static lean_object* l_Lean_Elab_Structural_preprocess___lam__1___closed__0;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_preprocess___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at___Lean_registerInternalExceptionId_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at___Lean_Core_betaReduce_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_preprocess___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
uint8_t l_Lean_Expr_isMData(lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
uint8_t l_Lean_MData_isRecApp(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_isConst(x_3);
if (x_4 == 0)
{
return x_1;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Expr_constName_x21(x_3);
x_6 = l_Array_contains___at___Lean_registerInternalExceptionId_spec__0(x_2, x_5);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Expr_isHeadBetaTarget(x_1, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = lean_unbox(x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___lam__0___boxed), 3, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_2);
x_8 = l_Lean_Expr_getAppFn(x_1);
x_9 = lean_find_expr(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = lean_unbox(x_3);
return x_10;
}
else
{
lean_dec(x_9);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___lam__0(x_4, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_panic___at___Lean_Elab_Structural_preprocess_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instInhabitedCoreM___lam__0___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Structural_preprocess_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_panic___at___Lean_Elab_Structural_preprocess_spec__0___closed__0;
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_3(x_6, x_2, x_3, x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Structural_preprocess___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_preprocess___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l___private_Lean_Elab_PreDefinition_Structural_Preprocess_0__Lean_Elab_Structural_shouldBetaReduce(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = l_Lean_Elab_Structural_preprocess___lam__0___closed__0;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Expr_headBeta(x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Elab_Structural_preprocess___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Structural_preprocess___lam__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.PreDefinition.Structural.Preprocess", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_preprocess___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Structural.preprocess", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_preprocess___lam__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_preprocess___lam__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Structural_preprocess___lam__1___closed__3;
x_2 = lean_unsigned_to_nat(39u);
x_3 = lean_unsigned_to_nat(47u);
x_4 = l_Lean_Elab_Structural_preprocess___lam__1___closed__2;
x_5 = l_Lean_Elab_Structural_preprocess___lam__1___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_preprocess___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_9; uint8_t x_32; 
x_32 = l_Lean_Expr_isApp(x_1);
if (x_32 == 0)
{
x_9 = x_32;
goto block_31;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Expr_getAppFn(x_1);
x_34 = l_Lean_Expr_isMData(x_33);
lean_dec(x_33);
x_9 = x_34;
goto block_31;
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Elab_Structural_preprocess___lam__0___closed__0;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
block_31:
{
if (x_9 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = x_4;
goto block_8;
}
else
{
lean_object* x_10; 
x_10 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_10) == 10)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_MData_isRecApp(x_11);
if (x_13 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_5 = x_4;
goto block_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = l_Lean_Elab_Structural_preprocess___lam__1___closed__0;
x_15 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_15);
x_16 = lean_mk_array(x_15, x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_15, x_17);
lean_dec(x_15);
x_19 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_16, x_18);
x_20 = l_Lean_Expr_beta(x_12, x_19);
x_21 = l_Lean_Expr_mdata___override(x_11, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_4);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_1);
x_24 = l_Lean_Elab_Structural_preprocess___lam__1___closed__4;
x_25 = l_panic___at___Lean_Elab_Structural_preprocess_spec__0(x_24, x_2, x_3, x_4);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_5 = x_26;
goto block_8;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_25);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_preprocess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_preprocess___lam__0___boxed), 5, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_preprocess___lam__1), 4, 0);
x_8 = l_Lean_Core_transform___at___Lean_Core_betaReduce_spec__0(x_1, x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_preprocess___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Structural_preprocess___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_RecAppSyntax(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_Structural_Preprocess(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Transform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_RecAppSyntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_panic___at___Lean_Elab_Structural_preprocess_spec__0___closed__0 = _init_l_panic___at___Lean_Elab_Structural_preprocess_spec__0___closed__0();
lean_mark_persistent(l_panic___at___Lean_Elab_Structural_preprocess_spec__0___closed__0);
l_Lean_Elab_Structural_preprocess___lam__0___closed__0 = _init_l_Lean_Elab_Structural_preprocess___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Structural_preprocess___lam__0___closed__0);
l_Lean_Elab_Structural_preprocess___lam__1___closed__0 = _init_l_Lean_Elab_Structural_preprocess___lam__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Structural_preprocess___lam__1___closed__0);
l_Lean_Elab_Structural_preprocess___lam__1___closed__1 = _init_l_Lean_Elab_Structural_preprocess___lam__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Structural_preprocess___lam__1___closed__1);
l_Lean_Elab_Structural_preprocess___lam__1___closed__2 = _init_l_Lean_Elab_Structural_preprocess___lam__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Structural_preprocess___lam__1___closed__2);
l_Lean_Elab_Structural_preprocess___lam__1___closed__3 = _init_l_Lean_Elab_Structural_preprocess___lam__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Structural_preprocess___lam__1___closed__3);
l_Lean_Elab_Structural_preprocess___lam__1___closed__4 = _init_l_Lean_Elab_Structural_preprocess___lam__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Structural_preprocess___lam__1___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
