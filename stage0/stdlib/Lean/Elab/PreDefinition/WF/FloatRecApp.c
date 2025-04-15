// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.FloatRecApp
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
static lean_object* l_Lean_Elab_WF_floatRecApp___closed__1;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_floatRecApp___lambda__2___closed__4;
static lean_object* l_panic___at_Lean_Elab_WF_floatRecApp___spec__1___closed__1;
static lean_object* l_Lean_Elab_WF_floatRecApp___closed__2;
static lean_object* l_Lean_Elab_WF_floatRecApp___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_WF_floatRecApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_floatRecApp___lambda__2___closed__5;
extern lean_object* l_Lean_levelZero;
static lean_object* l_Lean_Elab_WF_floatRecApp___lambda__2___closed__3;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_floatRecApp___lambda__2___closed__1;
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
extern lean_object* l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMData(lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
uint8_t l_Lean_KVMap_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_floatRecApp___lambda__2___closed__2;
static lean_object* _init_l_panic___at_Lean_Elab_WF_floatRecApp___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instInhabitedCoreM___boxed), 3, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_WF_floatRecApp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_panic___at_Lean_Elab_WF_floatRecApp___spec__1___closed__1;
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_3(x_6, x_2, x_3, x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_WF_floatRecApp___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_WF_floatRecApp___lambda__1___closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_WF_floatRecApp___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.PreDefinition.WF.FloatRecApp", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_floatRecApp___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.WF.floatRecApp", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_floatRecApp___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_floatRecApp___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_WF_floatRecApp___lambda__2___closed__1;
x_2 = l_Lean_Elab_WF_floatRecApp___lambda__2___closed__2;
x_3 = lean_unsigned_to_nat(31u);
x_4 = lean_unsigned_to_nat(39u);
x_5 = l_Lean_Elab_WF_floatRecApp___lambda__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_WF_floatRecApp___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Expr_isApp(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Lean_Elab_WF_floatRecApp___lambda__1___closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Expr_getAppFn(x_1);
x_9 = l_Lean_Expr_isMData(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = l_Lean_Elab_WF_floatRecApp___lambda__1___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
if (lean_obj_tag(x_8) == 10)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l___private_Lean_Elab_RecAppSyntax_0__Lean_recAppKey;
x_15 = l_Lean_KVMap_contains(x_12, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
x_16 = l_Lean_Elab_WF_floatRecApp___lambda__1___closed__1;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_18);
x_20 = l_Lean_Elab_WF_floatRecApp___lambda__2___closed__5;
lean_inc(x_19);
x_21 = lean_mk_array(x_19, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_19, x_22);
lean_dec(x_19);
x_24 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_21, x_23);
x_25 = l_Lean_Expr_beta(x_13, x_24);
x_26 = l_Lean_Expr_mdata___override(x_12, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_8);
lean_dec(x_1);
x_29 = l_Lean_Elab_WF_floatRecApp___lambda__2___closed__4;
x_30 = l_panic___at_Lean_Elab_WF_floatRecApp___spec__1(x_29, x_2, x_3, x_4);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = l_Lean_Elab_WF_floatRecApp___lambda__1___closed__1;
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = l_Lean_Elab_WF_floatRecApp___lambda__1___closed__1;
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
return x_30;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_30, 0);
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_30);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_WF_floatRecApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_WF_floatRecApp___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_floatRecApp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_WF_floatRecApp___lambda__2), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Elab_WF_floatRecApp___closed__1;
x_6 = l_Lean_Elab_WF_floatRecApp___closed__2;
x_7 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_1, x_5, x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_WF_floatRecApp___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_RecAppSyntax(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Transform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_RecAppSyntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_panic___at_Lean_Elab_WF_floatRecApp___spec__1___closed__1 = _init_l_panic___at_Lean_Elab_WF_floatRecApp___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Elab_WF_floatRecApp___spec__1___closed__1);
l_Lean_Elab_WF_floatRecApp___lambda__1___closed__1 = _init_l_Lean_Elab_WF_floatRecApp___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_floatRecApp___lambda__1___closed__1);
l_Lean_Elab_WF_floatRecApp___lambda__2___closed__1 = _init_l_Lean_Elab_WF_floatRecApp___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_floatRecApp___lambda__2___closed__1);
l_Lean_Elab_WF_floatRecApp___lambda__2___closed__2 = _init_l_Lean_Elab_WF_floatRecApp___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_floatRecApp___lambda__2___closed__2);
l_Lean_Elab_WF_floatRecApp___lambda__2___closed__3 = _init_l_Lean_Elab_WF_floatRecApp___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_floatRecApp___lambda__2___closed__3);
l_Lean_Elab_WF_floatRecApp___lambda__2___closed__4 = _init_l_Lean_Elab_WF_floatRecApp___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_floatRecApp___lambda__2___closed__4);
l_Lean_Elab_WF_floatRecApp___lambda__2___closed__5 = _init_l_Lean_Elab_WF_floatRecApp___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_WF_floatRecApp___lambda__2___closed__5);
l_Lean_Elab_WF_floatRecApp___closed__1 = _init_l_Lean_Elab_WF_floatRecApp___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_floatRecApp___closed__1);
l_Lean_Elab_WF_floatRecApp___closed__2 = _init_l_Lean_Elab_WF_floatRecApp___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_floatRecApp___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
