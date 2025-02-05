// Lean compiler output
// Module: Lean.Elab.InfoTree.InlayHints
// Imports: Lean.Meta.Basic
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
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHint_ofCustomInfo_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instTypeNameInlayHint;
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_noConfusion___rarg___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213____closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHint_ofCustomInfo_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHint_resolveDeferred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213_;
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHint_toCustomInfo(lean_object*);
static lean_object* l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213____closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_toCtorIdx___boxed(lean_object*);
static lean_object* l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213____closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_noConfusion___rarg___lambda__1(lean_object*);
static lean_object* l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213____closed__4;
static lean_object* l_Lean_Elab_InlayHintKind_noConfusion___rarg___closed__1;
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_toCtorIdx(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_InlayHintKind_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_InlayHintKind_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_InlayHintKind_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_InlayHintKind_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_InlayHintKind_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_InlayHintKind_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Elab_InlayHintKind_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("InlayHint", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213____closed__1;
x_2 = l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213____closed__2;
x_3 = l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213____closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213_() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213____closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instTypeNameInlayHint() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213_;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHint_toCustomInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_instTypeNameInlayHint;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHint_ofCustomInfo_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Lean_Elab_instTypeNameInlayHint;
x_4 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___rarg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHint_ofCustomInfo_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_InlayHint_ofCustomInfo_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHint_resolveDeferred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_apply_6(x_10, x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_ctor_set(x_1, 0, x_13);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_1, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_free_object(x_1);
lean_dec(x_10);
lean_dec(x_9);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
x_23 = lean_ctor_get(x_1, 2);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
lean_inc(x_23);
x_24 = lean_apply_6(x_23, x_21, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_22);
lean_ctor_set(x_28, 2, x_23);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_23);
lean_dec(x_22);
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_32 = x_24;
} else {
 lean_dec_ref(x_24);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_InfoTree_InlayHints(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_InlayHintKind_noConfusion___rarg___closed__1 = _init_l_Lean_Elab_InlayHintKind_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_InlayHintKind_noConfusion___rarg___closed__1);
l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213____closed__1 = _init_l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213____closed__1();
lean_mark_persistent(l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213____closed__1);
l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213____closed__2 = _init_l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213____closed__2();
lean_mark_persistent(l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213____closed__2);
l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213____closed__3 = _init_l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213____closed__3();
lean_mark_persistent(l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213____closed__3);
l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213____closed__4 = _init_l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213____closed__4();
lean_mark_persistent(l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213____closed__4);
l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213_ = _init_l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213_();
lean_mark_persistent(l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_213_);
l_Lean_Elab_instTypeNameInlayHint = _init_l_Lean_Elab_instTypeNameInlayHint();
lean_mark_persistent(l_Lean_Elab_instTypeNameInlayHint);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
