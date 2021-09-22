// Lean compiler output
// Module: Init.Control.EState
// Imports: Init.Control.State Init.Control.Except Init.Data.ToString.Basic
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
static lean_object* l_EStateM_instReprResult___rarg___closed__4;
LEAN_EXPORT lean_object* l_EStateM_fromStateM___rarg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_orElse_x27___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instToStringResult___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_EStateM_instReprResult___rarg___closed__3;
LEAN_EXPORT lean_object* l_EStateM_orElse_x27___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instToStringResult(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instMonadFinallyEStateM(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_EStateM_instToStringResult___rarg___closed__1;
LEAN_EXPORT lean_object* l_EStateM_instReprResult(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_fromStateM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instReprResult___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_EStateM_instReprResult___rarg___closed__2;
LEAN_EXPORT lean_object* l_EStateM_instMonadFinallyEStateM___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_EStateM_instToStringResult___rarg___closed__2;
LEAN_EXPORT lean_object* l_EStateM_instReprResult___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_EStateM_instReprResult___rarg___closed__1;
LEAN_EXPORT lean_object* l_EStateM_orElse_x27(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
static lean_object* _init_l_EStateM_instToStringResult___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ok: ");
return x_1;
}
}
static lean_object* _init_l_EStateM_instToStringResult___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("error: ");
return x_1;
}
}
LEAN_EXPORT lean_object* l_EStateM_instToStringResult___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_1(x_2, x_4);
x_6 = l_EStateM_instToStringResult___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_apply_1(x_1, x_8);
x_10 = l_EStateM_instToStringResult___rarg___closed__2;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_EStateM_instToStringResult(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_EStateM_instToStringResult___rarg), 3, 0);
return x_4;
}
}
static lean_object* _init_l_EStateM_instReprResult___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("EStateM.Result.ok ");
return x_1;
}
}
static lean_object* _init_l_EStateM_instReprResult___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_EStateM_instReprResult___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_EStateM_instReprResult___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("EStateM.Result.error ");
return x_1;
}
}
static lean_object* _init_l_EStateM_instReprResult___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_EStateM_instReprResult___rarg___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_EStateM_instReprResult___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_apply_2(x_2, x_5, x_6);
x_8 = l_EStateM_instReprResult___rarg___closed__2;
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Repr_addAppParen(x_9, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_unsigned_to_nat(1024u);
x_13 = lean_apply_2(x_1, x_11, x_12);
x_14 = l_EStateM_instReprResult___rarg___closed__4;
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Repr_addAppParen(x_15, x_4);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_EStateM_instReprResult(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_EStateM_instReprResult___rarg___boxed), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_EStateM_instReprResult___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_EStateM_instReprResult___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_EStateM_orElse_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_inc(x_5);
x_7 = lean_apply_1(x_6, x_5);
x_8 = lean_apply_1(x_2, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_2(x_11, x_10, x_7);
x_13 = lean_apply_1(x_3, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_9);
return x_13;
}
else
{
if (x_4 == 0)
{
uint8_t x_14; 
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_13, 0);
lean_dec(x_19);
lean_ctor_set(x_13, 0, x_9);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_EStateM_orElse_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_EStateM_orElse_x27___rarg___boxed), 5, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_EStateM_orElse_x27___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_EStateM_orElse_x27___rarg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_EStateM_instMonadFinallyEStateM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_apply_2(x_2, x_7, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_5);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_dec(x_4);
x_22 = lean_box(0);
x_23 = lean_apply_2(x_2, x_22, x_21);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_20);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_20);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EStateM_instMonadFinallyEStateM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_EStateM_instMonadFinallyEStateM___rarg), 3, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_EStateM_fromStateM___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_EStateM_fromStateM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_EStateM_fromStateM___rarg), 2, 0);
return x_4;
}
}
lean_object* initialize_Init_Control_State(lean_object*);
lean_object* initialize_Init_Control_Except(lean_object*);
lean_object* initialize_Init_Data_ToString_Basic(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Control_EState(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_State(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Except(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_EStateM_instToStringResult___rarg___closed__1 = _init_l_EStateM_instToStringResult___rarg___closed__1();
lean_mark_persistent(l_EStateM_instToStringResult___rarg___closed__1);
l_EStateM_instToStringResult___rarg___closed__2 = _init_l_EStateM_instToStringResult___rarg___closed__2();
lean_mark_persistent(l_EStateM_instToStringResult___rarg___closed__2);
l_EStateM_instReprResult___rarg___closed__1 = _init_l_EStateM_instReprResult___rarg___closed__1();
lean_mark_persistent(l_EStateM_instReprResult___rarg___closed__1);
l_EStateM_instReprResult___rarg___closed__2 = _init_l_EStateM_instReprResult___rarg___closed__2();
lean_mark_persistent(l_EStateM_instReprResult___rarg___closed__2);
l_EStateM_instReprResult___rarg___closed__3 = _init_l_EStateM_instReprResult___rarg___closed__3();
lean_mark_persistent(l_EStateM_instReprResult___rarg___closed__3);
l_EStateM_instReprResult___rarg___closed__4 = _init_l_EStateM_instReprResult___rarg___closed__4();
lean_mark_persistent(l_EStateM_instReprResult___rarg___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
