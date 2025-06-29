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
LEAN_EXPORT lean_object* l_EStateM_orElse_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instToStringResult___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_fromStateM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_orElse_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_EStateM_instToStringResult___redArg___lam__0___closed__1;
static lean_object* l_EStateM_instReprResult___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_EStateM_instReprResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_EStateM_instReprResult___redArg___lam__0___closed__2;
static lean_object* l_EStateM_instToStringResult___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_EStateM_instToStringResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instToStringResult___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instReprResult___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_EStateM_instReprResult___redArg___lam__0___closed__3;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instMonadFinally(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_orElse_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instMonadFinally___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_orElse_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instReprResult___redArg(lean_object*, lean_object*);
static lean_object* l_EStateM_instReprResult___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_EStateM_fromStateM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_instReprResult___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_EStateM_instToStringResult___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ok: ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_EStateM_instToStringResult___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error: ", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_EStateM_instToStringResult___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_EStateM_instToStringResult___redArg___lam__0___closed__0;
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_string_append(x_5, x_6);
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l_EStateM_instToStringResult___redArg___lam__0___closed__1;
x_10 = lean_apply_1(x_2, x_8);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_EStateM_instToStringResult___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_EStateM_instToStringResult___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_EStateM_instToStringResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_EStateM_instToStringResult___redArg(x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_EStateM_instReprResult___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("EStateM.Result.ok ", 18, 18);
return x_1;
}
}
static lean_object* _init_l_EStateM_instReprResult___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_EStateM_instReprResult___redArg___lam__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_EStateM_instReprResult___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("EStateM.Result.error ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_EStateM_instReprResult___redArg___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_EStateM_instReprResult___redArg___lam__0___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_EStateM_instReprResult___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
lean_dec(x_7);
x_8 = l_EStateM_instReprResult___redArg___lam__0___closed__1;
x_9 = lean_unsigned_to_nat(1024u);
x_10 = lean_apply_2(x_1, x_6, x_9);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_10);
lean_ctor_set(x_3, 0, x_8);
x_11 = l_Repr_addAppParen(x_3, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l_EStateM_instReprResult___redArg___lam__0___closed__1;
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_apply_2(x_1, x_12, x_14);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Repr_addAppParen(x_16, x_4);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
lean_dec(x_20);
x_21 = l_EStateM_instReprResult___redArg___lam__0___closed__3;
x_22 = lean_unsigned_to_nat(1024u);
x_23 = lean_apply_2(x_2, x_19, x_22);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_23);
lean_ctor_set(x_3, 0, x_21);
x_24 = l_Repr_addAppParen(x_3, x_4);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
lean_dec(x_3);
x_26 = l_EStateM_instReprResult___redArg___lam__0___closed__3;
x_27 = lean_unsigned_to_nat(1024u);
x_28 = lean_apply_2(x_2, x_25, x_27);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Repr_addAppParen(x_29, x_4);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_EStateM_instReprResult___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_EStateM_instReprResult___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_EStateM_instReprResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_EStateM_instReprResult___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_EStateM_instReprResult___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_EStateM_instReprResult___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_EStateM_orElse_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_2, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
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
x_11 = lean_apply_1(x_6, x_5);
x_12 = lean_apply_2(x_7, x_10, x_11);
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
lean_dec(x_9);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_9);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_EStateM_orElse_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
lean_inc(x_9);
x_12 = lean_apply_1(x_6, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_apply_1(x_10, x_9);
x_16 = lean_apply_2(x_11, x_14, x_15);
x_17 = lean_apply_1(x_7, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_13);
return x_17;
}
else
{
if (x_8 == 0)
{
lean_dec(x_13);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_13);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_EStateM_orElse_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_EStateM_orElse_x27___redArg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_EStateM_orElse_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_8);
lean_dec(x_8);
x_11 = l_EStateM_orElse_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_EStateM_instMonadFinally___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_apply_2(x_4, x_10, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_ctor_set(x_6, 1, x_13);
lean_ctor_set(x_11, 0, x_6);
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
lean_ctor_set(x_6, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_free_object(x_6);
lean_dec(x_8);
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
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
lean_inc(x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_apply_2(x_4, x_23, x_22);
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
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_25);
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
lean_dec(x_21);
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
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_6, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_6, 1);
lean_inc(x_35);
lean_dec(x_6);
x_36 = lean_box(0);
x_37 = lean_apply_2(x_4, x_36, x_35);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 0, x_34);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_34);
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_37);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EStateM_instMonadFinally(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_EStateM_instMonadFinally___lam__0), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_EStateM_fromStateM___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_EStateM_fromStateM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_apply_1(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* initialize_Init_Control_State(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Control_Except(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Control_EState(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_State(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Except(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_EStateM_instToStringResult___redArg___lam__0___closed__0 = _init_l_EStateM_instToStringResult___redArg___lam__0___closed__0();
lean_mark_persistent(l_EStateM_instToStringResult___redArg___lam__0___closed__0);
l_EStateM_instToStringResult___redArg___lam__0___closed__1 = _init_l_EStateM_instToStringResult___redArg___lam__0___closed__1();
lean_mark_persistent(l_EStateM_instToStringResult___redArg___lam__0___closed__1);
l_EStateM_instReprResult___redArg___lam__0___closed__0 = _init_l_EStateM_instReprResult___redArg___lam__0___closed__0();
lean_mark_persistent(l_EStateM_instReprResult___redArg___lam__0___closed__0);
l_EStateM_instReprResult___redArg___lam__0___closed__1 = _init_l_EStateM_instReprResult___redArg___lam__0___closed__1();
lean_mark_persistent(l_EStateM_instReprResult___redArg___lam__0___closed__1);
l_EStateM_instReprResult___redArg___lam__0___closed__2 = _init_l_EStateM_instReprResult___redArg___lam__0___closed__2();
lean_mark_persistent(l_EStateM_instReprResult___redArg___lam__0___closed__2);
l_EStateM_instReprResult___redArg___lam__0___closed__3 = _init_l_EStateM_instReprResult___redArg___lam__0___closed__3();
lean_mark_persistent(l_EStateM_instReprResult___redArg___lam__0___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
