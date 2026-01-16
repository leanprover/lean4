// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.MonadRing
// Imports: public import Lean.Meta.Tactic.Grind.Arith.CommRing.MonadCanon
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadLift___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadLift___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_apply_2(x_1, lean_box(0), x_4);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_1);
x_11 = lean_apply_2(x_1, lean_box(0), x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_3);
x_9 = lean_apply_2(x_3, lean_box(0), x_6);
lean_ctor_set(x_4, 1, x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
lean_inc(x_3);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_3);
x_13 = lean_apply_2(x_3, lean_box(0), x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingOfMonadLift___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingOfMonadLift___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_apply_2(x_1, lean_box(0), x_4);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_1);
x_11 = lean_apply_2(x_1, lean_box(0), x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingOfMonadLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_3);
x_9 = lean_apply_2(x_3, lean_box(0), x_6);
lean_ctor_set(x_4, 1, x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
lean_inc(x_3);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_3);
x_13 = lean_apply_2(x_3, lean_box(0), x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get(x_2, 4);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_ctor_get(x_2, 7);
x_14 = lean_ctor_get(x_2, 8);
x_15 = lean_ctor_get(x_2, 9);
x_16 = lean_ctor_get(x_2, 10);
x_17 = lean_ctor_get(x_2, 11);
x_18 = lean_ctor_get(x_2, 12);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*15);
x_20 = lean_ctor_get(x_2, 13);
x_21 = lean_ctor_get(x_2, 14);
x_22 = lean_ctor_get_uint8(x_2, sizeof(void*)*15 + 1);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_23 = lean_apply_1(x_1, x_6);
x_24 = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_7);
lean_ctor_set(x_24, 2, x_8);
lean_ctor_set(x_24, 3, x_9);
lean_ctor_set(x_24, 4, x_10);
lean_ctor_set(x_24, 5, x_11);
lean_ctor_set(x_24, 6, x_12);
lean_ctor_set(x_24, 7, x_13);
lean_ctor_set(x_24, 8, x_14);
lean_ctor_set(x_24, 9, x_15);
lean_ctor_set(x_24, 10, x_16);
lean_ctor_set(x_24, 11, x_17);
lean_ctor_set(x_24, 12, x_18);
lean_ctor_set(x_24, 13, x_20);
lean_ctor_set(x_24, 14, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*15, x_19);
lean_ctor_set_uint8(x_24, sizeof(void*)*15 + 1, x_22);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2), 2, 1);
lean_closure_set(x_10, 0, x_8);
x_11 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_10);
lean_ctor_set(x_2, 1, x_9);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec_ref(x_3);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1), 2, 1);
lean_closure_set(x_15, 0, x_13);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2), 2, 1);
lean_closure_set(x_16, 0, x_14);
x_17 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_12, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec_ref(x_4);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1), 2, 1);
lean_closure_set(x_10, 0, x_8);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2), 2, 1);
lean_closure_set(x_11, 0, x_9);
x_12 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_11);
lean_ctor_set(x_3, 1, x_10);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec_ref(x_4);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1), 2, 1);
lean_closure_set(x_16, 0, x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2), 2, 1);
lean_closure_set(x_17, 0, x_15);
x_18 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_13, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadCanon(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadCanon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
