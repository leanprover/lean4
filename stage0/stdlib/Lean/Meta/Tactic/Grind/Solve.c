// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Solve
// Imports: public import Lean.Meta.Tactic.Grind.Types public import Lean.Meta.Tactic.Grind.SearchM import Lean.Meta.Tactic.Grind.Split import Lean.Meta.Tactic.Grind.EMatch import Lean.Meta.Tactic.Grind.Lookahead import Lean.Meta.Tactic.Grind.Intro
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_solve_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isMaxHeartbeat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isMaxRecDepth(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_splitNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Solvers_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_solve_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_solve___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Solvers_mbtc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_solve_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_lookahead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGoal___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_assertAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ematch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop___closed__0;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_nextGoal_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg___lam__0), 10, 5);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
uint8_t x_14; 
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
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_13);
lean_dec(x_11);
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
lean_inc(x_15);
x_17 = l_Lean_Meta_Grind_Solvers_check(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_st_ref_get(x_15, x_20);
lean_dec(x_15);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_ctor_set(x_21, 1, x_23);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_17, 1, x_26);
lean_ctor_set(x_17, 0, x_27);
return x_17;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_st_ref_get(x_15, x_29);
lean_dec(x_15);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_15);
x_36 = !lean_is_exclusive(x_17);
if (x_36 == 0)
{
return x_17;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_17, 0);
x_38 = lean_ctor_get(x_17, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_17);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_13);
lean_dec(x_11);
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
lean_inc(x_15);
x_17 = l_Lean_Meta_Grind_ematch(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_st_ref_get(x_15, x_20);
lean_dec(x_15);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_ctor_set(x_21, 1, x_23);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_17, 1, x_26);
lean_ctor_set(x_17, 0, x_27);
return x_17;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_st_ref_get(x_15, x_29);
lean_dec(x_15);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_15);
x_36 = !lean_is_exclusive(x_17);
if (x_36 == 0)
{
return x_17;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_17, 0);
x_38 = lean_ctor_get(x_17, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_17);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_13);
lean_dec(x_11);
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
lean_inc(x_15);
x_17 = l_Lean_Meta_Grind_lookahead(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_st_ref_get(x_15, x_20);
lean_dec(x_15);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_ctor_set(x_21, 1, x_23);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_17, 1, x_26);
lean_ctor_set(x_17, 0, x_27);
return x_17;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_st_ref_get(x_15, x_29);
lean_dec(x_15);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_15);
x_36 = !lean_is_exclusive(x_17);
if (x_36 == 0)
{
return x_17;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_17, 0);
x_38 = lean_ctor_get(x_17, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_17);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_13);
lean_dec(x_11);
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
lean_inc(x_15);
x_17 = l_Lean_Meta_Grind_Solvers_mbtc(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_st_ref_get(x_15, x_20);
lean_dec(x_15);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_ctor_set(x_21, 1, x_23);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_17, 1, x_26);
lean_ctor_set(x_17, 0, x_27);
return x_17;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_st_ref_get(x_15, x_29);
lean_dec(x_15);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_15);
x_36 = !lean_is_exclusive(x_17);
if (x_36 == 0)
{
return x_17;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_17, 0);
x_38 = lean_ctor_get(x_17, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_17);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_33; lean_object* x_34; lean_object* x_43; 
x_43 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_11);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = lean_ctor_get_uint8(x_44, sizeof(void*)*17);
lean_dec(x_44);
x_47 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__0___boxed), 9, 0);
x_48 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__1___boxed), 9, 0);
x_49 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__2___boxed), 9, 0);
x_50 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__3___boxed), 9, 0);
if (x_46 == 0)
{
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_51 = x_3;
x_52 = x_4;
x_53 = x_5;
x_54 = x_6;
x_55 = x_7;
x_56 = x_8;
x_57 = x_9;
x_58 = x_10;
x_59 = x_45;
goto block_374;
}
else
{
lean_object* x_375; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_375 = l_Lean_Meta_Grind_nextGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_45);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
if (lean_obj_tag(x_376) == 0)
{
uint8_t x_377; 
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_377 = !lean_is_exclusive(x_375);
if (x_377 == 0)
{
lean_object* x_378; 
x_378 = lean_ctor_get(x_375, 0);
lean_dec(x_378);
lean_ctor_set(x_375, 0, x_1);
return x_375;
}
else
{
lean_object* x_379; lean_object* x_380; 
x_379 = lean_ctor_get(x_375, 1);
lean_inc(x_379);
lean_dec(x_375);
x_380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_380, 0, x_1);
lean_ctor_set(x_380, 1, x_379);
return x_380;
}
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_ctor_get(x_375, 1);
lean_inc(x_381);
lean_dec_ref(x_375);
x_382 = lean_ctor_get(x_376, 0);
lean_inc(x_382);
lean_dec_ref(x_376);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_383 = l_Lean_Meta_Grind_intros(x_382, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_381);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; 
x_384 = lean_ctor_get(x_383, 1);
lean_inc(x_384);
lean_dec_ref(x_383);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_51 = x_3;
x_52 = x_4;
x_53 = x_5;
x_54 = x_6;
x_55 = x_7;
x_56 = x_8;
x_57 = x_9;
x_58 = x_10;
x_59 = x_384;
goto block_374;
}
else
{
uint8_t x_385; 
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_385 = !lean_is_exclusive(x_383);
if (x_385 == 0)
{
return x_383;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_383, 0);
x_387 = lean_ctor_get(x_383, 1);
lean_inc(x_387);
lean_inc(x_386);
lean_dec(x_383);
x_388 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_387);
return x_388;
}
}
}
}
else
{
uint8_t x_389; 
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_389 = !lean_is_exclusive(x_375);
if (x_389 == 0)
{
return x_375;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_375, 0);
x_391 = lean_ctor_get(x_375, 1);
lean_inc(x_391);
lean_inc(x_390);
lean_dec(x_375);
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_391);
return x_392;
}
}
}
block_374:
{
lean_object* x_60; 
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_60 = l_Lean_Meta_Grind_assertAll(x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec_ref(x_60);
x_64 = l_Lean_Meta_Grind_getGoal___redArg(x_51, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec_ref(x_64);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_68 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_67, x_47, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_66);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_st_ref_take(x_51, x_70);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec_ref(x_73);
x_76 = !lean_is_exclusive(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_74, 0);
lean_dec(x_77);
lean_ctor_set(x_74, 0, x_72);
x_78 = lean_st_ref_set(x_51, x_74, x_75);
x_79 = lean_unbox(x_71);
lean_dec(x_71);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec_ref(x_78);
x_81 = l_Lean_Meta_Grind_getGoal___redArg(x_51, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec_ref(x_81);
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_85 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_84, x_48, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_83);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec_ref(x_85);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_st_ref_take(x_51, x_87);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec_ref(x_90);
x_93 = !lean_is_exclusive(x_91);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_94 = lean_ctor_get(x_91, 0);
lean_dec(x_94);
lean_ctor_set(x_91, 0, x_89);
x_95 = lean_st_ref_set(x_51, x_91, x_92);
x_96 = lean_unbox(x_88);
lean_dec(x_88);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec_ref(x_95);
x_98 = l_Lean_Meta_Grind_getGoal___redArg(x_51, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec_ref(x_98);
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
lean_dec(x_99);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_102 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_101, x_49, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_100);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec_ref(x_102);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = lean_st_ref_take(x_51, x_104);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec_ref(x_107);
x_110 = !lean_is_exclusive(x_108);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_108, 0);
lean_dec(x_111);
lean_ctor_set(x_108, 0, x_106);
x_112 = lean_st_ref_set(x_51, x_108, x_109);
x_113 = lean_unbox(x_105);
lean_dec(x_105);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec_ref(x_112);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_115 = l_Lean_Meta_Grind_splitNext(x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_unbox(x_116);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec_ref(x_115);
x_119 = l_Lean_Meta_Grind_getGoal___redArg(x_51, x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec_ref(x_119);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
lean_dec(x_120);
lean_inc(x_51);
x_123 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_122, x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec_ref(x_123);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_dec(x_124);
x_128 = lean_st_ref_take(x_51, x_125);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec_ref(x_128);
x_131 = !lean_is_exclusive(x_129);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_132 = lean_ctor_get(x_129, 0);
lean_dec(x_132);
lean_ctor_set(x_129, 0, x_127);
x_133 = lean_st_ref_set(x_51, x_129, x_130);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec_ref(x_133);
x_135 = lean_unbox(x_126);
lean_dec(x_126);
x_12 = x_51;
x_13 = x_135;
x_14 = x_134;
goto block_32;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_129, 1);
lean_inc(x_136);
lean_dec(x_129);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_127);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_st_ref_set(x_51, x_137, x_130);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec_ref(x_138);
x_140 = lean_unbox(x_126);
lean_dec(x_126);
x_12 = x_51;
x_13 = x_140;
x_14 = x_139;
goto block_32;
}
}
else
{
uint8_t x_141; 
lean_dec(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_141 = !lean_is_exclusive(x_123);
if (x_141 == 0)
{
return x_123;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_123, 0);
x_143 = lean_ctor_get(x_123, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_123);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_145 = !lean_is_exclusive(x_119);
if (x_145 == 0)
{
return x_119;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_119, 0);
x_147 = lean_ctor_get(x_119, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_119);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
else
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_50);
x_33 = x_51;
x_34 = x_115;
goto block_42;
}
}
else
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_50);
x_33 = x_51;
x_34 = x_115;
goto block_42;
}
}
else
{
lean_object* x_149; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
x_149 = lean_ctor_get(x_112, 1);
lean_inc(x_149);
lean_dec_ref(x_112);
x_11 = x_149;
goto _start;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_151 = lean_ctor_get(x_108, 1);
lean_inc(x_151);
lean_dec(x_108);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_106);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_st_ref_set(x_51, x_152, x_109);
x_154 = lean_unbox(x_105);
lean_dec(x_105);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec_ref(x_153);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_156 = l_Lean_Meta_Grind_splitNext(x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_155);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; uint8_t x_158; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_unbox(x_157);
lean_dec(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
lean_dec_ref(x_156);
x_160 = l_Lean_Meta_Grind_getGoal___redArg(x_51, x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec_ref(x_160);
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
lean_dec(x_161);
lean_inc(x_51);
x_164 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_163, x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_162);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec_ref(x_164);
x_167 = lean_ctor_get(x_165, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
lean_dec(x_165);
x_169 = lean_st_ref_take(x_51, x_166);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec_ref(x_169);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_173 = x_170;
} else {
 lean_dec_ref(x_170);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_168);
lean_ctor_set(x_174, 1, x_172);
x_175 = lean_st_ref_set(x_51, x_174, x_171);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec_ref(x_175);
x_177 = lean_unbox(x_167);
lean_dec(x_167);
x_12 = x_51;
x_13 = x_177;
x_14 = x_176;
goto block_32;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_178 = lean_ctor_get(x_164, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_164, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_180 = x_164;
} else {
 lean_dec_ref(x_164);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_182 = lean_ctor_get(x_160, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_160, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_184 = x_160;
} else {
 lean_dec_ref(x_160);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
else
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_50);
x_33 = x_51;
x_34 = x_156;
goto block_42;
}
}
else
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_50);
x_33 = x_51;
x_34 = x_156;
goto block_42;
}
}
else
{
lean_object* x_186; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
x_186 = lean_ctor_get(x_153, 1);
lean_inc(x_186);
lean_dec_ref(x_153);
x_11 = x_186;
goto _start;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_188 = !lean_is_exclusive(x_102);
if (x_188 == 0)
{
return x_102;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_102, 0);
x_190 = lean_ctor_get(x_102, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_102);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_192 = !lean_is_exclusive(x_98);
if (x_192 == 0)
{
return x_98;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_98, 0);
x_194 = lean_ctor_get(x_98, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_98);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
lean_object* x_196; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
x_196 = lean_ctor_get(x_95, 1);
lean_inc(x_196);
lean_dec_ref(x_95);
x_11 = x_196;
goto _start;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_198 = lean_ctor_get(x_91, 1);
lean_inc(x_198);
lean_dec(x_91);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_89);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_st_ref_set(x_51, x_199, x_92);
x_201 = lean_unbox(x_88);
lean_dec(x_88);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec_ref(x_200);
x_203 = l_Lean_Meta_Grind_getGoal___redArg(x_51, x_202);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec_ref(x_203);
x_206 = lean_ctor_get(x_204, 0);
lean_inc(x_206);
lean_dec(x_204);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_207 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_206, x_49, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_205);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec_ref(x_207);
x_210 = lean_ctor_get(x_208, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_208, 1);
lean_inc(x_211);
lean_dec(x_208);
x_212 = lean_st_ref_take(x_51, x_209);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec_ref(x_212);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_216 = x_213;
} else {
 lean_dec_ref(x_213);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_211);
lean_ctor_set(x_217, 1, x_215);
x_218 = lean_st_ref_set(x_51, x_217, x_214);
x_219 = lean_unbox(x_210);
lean_dec(x_210);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec_ref(x_218);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_221 = l_Lean_Meta_Grind_splitNext(x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_220);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; uint8_t x_223; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_unbox(x_222);
lean_dec(x_222);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
lean_dec_ref(x_221);
x_225 = l_Lean_Meta_Grind_getGoal___redArg(x_51, x_224);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec_ref(x_225);
x_228 = lean_ctor_get(x_226, 0);
lean_inc(x_228);
lean_dec(x_226);
lean_inc(x_51);
x_229 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_228, x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_227);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec_ref(x_229);
x_232 = lean_ctor_get(x_230, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_230, 1);
lean_inc(x_233);
lean_dec(x_230);
x_234 = lean_st_ref_take(x_51, x_231);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec_ref(x_234);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_238 = x_235;
} else {
 lean_dec_ref(x_235);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_233);
lean_ctor_set(x_239, 1, x_237);
x_240 = lean_st_ref_set(x_51, x_239, x_236);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
lean_dec_ref(x_240);
x_242 = lean_unbox(x_232);
lean_dec(x_232);
x_12 = x_51;
x_13 = x_242;
x_14 = x_241;
goto block_32;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_243 = lean_ctor_get(x_229, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_229, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_245 = x_229;
} else {
 lean_dec_ref(x_229);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(1, 2, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_244);
return x_246;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_247 = lean_ctor_get(x_225, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_225, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_249 = x_225;
} else {
 lean_dec_ref(x_225);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_248);
return x_250;
}
}
else
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_50);
x_33 = x_51;
x_34 = x_221;
goto block_42;
}
}
else
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_50);
x_33 = x_51;
x_34 = x_221;
goto block_42;
}
}
else
{
lean_object* x_251; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
x_251 = lean_ctor_get(x_218, 1);
lean_inc(x_251);
lean_dec_ref(x_218);
x_11 = x_251;
goto _start;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_253 = lean_ctor_get(x_207, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_207, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_255 = x_207;
} else {
 lean_dec_ref(x_207);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_257 = lean_ctor_get(x_203, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_203, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_259 = x_203;
} else {
 lean_dec_ref(x_203);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_258);
return x_260;
}
}
else
{
lean_object* x_261; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
x_261 = lean_ctor_get(x_200, 1);
lean_inc(x_261);
lean_dec_ref(x_200);
x_11 = x_261;
goto _start;
}
}
}
else
{
uint8_t x_263; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_263 = !lean_is_exclusive(x_85);
if (x_263 == 0)
{
return x_85;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_85, 0);
x_265 = lean_ctor_get(x_85, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_85);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
}
else
{
uint8_t x_267; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_267 = !lean_is_exclusive(x_81);
if (x_267 == 0)
{
return x_81;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_81, 0);
x_269 = lean_ctor_get(x_81, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_81);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
}
else
{
lean_object* x_271; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
x_271 = lean_ctor_get(x_78, 1);
lean_inc(x_271);
lean_dec_ref(x_78);
x_11 = x_271;
goto _start;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; 
x_273 = lean_ctor_get(x_74, 1);
lean_inc(x_273);
lean_dec(x_74);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_72);
lean_ctor_set(x_274, 1, x_273);
x_275 = lean_st_ref_set(x_51, x_274, x_75);
x_276 = lean_unbox(x_71);
lean_dec(x_71);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; 
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec_ref(x_275);
x_278 = l_Lean_Meta_Grind_getGoal___redArg(x_51, x_277);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
lean_dec_ref(x_278);
x_281 = lean_ctor_get(x_279, 0);
lean_inc(x_281);
lean_dec(x_279);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_282 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_281, x_48, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_280);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec_ref(x_282);
x_285 = lean_ctor_get(x_283, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_283, 1);
lean_inc(x_286);
lean_dec(x_283);
x_287 = lean_st_ref_take(x_51, x_284);
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec_ref(x_287);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_291 = x_288;
} else {
 lean_dec_ref(x_288);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_286);
lean_ctor_set(x_292, 1, x_290);
x_293 = lean_st_ref_set(x_51, x_292, x_289);
x_294 = lean_unbox(x_285);
lean_dec(x_285);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec_ref(x_293);
x_296 = l_Lean_Meta_Grind_getGoal___redArg(x_51, x_295);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec_ref(x_296);
x_299 = lean_ctor_get(x_297, 0);
lean_inc(x_299);
lean_dec(x_297);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_300 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_299, x_49, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_298);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec_ref(x_300);
x_303 = lean_ctor_get(x_301, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_301, 1);
lean_inc(x_304);
lean_dec(x_301);
x_305 = lean_st_ref_take(x_51, x_302);
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
lean_dec_ref(x_305);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 x_309 = x_306;
} else {
 lean_dec_ref(x_306);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_304);
lean_ctor_set(x_310, 1, x_308);
x_311 = lean_st_ref_set(x_51, x_310, x_307);
x_312 = lean_unbox(x_303);
lean_dec(x_303);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; 
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
lean_dec_ref(x_311);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_314 = l_Lean_Meta_Grind_splitNext(x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_313);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; uint8_t x_316; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_unbox(x_315);
lean_dec(x_315);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; 
x_317 = lean_ctor_get(x_314, 1);
lean_inc(x_317);
lean_dec_ref(x_314);
x_318 = l_Lean_Meta_Grind_getGoal___redArg(x_51, x_317);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec_ref(x_318);
x_321 = lean_ctor_get(x_319, 0);
lean_inc(x_321);
lean_dec(x_319);
lean_inc(x_51);
x_322 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_321, x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_320);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
lean_dec_ref(x_322);
x_325 = lean_ctor_get(x_323, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_323, 1);
lean_inc(x_326);
lean_dec(x_323);
x_327 = lean_st_ref_take(x_51, x_324);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
lean_dec_ref(x_327);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_331 = x_328;
} else {
 lean_dec_ref(x_328);
 x_331 = lean_box(0);
}
if (lean_is_scalar(x_331)) {
 x_332 = lean_alloc_ctor(0, 2, 0);
} else {
 x_332 = x_331;
}
lean_ctor_set(x_332, 0, x_326);
lean_ctor_set(x_332, 1, x_330);
x_333 = lean_st_ref_set(x_51, x_332, x_329);
x_334 = lean_ctor_get(x_333, 1);
lean_inc(x_334);
lean_dec_ref(x_333);
x_335 = lean_unbox(x_325);
lean_dec(x_325);
x_12 = x_51;
x_13 = x_335;
x_14 = x_334;
goto block_32;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_336 = lean_ctor_get(x_322, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_322, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 x_338 = x_322;
} else {
 lean_dec_ref(x_322);
 x_338 = lean_box(0);
}
if (lean_is_scalar(x_338)) {
 x_339 = lean_alloc_ctor(1, 2, 0);
} else {
 x_339 = x_338;
}
lean_ctor_set(x_339, 0, x_336);
lean_ctor_set(x_339, 1, x_337);
return x_339;
}
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_340 = lean_ctor_get(x_318, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_318, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_342 = x_318;
} else {
 lean_dec_ref(x_318);
 x_342 = lean_box(0);
}
if (lean_is_scalar(x_342)) {
 x_343 = lean_alloc_ctor(1, 2, 0);
} else {
 x_343 = x_342;
}
lean_ctor_set(x_343, 0, x_340);
lean_ctor_set(x_343, 1, x_341);
return x_343;
}
}
else
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_50);
x_33 = x_51;
x_34 = x_314;
goto block_42;
}
}
else
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_50);
x_33 = x_51;
x_34 = x_314;
goto block_42;
}
}
else
{
lean_object* x_344; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
x_344 = lean_ctor_get(x_311, 1);
lean_inc(x_344);
lean_dec_ref(x_311);
x_11 = x_344;
goto _start;
}
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_346 = lean_ctor_get(x_300, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_300, 1);
lean_inc(x_347);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_348 = x_300;
} else {
 lean_dec_ref(x_300);
 x_348 = lean_box(0);
}
if (lean_is_scalar(x_348)) {
 x_349 = lean_alloc_ctor(1, 2, 0);
} else {
 x_349 = x_348;
}
lean_ctor_set(x_349, 0, x_346);
lean_ctor_set(x_349, 1, x_347);
return x_349;
}
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_350 = lean_ctor_get(x_296, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_296, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_352 = x_296;
} else {
 lean_dec_ref(x_296);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(1, 2, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_350);
lean_ctor_set(x_353, 1, x_351);
return x_353;
}
}
else
{
lean_object* x_354; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
x_354 = lean_ctor_get(x_293, 1);
lean_inc(x_354);
lean_dec_ref(x_293);
x_11 = x_354;
goto _start;
}
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_356 = lean_ctor_get(x_282, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_282, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_358 = x_282;
} else {
 lean_dec_ref(x_282);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(1, 2, 0);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_356);
lean_ctor_set(x_359, 1, x_357);
return x_359;
}
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_360 = lean_ctor_get(x_278, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_278, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_362 = x_278;
} else {
 lean_dec_ref(x_278);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(1, 2, 0);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_360);
lean_ctor_set(x_363, 1, x_361);
return x_363;
}
}
else
{
lean_object* x_364; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
x_364 = lean_ctor_get(x_275, 1);
lean_inc(x_364);
lean_dec_ref(x_275);
x_11 = x_364;
goto _start;
}
}
}
else
{
uint8_t x_366; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_366 = !lean_is_exclusive(x_68);
if (x_366 == 0)
{
return x_68;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_367 = lean_ctor_get(x_68, 0);
x_368 = lean_ctor_get(x_68, 1);
lean_inc(x_368);
lean_inc(x_367);
lean_dec(x_68);
x_369 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set(x_369, 1, x_368);
return x_369;
}
}
}
else
{
uint8_t x_370; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_370 = !lean_is_exclusive(x_64);
if (x_370 == 0)
{
return x_64;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_371 = lean_ctor_get(x_64, 0);
x_372 = lean_ctor_get(x_64, 1);
lean_inc(x_372);
lean_inc(x_371);
lean_dec(x_64);
x_373 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set(x_373, 1, x_372);
return x_373;
}
}
}
else
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
x_33 = x_51;
x_34 = x_60;
goto block_42;
}
}
else
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
x_33 = x_51;
x_34 = x_60;
goto block_42;
}
}
}
else
{
uint8_t x_393; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_393 = !lean_is_exclusive(x_43);
if (x_393 == 0)
{
return x_43;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_43, 0);
x_395 = lean_ctor_get(x_43, 1);
lean_inc(x_395);
lean_inc(x_394);
lean_dec(x_43);
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
return x_396;
}
}
block_32:
{
if (x_13 == 0)
{
lean_object* x_15; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_15 = l_Lean_Meta_Grind_getGoal___redArg(x_12, x_14);
lean_dec(x_12);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_dec(x_12);
x_11 = x_14;
goto _start;
}
}
block_42:
{
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = lean_unbox(x_35);
lean_dec(x_35);
x_12 = x_33;
x_13 = x_37;
x_14 = x_36;
goto block_32;
}
else
{
uint8_t x_38; 
lean_dec(x_33);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_34);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_33; lean_object* x_34; lean_object* x_43; 
x_43 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_11);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = lean_ctor_get_uint8(x_44, sizeof(void*)*17);
lean_dec(x_44);
x_47 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__0___boxed), 9, 0);
x_48 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__1___boxed), 9, 0);
x_49 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__2___boxed), 9, 0);
x_50 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__3___boxed), 9, 0);
if (x_46 == 0)
{
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_51 = x_3;
x_52 = x_4;
x_53 = x_5;
x_54 = x_6;
x_55 = x_7;
x_56 = x_8;
x_57 = x_9;
x_58 = x_10;
x_59 = x_45;
goto block_374;
}
else
{
lean_object* x_375; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_375 = l_Lean_Meta_Grind_nextGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_45);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
if (lean_obj_tag(x_376) == 0)
{
uint8_t x_377; 
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_377 = !lean_is_exclusive(x_375);
if (x_377 == 0)
{
lean_object* x_378; 
x_378 = lean_ctor_get(x_375, 0);
lean_dec(x_378);
lean_ctor_set(x_375, 0, x_1);
return x_375;
}
else
{
lean_object* x_379; lean_object* x_380; 
x_379 = lean_ctor_get(x_375, 1);
lean_inc(x_379);
lean_dec(x_375);
x_380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_380, 0, x_1);
lean_ctor_set(x_380, 1, x_379);
return x_380;
}
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_ctor_get(x_375, 1);
lean_inc(x_381);
lean_dec_ref(x_375);
x_382 = lean_ctor_get(x_376, 0);
lean_inc(x_382);
lean_dec_ref(x_376);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_383 = l_Lean_Meta_Grind_intros(x_382, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_381);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; 
x_384 = lean_ctor_get(x_383, 1);
lean_inc(x_384);
lean_dec_ref(x_383);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_51 = x_3;
x_52 = x_4;
x_53 = x_5;
x_54 = x_6;
x_55 = x_7;
x_56 = x_8;
x_57 = x_9;
x_58 = x_10;
x_59 = x_384;
goto block_374;
}
else
{
uint8_t x_385; 
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_385 = !lean_is_exclusive(x_383);
if (x_385 == 0)
{
return x_383;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_383, 0);
x_387 = lean_ctor_get(x_383, 1);
lean_inc(x_387);
lean_inc(x_386);
lean_dec(x_383);
x_388 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_387);
return x_388;
}
}
}
}
else
{
uint8_t x_389; 
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_389 = !lean_is_exclusive(x_375);
if (x_389 == 0)
{
return x_375;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_375, 0);
x_391 = lean_ctor_get(x_375, 1);
lean_inc(x_391);
lean_inc(x_390);
lean_dec(x_375);
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_391);
return x_392;
}
}
}
block_374:
{
lean_object* x_60; 
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_60 = l_Lean_Meta_Grind_assertAll(x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec_ref(x_60);
x_64 = l_Lean_Meta_Grind_getGoal___redArg(x_51, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec_ref(x_64);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_68 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_67, x_47, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_66);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_st_ref_take(x_51, x_70);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec_ref(x_73);
x_76 = !lean_is_exclusive(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_74, 0);
lean_dec(x_77);
lean_ctor_set(x_74, 0, x_72);
x_78 = lean_st_ref_set(x_51, x_74, x_75);
x_79 = lean_unbox(x_71);
lean_dec(x_71);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec_ref(x_78);
x_81 = l_Lean_Meta_Grind_getGoal___redArg(x_51, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec_ref(x_81);
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_85 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_84, x_48, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_83);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec_ref(x_85);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_st_ref_take(x_51, x_87);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec_ref(x_90);
x_93 = !lean_is_exclusive(x_91);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_94 = lean_ctor_get(x_91, 0);
lean_dec(x_94);
lean_ctor_set(x_91, 0, x_89);
x_95 = lean_st_ref_set(x_51, x_91, x_92);
x_96 = lean_unbox(x_88);
lean_dec(x_88);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec_ref(x_95);
x_98 = l_Lean_Meta_Grind_getGoal___redArg(x_51, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec_ref(x_98);
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
lean_dec(x_99);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_102 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_101, x_49, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_100);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec_ref(x_102);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = lean_st_ref_take(x_51, x_104);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec_ref(x_107);
x_110 = !lean_is_exclusive(x_108);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_108, 0);
lean_dec(x_111);
lean_ctor_set(x_108, 0, x_106);
x_112 = lean_st_ref_set(x_51, x_108, x_109);
x_113 = lean_unbox(x_105);
lean_dec(x_105);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec_ref(x_112);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_115 = l_Lean_Meta_Grind_splitNext(x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_unbox(x_116);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec_ref(x_115);
x_119 = l_Lean_Meta_Grind_getGoal___redArg(x_51, x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec_ref(x_119);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
lean_dec(x_120);
lean_inc(x_51);
x_123 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_122, x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec_ref(x_123);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_dec(x_124);
x_128 = lean_st_ref_take(x_51, x_125);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec_ref(x_128);
x_131 = !lean_is_exclusive(x_129);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_132 = lean_ctor_get(x_129, 0);
lean_dec(x_132);
lean_ctor_set(x_129, 0, x_127);
x_133 = lean_st_ref_set(x_51, x_129, x_130);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec_ref(x_133);
x_135 = lean_unbox(x_126);
lean_dec(x_126);
x_12 = x_51;
x_13 = x_135;
x_14 = x_134;
goto block_32;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_129, 1);
lean_inc(x_136);
lean_dec(x_129);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_127);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_st_ref_set(x_51, x_137, x_130);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec_ref(x_138);
x_140 = lean_unbox(x_126);
lean_dec(x_126);
x_12 = x_51;
x_13 = x_140;
x_14 = x_139;
goto block_32;
}
}
else
{
uint8_t x_141; 
lean_dec(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_141 = !lean_is_exclusive(x_123);
if (x_141 == 0)
{
return x_123;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_123, 0);
x_143 = lean_ctor_get(x_123, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_123);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_145 = !lean_is_exclusive(x_119);
if (x_145 == 0)
{
return x_119;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_119, 0);
x_147 = lean_ctor_get(x_119, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_119);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
else
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_50);
x_33 = x_51;
x_34 = x_115;
goto block_42;
}
}
else
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_50);
x_33 = x_51;
x_34 = x_115;
goto block_42;
}
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
x_149 = lean_ctor_get(x_112, 1);
lean_inc(x_149);
lean_dec_ref(x_112);
x_150 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_149);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_151 = lean_ctor_get(x_108, 1);
lean_inc(x_151);
lean_dec(x_108);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_106);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_st_ref_set(x_51, x_152, x_109);
x_154 = lean_unbox(x_105);
lean_dec(x_105);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec_ref(x_153);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_156 = l_Lean_Meta_Grind_splitNext(x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_155);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; uint8_t x_158; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_unbox(x_157);
lean_dec(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
lean_dec_ref(x_156);
x_160 = l_Lean_Meta_Grind_getGoal___redArg(x_51, x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec_ref(x_160);
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
lean_dec(x_161);
lean_inc(x_51);
x_164 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_163, x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_162);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec_ref(x_164);
x_167 = lean_ctor_get(x_165, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
lean_dec(x_165);
x_169 = lean_st_ref_take(x_51, x_166);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec_ref(x_169);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_173 = x_170;
} else {
 lean_dec_ref(x_170);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_168);
lean_ctor_set(x_174, 1, x_172);
x_175 = lean_st_ref_set(x_51, x_174, x_171);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec_ref(x_175);
x_177 = lean_unbox(x_167);
lean_dec(x_167);
x_12 = x_51;
x_13 = x_177;
x_14 = x_176;
goto block_32;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_178 = lean_ctor_get(x_164, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_164, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_180 = x_164;
} else {
 lean_dec_ref(x_164);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_182 = lean_ctor_get(x_160, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_160, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_184 = x_160;
} else {
 lean_dec_ref(x_160);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
else
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_50);
x_33 = x_51;
x_34 = x_156;
goto block_42;
}
}
else
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_50);
x_33 = x_51;
x_34 = x_156;
goto block_42;
}
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
x_186 = lean_ctor_get(x_153, 1);
lean_inc(x_186);
lean_dec_ref(x_153);
x_187 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_186);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_188 = !lean_is_exclusive(x_102);
if (x_188 == 0)
{
return x_102;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_102, 0);
x_190 = lean_ctor_get(x_102, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_102);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_192 = !lean_is_exclusive(x_98);
if (x_192 == 0)
{
return x_98;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_98, 0);
x_194 = lean_ctor_get(x_98, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_98);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
lean_object* x_196; lean_object* x_197; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
x_196 = lean_ctor_get(x_95, 1);
lean_inc(x_196);
lean_dec_ref(x_95);
x_197 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_196);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_198 = lean_ctor_get(x_91, 1);
lean_inc(x_198);
lean_dec(x_91);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_89);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_st_ref_set(x_51, x_199, x_92);
x_201 = lean_unbox(x_88);
lean_dec(x_88);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec_ref(x_200);
x_203 = l_Lean_Meta_Grind_getGoal___redArg(x_51, x_202);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec_ref(x_203);
x_206 = lean_ctor_get(x_204, 0);
lean_inc(x_206);
lean_dec(x_204);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_207 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_206, x_49, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_205);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec_ref(x_207);
x_210 = lean_ctor_get(x_208, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_208, 1);
lean_inc(x_211);
lean_dec(x_208);
x_212 = lean_st_ref_take(x_51, x_209);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec_ref(x_212);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_216 = x_213;
} else {
 lean_dec_ref(x_213);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_211);
lean_ctor_set(x_217, 1, x_215);
x_218 = lean_st_ref_set(x_51, x_217, x_214);
x_219 = lean_unbox(x_210);
lean_dec(x_210);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec_ref(x_218);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_221 = l_Lean_Meta_Grind_splitNext(x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_220);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; uint8_t x_223; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_unbox(x_222);
lean_dec(x_222);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
lean_dec_ref(x_221);
x_225 = l_Lean_Meta_Grind_getGoal___redArg(x_51, x_224);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec_ref(x_225);
x_228 = lean_ctor_get(x_226, 0);
lean_inc(x_228);
lean_dec(x_226);
lean_inc(x_51);
x_229 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_228, x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_227);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec_ref(x_229);
x_232 = lean_ctor_get(x_230, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_230, 1);
lean_inc(x_233);
lean_dec(x_230);
x_234 = lean_st_ref_take(x_51, x_231);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec_ref(x_234);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_238 = x_235;
} else {
 lean_dec_ref(x_235);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_233);
lean_ctor_set(x_239, 1, x_237);
x_240 = lean_st_ref_set(x_51, x_239, x_236);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
lean_dec_ref(x_240);
x_242 = lean_unbox(x_232);
lean_dec(x_232);
x_12 = x_51;
x_13 = x_242;
x_14 = x_241;
goto block_32;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_243 = lean_ctor_get(x_229, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_229, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_245 = x_229;
} else {
 lean_dec_ref(x_229);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(1, 2, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_244);
return x_246;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_247 = lean_ctor_get(x_225, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_225, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_249 = x_225;
} else {
 lean_dec_ref(x_225);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_248);
return x_250;
}
}
else
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_50);
x_33 = x_51;
x_34 = x_221;
goto block_42;
}
}
else
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_50);
x_33 = x_51;
x_34 = x_221;
goto block_42;
}
}
else
{
lean_object* x_251; lean_object* x_252; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
x_251 = lean_ctor_get(x_218, 1);
lean_inc(x_251);
lean_dec_ref(x_218);
x_252 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_251);
return x_252;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_253 = lean_ctor_get(x_207, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_207, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_255 = x_207;
} else {
 lean_dec_ref(x_207);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_257 = lean_ctor_get(x_203, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_203, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_259 = x_203;
} else {
 lean_dec_ref(x_203);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_258);
return x_260;
}
}
else
{
lean_object* x_261; lean_object* x_262; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
x_261 = lean_ctor_get(x_200, 1);
lean_inc(x_261);
lean_dec_ref(x_200);
x_262 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_261);
return x_262;
}
}
}
else
{
uint8_t x_263; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_263 = !lean_is_exclusive(x_85);
if (x_263 == 0)
{
return x_85;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_85, 0);
x_265 = lean_ctor_get(x_85, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_85);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
}
else
{
uint8_t x_267; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_267 = !lean_is_exclusive(x_81);
if (x_267 == 0)
{
return x_81;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_81, 0);
x_269 = lean_ctor_get(x_81, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_81);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
}
else
{
lean_object* x_271; lean_object* x_272; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
x_271 = lean_ctor_get(x_78, 1);
lean_inc(x_271);
lean_dec_ref(x_78);
x_272 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_271);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; 
x_273 = lean_ctor_get(x_74, 1);
lean_inc(x_273);
lean_dec(x_74);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_72);
lean_ctor_set(x_274, 1, x_273);
x_275 = lean_st_ref_set(x_51, x_274, x_75);
x_276 = lean_unbox(x_71);
lean_dec(x_71);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; 
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec_ref(x_275);
x_278 = l_Lean_Meta_Grind_getGoal___redArg(x_51, x_277);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
lean_dec_ref(x_278);
x_281 = lean_ctor_get(x_279, 0);
lean_inc(x_281);
lean_dec(x_279);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_282 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_281, x_48, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_280);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec_ref(x_282);
x_285 = lean_ctor_get(x_283, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_283, 1);
lean_inc(x_286);
lean_dec(x_283);
x_287 = lean_st_ref_take(x_51, x_284);
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec_ref(x_287);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_291 = x_288;
} else {
 lean_dec_ref(x_288);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_286);
lean_ctor_set(x_292, 1, x_290);
x_293 = lean_st_ref_set(x_51, x_292, x_289);
x_294 = lean_unbox(x_285);
lean_dec(x_285);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec_ref(x_293);
x_296 = l_Lean_Meta_Grind_getGoal___redArg(x_51, x_295);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec_ref(x_296);
x_299 = lean_ctor_get(x_297, 0);
lean_inc(x_299);
lean_dec(x_297);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_300 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_299, x_49, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_298);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec_ref(x_300);
x_303 = lean_ctor_get(x_301, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_301, 1);
lean_inc(x_304);
lean_dec(x_301);
x_305 = lean_st_ref_take(x_51, x_302);
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
lean_dec_ref(x_305);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 x_309 = x_306;
} else {
 lean_dec_ref(x_306);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_304);
lean_ctor_set(x_310, 1, x_308);
x_311 = lean_st_ref_set(x_51, x_310, x_307);
x_312 = lean_unbox(x_303);
lean_dec(x_303);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; 
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
lean_dec_ref(x_311);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_314 = l_Lean_Meta_Grind_splitNext(x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_313);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; uint8_t x_316; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_unbox(x_315);
lean_dec(x_315);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; 
x_317 = lean_ctor_get(x_314, 1);
lean_inc(x_317);
lean_dec_ref(x_314);
x_318 = l_Lean_Meta_Grind_getGoal___redArg(x_51, x_317);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec_ref(x_318);
x_321 = lean_ctor_get(x_319, 0);
lean_inc(x_321);
lean_dec(x_319);
lean_inc(x_51);
x_322 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_321, x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_320);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
lean_dec_ref(x_322);
x_325 = lean_ctor_get(x_323, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_323, 1);
lean_inc(x_326);
lean_dec(x_323);
x_327 = lean_st_ref_take(x_51, x_324);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
lean_dec_ref(x_327);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_331 = x_328;
} else {
 lean_dec_ref(x_328);
 x_331 = lean_box(0);
}
if (lean_is_scalar(x_331)) {
 x_332 = lean_alloc_ctor(0, 2, 0);
} else {
 x_332 = x_331;
}
lean_ctor_set(x_332, 0, x_326);
lean_ctor_set(x_332, 1, x_330);
x_333 = lean_st_ref_set(x_51, x_332, x_329);
x_334 = lean_ctor_get(x_333, 1);
lean_inc(x_334);
lean_dec_ref(x_333);
x_335 = lean_unbox(x_325);
lean_dec(x_325);
x_12 = x_51;
x_13 = x_335;
x_14 = x_334;
goto block_32;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_336 = lean_ctor_get(x_322, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_322, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 x_338 = x_322;
} else {
 lean_dec_ref(x_322);
 x_338 = lean_box(0);
}
if (lean_is_scalar(x_338)) {
 x_339 = lean_alloc_ctor(1, 2, 0);
} else {
 x_339 = x_338;
}
lean_ctor_set(x_339, 0, x_336);
lean_ctor_set(x_339, 1, x_337);
return x_339;
}
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_340 = lean_ctor_get(x_318, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_318, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_342 = x_318;
} else {
 lean_dec_ref(x_318);
 x_342 = lean_box(0);
}
if (lean_is_scalar(x_342)) {
 x_343 = lean_alloc_ctor(1, 2, 0);
} else {
 x_343 = x_342;
}
lean_ctor_set(x_343, 0, x_340);
lean_ctor_set(x_343, 1, x_341);
return x_343;
}
}
else
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_50);
x_33 = x_51;
x_34 = x_314;
goto block_42;
}
}
else
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_50);
x_33 = x_51;
x_34 = x_314;
goto block_42;
}
}
else
{
lean_object* x_344; lean_object* x_345; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
x_344 = lean_ctor_get(x_311, 1);
lean_inc(x_344);
lean_dec_ref(x_311);
x_345 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_344);
return x_345;
}
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_346 = lean_ctor_get(x_300, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_300, 1);
lean_inc(x_347);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_348 = x_300;
} else {
 lean_dec_ref(x_300);
 x_348 = lean_box(0);
}
if (lean_is_scalar(x_348)) {
 x_349 = lean_alloc_ctor(1, 2, 0);
} else {
 x_349 = x_348;
}
lean_ctor_set(x_349, 0, x_346);
lean_ctor_set(x_349, 1, x_347);
return x_349;
}
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_350 = lean_ctor_get(x_296, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_296, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_352 = x_296;
} else {
 lean_dec_ref(x_296);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(1, 2, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_350);
lean_ctor_set(x_353, 1, x_351);
return x_353;
}
}
else
{
lean_object* x_354; lean_object* x_355; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
x_354 = lean_ctor_get(x_293, 1);
lean_inc(x_354);
lean_dec_ref(x_293);
x_355 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_354);
return x_355;
}
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_356 = lean_ctor_get(x_282, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_282, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_358 = x_282;
} else {
 lean_dec_ref(x_282);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(1, 2, 0);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_356);
lean_ctor_set(x_359, 1, x_357);
return x_359;
}
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_360 = lean_ctor_get(x_278, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_278, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_362 = x_278;
} else {
 lean_dec_ref(x_278);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(1, 2, 0);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_360);
lean_ctor_set(x_363, 1, x_361);
return x_363;
}
}
else
{
lean_object* x_364; lean_object* x_365; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
x_364 = lean_ctor_get(x_275, 1);
lean_inc(x_364);
lean_dec_ref(x_275);
x_365 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_364);
return x_365;
}
}
}
else
{
uint8_t x_366; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_366 = !lean_is_exclusive(x_68);
if (x_366 == 0)
{
return x_68;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_367 = lean_ctor_get(x_68, 0);
x_368 = lean_ctor_get(x_68, 1);
lean_inc(x_368);
lean_inc(x_367);
lean_dec(x_68);
x_369 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set(x_369, 1, x_368);
return x_369;
}
}
}
else
{
uint8_t x_370; 
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_370 = !lean_is_exclusive(x_64);
if (x_370 == 0)
{
return x_64;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_371 = lean_ctor_get(x_64, 0);
x_372 = lean_ctor_get(x_64, 1);
lean_inc(x_372);
lean_inc(x_371);
lean_dec(x_64);
x_373 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set(x_373, 1, x_372);
return x_373;
}
}
}
else
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
x_33 = x_51;
x_34 = x_60;
goto block_42;
}
}
else
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
x_33 = x_51;
x_34 = x_60;
goto block_42;
}
}
}
else
{
uint8_t x_393; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_393 = !lean_is_exclusive(x_43);
if (x_393 == 0)
{
return x_43;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_43, 0);
x_395 = lean_ctor_get(x_43, 1);
lean_inc(x_395);
lean_inc(x_394);
lean_dec(x_43);
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
return x_396;
}
}
block_32:
{
if (x_13 == 0)
{
lean_object* x_15; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_15 = l_Lean_Meta_Grind_getGoal___redArg(x_12, x_14);
lean_dec(x_12);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_12);
x_31 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_31;
}
}
block_42:
{
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = lean_unbox(x_35);
lean_dec(x_35);
x_12 = x_33;
x_13 = x_37;
x_14 = x_36;
goto block_32;
}
else
{
uint8_t x_38; 
lean_dec(x_33);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_34);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Lean_Meta_Grind_intros(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop___closed__0;
x_16 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1___redArg(x_15, x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_16, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec_ref(x_18);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec_ref(x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_11);
if (x_33 == 0)
{
return x_11;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_11, 0);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_11);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_13);
lean_dec(x_11);
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = l_Lean_Meta_Grind_getConfig___redArg(x_3, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_st_ref_get(x_15, x_20);
lean_dec(x_15);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_ctor_set(x_21, 1, x_23);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_17, 1, x_26);
lean_ctor_set(x_17, 0, x_27);
return x_17;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_st_ref_get(x_15, x_29);
lean_dec(x_15);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_15);
x_36 = !lean_is_exclusive(x_17);
if (x_36 == 0)
{
return x_17;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_17, 0);
x_38 = lean_ctor_get(x_17, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_17);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_st_ref_get(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_14);
lean_dec(x_12);
x_15 = lean_st_mk_ref(x_14, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = l_Lean_Meta_Grind_reportIssue(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_st_ref_get(x_16, x_21);
lean_dec(x_16);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_ctor_set(x_22, 1, x_24);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_18, 1, x_25);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_18, 1, x_27);
lean_ctor_set(x_18, 0, x_28);
return x_18;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_st_ref_get(x_16, x_30);
lean_dec(x_16);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_16);
x_37 = !lean_is_exclusive(x_18);
if (x_37 == 0)
{
return x_18;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_18, 0);
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_18);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_25; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_25 = l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_25) == 0)
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
x_28 = l_Lean_Exception_isInterrupt(x_26);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; uint8_t x_119; 
x_29 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main___lam__0___boxed), 9, 0);
x_119 = l_Lean_Exception_isMaxHeartbeat(x_26);
if (x_119 == 0)
{
uint8_t x_120; 
x_120 = l_Lean_Exception_isMaxRecDepth(x_26);
x_30 = x_120;
goto block_118;
}
else
{
x_30 = x_119;
goto block_118;
}
block_118:
{
if (x_30 == 0)
{
lean_dec_ref(x_29);
lean_dec(x_26);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_25;
}
else
{
lean_object* x_31; 
lean_dec_ref(x_25);
x_31 = l_Lean_Meta_Grind_getGoal___redArg(x_1, x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_35 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_34, x_29, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_st_ref_take(x_1, x_37);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_41, 0);
lean_dec(x_44);
lean_ctor_set(x_41, 0, x_39);
x_45 = lean_st_ref_set(x_1, x_41, x_42);
x_46 = lean_ctor_get_uint8(x_38, sizeof(void*)*8 + 11);
lean_dec(x_38);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_10 = x_1;
x_11 = x_47;
goto block_24;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec_ref(x_45);
x_49 = l_Lean_Meta_Grind_getGoal___redArg(x_1, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec_ref(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Exception_toMessageData(x_26);
x_54 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main___lam__1___boxed), 10, 1);
lean_closure_set(x_54, 0, x_53);
lean_inc(x_1);
x_55 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_52, x_54, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_51);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_st_ref_take(x_1, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec_ref(x_59);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_60, 0);
lean_dec(x_63);
lean_ctor_set(x_60, 0, x_58);
x_64 = lean_st_ref_set(x_1, x_60, x_61);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec_ref(x_64);
x_10 = x_1;
x_11 = x_65;
goto block_24;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
lean_dec(x_60);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_58);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_st_ref_set(x_1, x_67, x_61);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec_ref(x_68);
x_10 = x_1;
x_11 = x_69;
goto block_24;
}
}
else
{
uint8_t x_70; 
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_55);
if (x_70 == 0)
{
return x_55;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_55, 0);
x_72 = lean_ctor_get(x_55, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_55);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_49);
if (x_74 == 0)
{
return x_49;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_49, 0);
x_76 = lean_ctor_get(x_49, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_49);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_ctor_get(x_41, 1);
lean_inc(x_78);
lean_dec(x_41);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_39);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_st_ref_set(x_1, x_79, x_42);
x_81 = lean_ctor_get_uint8(x_38, sizeof(void*)*8 + 11);
lean_dec(x_38);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec_ref(x_80);
x_10 = x_1;
x_11 = x_82;
goto block_24;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec_ref(x_80);
x_84 = l_Lean_Meta_Grind_getGoal___redArg(x_1, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec_ref(x_84);
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Lean_Exception_toMessageData(x_26);
x_89 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main___lam__1___boxed), 10, 1);
lean_closure_set(x_89, 0, x_88);
lean_inc(x_1);
x_90 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_87, x_89, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_86);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec_ref(x_90);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_st_ref_take(x_1, x_92);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec_ref(x_94);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_93);
lean_ctor_set(x_99, 1, x_97);
x_100 = lean_st_ref_set(x_1, x_99, x_96);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec_ref(x_100);
x_10 = x_1;
x_11 = x_101;
goto block_24;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_1);
x_102 = lean_ctor_get(x_90, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_90, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_104 = x_90;
} else {
 lean_dec_ref(x_90);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = lean_ctor_get(x_84, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_84, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_108 = x_84;
} else {
 lean_dec_ref(x_84);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_35);
if (x_110 == 0)
{
return x_35;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_35, 0);
x_112 = lean_ctor_get(x_35, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_35);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec_ref(x_29);
lean_dec(x_26);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_31);
if (x_114 == 0)
{
return x_31;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_31, 0);
x_116 = lean_ctor_get(x_31, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_31);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
}
else
{
lean_dec(x_26);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_25;
}
}
block_24:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_getGoal___redArg(x_10, x_11);
lean_dec(x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_solve_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_solve_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___Lean_Meta_Grind_solve_spec__0___redArg___lam__0), 9, 4);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_5);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_solve_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_solve_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_solve___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_st_mk_ref(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
lean_inc(x_11);
x_13 = l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_st_ref_get(x_11, x_16);
lean_dec(x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_ctor_set(x_17, 1, x_19);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_13, 1, x_20);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_st_ref_get(x_11, x_25);
lean_dec(x_11);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_11);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
return x_13;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_solve(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_solve___lam__0), 9, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_solve_spec__0___redArg(x_10, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
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
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_SearchM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Split(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_EMatch(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Lookahead(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Intro(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Solve(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_SearchM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Split(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_EMatch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Lookahead(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
