// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Solve
// Imports: public import Lean.Meta.Tactic.Grind.SearchM import Lean.Meta.Tactic.Grind.Split import Lean.Meta.Tactic.Grind.EMatch import Lean.Meta.Tactic.Grind.Lookahead import Lean.Meta.Tactic.Grind.Intro
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
uint8_t l_Lean_Exception_isMaxHeartbeat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtcStep___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ematchStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSolvers___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isMaxRecDepth(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Meta_Grind_splitNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtcStep___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Solvers_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_solve_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookaheadStep___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_solve___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Solvers_mbtc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Meta_Grind_checkSolvers_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtcStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSolvers___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSolvers___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_ematchStep___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Meta_Grind_checkSolvers_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_solve_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_lookahead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_ematchStep___closed__2;
lean_object* l_Lean_Meta_Grind_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSolvers___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSolvers___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSolvers___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGoal___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_solve___closed__0;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_ematchStep___closed__0;
lean_object* l_Lean_Meta_Grind_assertAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ematch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookaheadStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop___closed__0;
lean_object* l_Lean_Meta_Grind_Solvers_check_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ematchStep___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSolvers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_Grind_nextGoal_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ematchStep___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookaheadStep___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg___lam__0), 10, 5);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Meta_Grind_checkSolvers_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSolvers___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSolvers___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSolvers___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_17 = l_Lean_Meta_Grind_Solvers_check_x3f(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSolvers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_getGoal___redArg(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_checkSolvers___lam__0___boxed), 9, 0);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg(x_13, x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_st_ref_take(x_1, x_17);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
lean_ctor_set(x_21, 0, x_19);
x_25 = lean_st_ref_set(x_1, x_21, x_22);
x_26 = lean_ctor_get_uint8(x_18, sizeof(void*)*8);
lean_dec(x_18);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = l_Lean_Meta_Grind_getGoal___redArg(x_1, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_checkSolvers___lam__1___boxed), 9, 0);
lean_inc(x_1);
x_33 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg(x_31, x_32, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_st_ref_take(x_1, x_36);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_40, 0);
lean_dec(x_43);
lean_ctor_set(x_40, 0, x_38);
x_44 = lean_st_ref_set(x_1, x_40, x_41);
lean_dec(x_1);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec_ref(x_44);
lean_ctor_set(x_33, 1, x_45);
lean_ctor_set(x_33, 0, x_37);
return x_33;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_40, 1);
x_47 = lean_ctor_get(x_40, 2);
x_48 = lean_ctor_get(x_40, 3);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_40);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_38);
lean_ctor_set(x_49, 1, x_46);
lean_ctor_set(x_49, 2, x_47);
lean_ctor_set(x_49, 3, x_48);
x_50 = lean_st_ref_set(x_1, x_49, x_41);
lean_dec(x_1);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec_ref(x_50);
lean_ctor_set(x_33, 1, x_51);
lean_ctor_set(x_33, 0, x_37);
return x_33;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_52 = lean_ctor_get(x_33, 0);
x_53 = lean_ctor_get(x_33, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_33);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_st_ref_take(x_1, x_53);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec_ref(x_56);
x_59 = lean_ctor_get(x_57, 1);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_57, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 3);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 4, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_55);
lean_ctor_set(x_63, 1, x_59);
lean_ctor_set(x_63, 2, x_60);
lean_ctor_set(x_63, 3, x_61);
x_64 = lean_st_ref_set(x_1, x_63, x_58);
lean_dec(x_1);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_54);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_33);
if (x_67 == 0)
{
return x_33;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_33, 0);
x_69 = lean_ctor_get(x_33, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_33);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_28);
if (x_71 == 0)
{
return x_28;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_28, 0);
x_73 = lean_ctor_get(x_28, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_28);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_25, 1);
lean_inc(x_75);
lean_dec_ref(x_25);
x_76 = l_Lean_Meta_Grind_getGoal___redArg(x_1, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec_ref(x_76);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_checkSolvers___lam__2___boxed), 9, 0);
lean_inc(x_1);
x_81 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg(x_79, x_80, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_78);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = lean_ctor_get(x_81, 1);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
x_87 = lean_st_ref_take(x_1, x_84);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec_ref(x_87);
x_90 = !lean_is_exclusive(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_88, 0);
lean_dec(x_91);
lean_ctor_set(x_88, 0, x_86);
x_92 = lean_st_ref_set(x_1, x_88, x_89);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_93; uint8_t x_94; lean_object* x_95; 
lean_dec(x_1);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec_ref(x_92);
x_94 = 0;
x_95 = lean_box(x_94);
lean_ctor_set(x_81, 1, x_93);
lean_ctor_set(x_81, 0, x_95);
return x_81;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_dec_ref(x_92);
x_97 = lean_ctor_get(x_85, 0);
lean_inc(x_97);
lean_dec_ref(x_85);
x_98 = lean_st_ref_take(x_1, x_96);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec_ref(x_98);
x_101 = !lean_is_exclusive(x_99);
if (x_101 == 0)
{
lean_object* x_102; size_t x_103; size_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_ctor_get(x_99, 1);
x_103 = lean_array_size(x_97);
x_104 = 0;
x_105 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Meta_Grind_checkSolvers_spec__1(x_103, x_104, x_97);
x_106 = l_Array_append___redArg(x_102, x_105);
lean_dec_ref(x_105);
lean_ctor_set(x_99, 1, x_106);
x_107 = lean_st_ref_set(x_1, x_99, x_100);
lean_dec(x_1);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = lean_box(x_26);
lean_ctor_set(x_81, 1, x_108);
lean_ctor_set(x_81, 0, x_109);
return x_81;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; size_t x_114; size_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_110 = lean_ctor_get(x_99, 0);
x_111 = lean_ctor_get(x_99, 1);
x_112 = lean_ctor_get(x_99, 2);
x_113 = lean_ctor_get(x_99, 3);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_99);
x_114 = lean_array_size(x_97);
x_115 = 0;
x_116 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Meta_Grind_checkSolvers_spec__1(x_114, x_115, x_97);
x_117 = l_Array_append___redArg(x_111, x_116);
lean_dec_ref(x_116);
x_118 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_118, 0, x_110);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_118, 2, x_112);
lean_ctor_set(x_118, 3, x_113);
x_119 = lean_st_ref_set(x_1, x_118, x_100);
lean_dec(x_1);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec_ref(x_119);
x_121 = lean_box(x_26);
lean_ctor_set(x_81, 1, x_120);
lean_ctor_set(x_81, 0, x_121);
return x_81;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_88, 1);
x_123 = lean_ctor_get(x_88, 2);
x_124 = lean_ctor_get(x_88, 3);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_88);
x_125 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_125, 0, x_86);
lean_ctor_set(x_125, 1, x_122);
lean_ctor_set(x_125, 2, x_123);
lean_ctor_set(x_125, 3, x_124);
x_126 = lean_st_ref_set(x_1, x_125, x_89);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_127; uint8_t x_128; lean_object* x_129; 
lean_dec(x_1);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec_ref(x_126);
x_128 = 0;
x_129 = lean_box(x_128);
lean_ctor_set(x_81, 1, x_127);
lean_ctor_set(x_81, 0, x_129);
return x_81;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; size_t x_140; size_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_130 = lean_ctor_get(x_126, 1);
lean_inc(x_130);
lean_dec_ref(x_126);
x_131 = lean_ctor_get(x_85, 0);
lean_inc(x_131);
lean_dec_ref(x_85);
x_132 = lean_st_ref_take(x_1, x_130);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec_ref(x_132);
x_135 = lean_ctor_get(x_133, 0);
lean_inc_ref(x_135);
x_136 = lean_ctor_get(x_133, 1);
lean_inc_ref(x_136);
x_137 = lean_ctor_get(x_133, 2);
lean_inc(x_137);
x_138 = lean_ctor_get(x_133, 3);
lean_inc(x_138);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 lean_ctor_release(x_133, 2);
 lean_ctor_release(x_133, 3);
 x_139 = x_133;
} else {
 lean_dec_ref(x_133);
 x_139 = lean_box(0);
}
x_140 = lean_array_size(x_131);
x_141 = 0;
x_142 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Meta_Grind_checkSolvers_spec__1(x_140, x_141, x_131);
x_143 = l_Array_append___redArg(x_136, x_142);
lean_dec_ref(x_142);
if (lean_is_scalar(x_139)) {
 x_144 = lean_alloc_ctor(0, 4, 0);
} else {
 x_144 = x_139;
}
lean_ctor_set(x_144, 0, x_135);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set(x_144, 2, x_137);
lean_ctor_set(x_144, 3, x_138);
x_145 = lean_st_ref_set(x_1, x_144, x_134);
lean_dec(x_1);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec_ref(x_145);
x_147 = lean_box(x_26);
lean_ctor_set(x_81, 1, x_146);
lean_ctor_set(x_81, 0, x_147);
return x_81;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_148 = lean_ctor_get(x_81, 0);
x_149 = lean_ctor_get(x_81, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_81);
x_150 = lean_ctor_get(x_148, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_151);
lean_dec(x_148);
x_152 = lean_st_ref_take(x_1, x_149);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec_ref(x_152);
x_155 = lean_ctor_get(x_153, 1);
lean_inc_ref(x_155);
x_156 = lean_ctor_get(x_153, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_153, 3);
lean_inc(x_157);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 lean_ctor_release(x_153, 2);
 lean_ctor_release(x_153, 3);
 x_158 = x_153;
} else {
 lean_dec_ref(x_153);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(0, 4, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_151);
lean_ctor_set(x_159, 1, x_155);
lean_ctor_set(x_159, 2, x_156);
lean_ctor_set(x_159, 3, x_157);
x_160 = lean_st_ref_set(x_1, x_159, x_154);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_1);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec_ref(x_160);
x_162 = 0;
x_163 = lean_box(x_162);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_161);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; size_t x_175; size_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
lean_dec_ref(x_160);
x_166 = lean_ctor_get(x_150, 0);
lean_inc(x_166);
lean_dec_ref(x_150);
x_167 = lean_st_ref_take(x_1, x_165);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec_ref(x_167);
x_170 = lean_ctor_get(x_168, 0);
lean_inc_ref(x_170);
x_171 = lean_ctor_get(x_168, 1);
lean_inc_ref(x_171);
x_172 = lean_ctor_get(x_168, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_168, 3);
lean_inc(x_173);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 lean_ctor_release(x_168, 2);
 lean_ctor_release(x_168, 3);
 x_174 = x_168;
} else {
 lean_dec_ref(x_168);
 x_174 = lean_box(0);
}
x_175 = lean_array_size(x_166);
x_176 = 0;
x_177 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Meta_Grind_checkSolvers_spec__1(x_175, x_176, x_166);
x_178 = l_Array_append___redArg(x_171, x_177);
lean_dec_ref(x_177);
if (lean_is_scalar(x_174)) {
 x_179 = lean_alloc_ctor(0, 4, 0);
} else {
 x_179 = x_174;
}
lean_ctor_set(x_179, 0, x_170);
lean_ctor_set(x_179, 1, x_178);
lean_ctor_set(x_179, 2, x_172);
lean_ctor_set(x_179, 3, x_173);
x_180 = lean_st_ref_set(x_1, x_179, x_169);
lean_dec(x_1);
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
lean_dec_ref(x_180);
x_182 = lean_box(x_26);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_1);
x_184 = !lean_is_exclusive(x_81);
if (x_184 == 0)
{
return x_81;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_81, 0);
x_186 = lean_ctor_get(x_81, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_81);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_188 = !lean_is_exclusive(x_76);
if (x_188 == 0)
{
return x_76;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_76, 0);
x_190 = lean_ctor_get(x_76, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_76);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_192 = lean_ctor_get(x_21, 1);
x_193 = lean_ctor_get(x_21, 2);
x_194 = lean_ctor_get(x_21, 3);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_21);
x_195 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_195, 0, x_19);
lean_ctor_set(x_195, 1, x_192);
lean_ctor_set(x_195, 2, x_193);
lean_ctor_set(x_195, 3, x_194);
x_196 = lean_st_ref_set(x_1, x_195, x_22);
x_197 = lean_ctor_get_uint8(x_18, sizeof(void*)*8);
lean_dec(x_18);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; 
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec_ref(x_196);
x_199 = l_Lean_Meta_Grind_getGoal___redArg(x_1, x_198);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec_ref(x_199);
x_202 = lean_ctor_get(x_200, 0);
lean_inc(x_202);
lean_dec(x_200);
x_203 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_checkSolvers___lam__1___boxed), 9, 0);
lean_inc(x_1);
x_204 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg(x_202, x_203, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_201);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_207 = x_204;
} else {
 lean_dec_ref(x_204);
 x_207 = lean_box(0);
}
x_208 = lean_ctor_get(x_205, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_205, 1);
lean_inc(x_209);
lean_dec(x_205);
x_210 = lean_st_ref_take(x_1, x_206);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec_ref(x_210);
x_213 = lean_ctor_get(x_211, 1);
lean_inc_ref(x_213);
x_214 = lean_ctor_get(x_211, 2);
lean_inc(x_214);
x_215 = lean_ctor_get(x_211, 3);
lean_inc(x_215);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 lean_ctor_release(x_211, 2);
 lean_ctor_release(x_211, 3);
 x_216 = x_211;
} else {
 lean_dec_ref(x_211);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(0, 4, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_209);
lean_ctor_set(x_217, 1, x_213);
lean_ctor_set(x_217, 2, x_214);
lean_ctor_set(x_217, 3, x_215);
x_218 = lean_st_ref_set(x_1, x_217, x_212);
lean_dec(x_1);
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec_ref(x_218);
if (lean_is_scalar(x_207)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_207;
}
lean_ctor_set(x_220, 0, x_208);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_1);
x_221 = lean_ctor_get(x_204, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_204, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_223 = x_204;
} else {
 lean_dec_ref(x_204);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(1, 2, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_222);
return x_224;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_225 = lean_ctor_get(x_199, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_199, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_227 = x_199;
} else {
 lean_dec_ref(x_199);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
}
else
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_196, 1);
lean_inc(x_229);
lean_dec_ref(x_196);
x_230 = l_Lean_Meta_Grind_getGoal___redArg(x_1, x_229);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec_ref(x_230);
x_233 = lean_ctor_get(x_231, 0);
lean_inc(x_233);
lean_dec(x_231);
x_234 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_checkSolvers___lam__2___boxed), 9, 0);
lean_inc(x_1);
x_235 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg(x_233, x_234, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_232);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
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
x_239 = lean_ctor_get(x_236, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_236, 1);
lean_inc(x_240);
lean_dec(x_236);
x_241 = lean_st_ref_take(x_1, x_237);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec_ref(x_241);
x_244 = lean_ctor_get(x_242, 1);
lean_inc_ref(x_244);
x_245 = lean_ctor_get(x_242, 2);
lean_inc(x_245);
x_246 = lean_ctor_get(x_242, 3);
lean_inc(x_246);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 lean_ctor_release(x_242, 2);
 lean_ctor_release(x_242, 3);
 x_247 = x_242;
} else {
 lean_dec_ref(x_242);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(0, 4, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_240);
lean_ctor_set(x_248, 1, x_244);
lean_ctor_set(x_248, 2, x_245);
lean_ctor_set(x_248, 3, x_246);
x_249 = lean_st_ref_set(x_1, x_248, x_243);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_1);
x_250 = lean_ctor_get(x_249, 1);
lean_inc(x_250);
lean_dec_ref(x_249);
x_251 = 0;
x_252 = lean_box(x_251);
if (lean_is_scalar(x_238)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_238;
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_250);
return x_253;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; size_t x_264; size_t x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_254 = lean_ctor_get(x_249, 1);
lean_inc(x_254);
lean_dec_ref(x_249);
x_255 = lean_ctor_get(x_239, 0);
lean_inc(x_255);
lean_dec_ref(x_239);
x_256 = lean_st_ref_take(x_1, x_254);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec_ref(x_256);
x_259 = lean_ctor_get(x_257, 0);
lean_inc_ref(x_259);
x_260 = lean_ctor_get(x_257, 1);
lean_inc_ref(x_260);
x_261 = lean_ctor_get(x_257, 2);
lean_inc(x_261);
x_262 = lean_ctor_get(x_257, 3);
lean_inc(x_262);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 lean_ctor_release(x_257, 2);
 lean_ctor_release(x_257, 3);
 x_263 = x_257;
} else {
 lean_dec_ref(x_257);
 x_263 = lean_box(0);
}
x_264 = lean_array_size(x_255);
x_265 = 0;
x_266 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Meta_Grind_checkSolvers_spec__1(x_264, x_265, x_255);
x_267 = l_Array_append___redArg(x_260, x_266);
lean_dec_ref(x_266);
if (lean_is_scalar(x_263)) {
 x_268 = lean_alloc_ctor(0, 4, 0);
} else {
 x_268 = x_263;
}
lean_ctor_set(x_268, 0, x_259);
lean_ctor_set(x_268, 1, x_267);
lean_ctor_set(x_268, 2, x_261);
lean_ctor_set(x_268, 3, x_262);
x_269 = lean_st_ref_set(x_1, x_268, x_258);
lean_dec(x_1);
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
lean_dec_ref(x_269);
x_271 = lean_box(x_197);
if (lean_is_scalar(x_238)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_238;
}
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_270);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_1);
x_273 = lean_ctor_get(x_235, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_235, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_275 = x_235;
} else {
 lean_dec_ref(x_235);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_277 = lean_ctor_get(x_230, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_230, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_279 = x_230;
} else {
 lean_dec_ref(x_230);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(1, 2, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_277);
lean_ctor_set(x_280, 1, x_278);
return x_280;
}
}
}
}
else
{
uint8_t x_281; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_281 = !lean_is_exclusive(x_15);
if (x_281 == 0)
{
return x_15;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_15, 0);
x_283 = lean_ctor_get(x_15, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_15);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
}
else
{
uint8_t x_285; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_285 = !lean_is_exclusive(x_10);
if (x_285 == 0)
{
return x_10;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_10, 0);
x_287 = lean_ctor_get(x_10, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_10);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
return x_288;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Meta_Grind_checkSolvers_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Meta_Grind_checkSolvers_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSolvers___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_checkSolvers___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSolvers___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_checkSolvers___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkSolvers___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_checkSolvers___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ematchStep___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_inc(x_16);
x_18 = l_Lean_Meta_Grind_ematch(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
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
static lean_object* _init_l_Lean_Meta_Grind_ematchStep___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_checkSolvers___lam__0___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ematchStep___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ematchStep___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ematchStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_getGoal___redArg(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_Grind_ematchStep___closed__0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg(x_13, x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_st_ref_take(x_1, x_17);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
lean_ctor_set(x_21, 0, x_19);
x_25 = lean_st_ref_set(x_1, x_21, x_22);
x_26 = lean_ctor_get_uint8(x_18, sizeof(void*)*8);
lean_dec(x_18);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = l_Lean_Meta_Grind_getGoal___redArg(x_1, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Meta_Grind_ematchStep___closed__1;
x_33 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_ematchStep___lam__1___boxed), 10, 1);
lean_closure_set(x_33, 0, x_32);
lean_inc(x_1);
x_34 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg(x_31, x_33, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
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
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_41, 0);
lean_dec(x_44);
lean_ctor_set(x_41, 0, x_39);
x_45 = lean_st_ref_set(x_1, x_41, x_42);
lean_dec(x_1);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec_ref(x_45);
lean_ctor_set(x_34, 1, x_46);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_41, 1);
x_48 = lean_ctor_get(x_41, 2);
x_49 = lean_ctor_get(x_41, 3);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_41);
x_50 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_50, 0, x_39);
lean_ctor_set(x_50, 1, x_47);
lean_ctor_set(x_50, 2, x_48);
lean_ctor_set(x_50, 3, x_49);
x_51 = lean_st_ref_set(x_1, x_50, x_42);
lean_dec(x_1);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec_ref(x_51);
lean_ctor_set(x_34, 1, x_52);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_53 = lean_ctor_get(x_34, 0);
x_54 = lean_ctor_get(x_34, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_34);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_st_ref_take(x_1, x_54);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec_ref(x_57);
x_60 = lean_ctor_get(x_58, 1);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_58, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_58, 3);
lean_inc(x_62);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 x_63 = x_58;
} else {
 lean_dec_ref(x_58);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 4, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_56);
lean_ctor_set(x_64, 1, x_60);
lean_ctor_set(x_64, 2, x_61);
lean_ctor_set(x_64, 3, x_62);
x_65 = lean_st_ref_set(x_1, x_64, x_59);
lean_dec(x_1);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec_ref(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_55);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_34);
if (x_68 == 0)
{
return x_34;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_34, 0);
x_70 = lean_ctor_get(x_34, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_34);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_28);
if (x_72 == 0)
{
return x_28;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_28, 0);
x_74 = lean_ctor_get(x_28, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_28);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_25, 1);
lean_inc(x_76);
lean_dec_ref(x_25);
x_77 = l_Lean_Meta_Grind_getGoal___redArg(x_1, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec_ref(x_77);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Meta_Grind_ematchStep___closed__1;
x_82 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_ematchStep___lam__1___boxed), 10, 1);
lean_closure_set(x_82, 0, x_81);
lean_inc(x_1);
x_83 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg(x_80, x_82, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_79);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_85 = lean_ctor_get(x_83, 0);
x_86 = lean_ctor_get(x_83, 1);
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = lean_st_ref_take(x_1, x_86);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec_ref(x_89);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_90, 0);
lean_dec(x_93);
lean_ctor_set(x_90, 0, x_88);
x_94 = lean_st_ref_set(x_1, x_90, x_91);
x_95 = lean_unbox(x_87);
if (x_95 == 0)
{
lean_object* x_96; 
lean_dec(x_1);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec_ref(x_94);
lean_ctor_set(x_83, 1, x_96);
lean_ctor_set(x_83, 0, x_87);
return x_83;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec_ref(x_94);
x_98 = lean_st_ref_take(x_1, x_97);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec_ref(x_98);
x_101 = !lean_is_exclusive(x_99);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_99, 1);
x_103 = l_Lean_Meta_Grind_ematchStep___closed__2;
x_104 = lean_array_push(x_102, x_103);
lean_ctor_set(x_99, 1, x_104);
x_105 = lean_st_ref_set(x_1, x_99, x_100);
lean_dec(x_1);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec_ref(x_105);
lean_ctor_set(x_83, 1, x_106);
lean_ctor_set(x_83, 0, x_87);
return x_83;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_107 = lean_ctor_get(x_99, 0);
x_108 = lean_ctor_get(x_99, 1);
x_109 = lean_ctor_get(x_99, 2);
x_110 = lean_ctor_get(x_99, 3);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_99);
x_111 = l_Lean_Meta_Grind_ematchStep___closed__2;
x_112 = lean_array_push(x_108, x_111);
x_113 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set(x_113, 2, x_109);
lean_ctor_set(x_113, 3, x_110);
x_114 = lean_st_ref_set(x_1, x_113, x_100);
lean_dec(x_1);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec_ref(x_114);
lean_ctor_set(x_83, 1, x_115);
lean_ctor_set(x_83, 0, x_87);
return x_83;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_116 = lean_ctor_get(x_90, 1);
x_117 = lean_ctor_get(x_90, 2);
x_118 = lean_ctor_get(x_90, 3);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_90);
x_119 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_119, 0, x_88);
lean_ctor_set(x_119, 1, x_116);
lean_ctor_set(x_119, 2, x_117);
lean_ctor_set(x_119, 3, x_118);
x_120 = lean_st_ref_set(x_1, x_119, x_91);
x_121 = lean_unbox(x_87);
if (x_121 == 0)
{
lean_object* x_122; 
lean_dec(x_1);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec_ref(x_120);
lean_ctor_set(x_83, 1, x_122);
lean_ctor_set(x_83, 0, x_87);
return x_83;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec_ref(x_120);
x_124 = lean_st_ref_take(x_1, x_123);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec_ref(x_124);
x_127 = lean_ctor_get(x_125, 0);
lean_inc_ref(x_127);
x_128 = lean_ctor_get(x_125, 1);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_125, 2);
lean_inc(x_129);
x_130 = lean_ctor_get(x_125, 3);
lean_inc(x_130);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 lean_ctor_release(x_125, 2);
 lean_ctor_release(x_125, 3);
 x_131 = x_125;
} else {
 lean_dec_ref(x_125);
 x_131 = lean_box(0);
}
x_132 = l_Lean_Meta_Grind_ematchStep___closed__2;
x_133 = lean_array_push(x_128, x_132);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 4, 0);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_127);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_134, 2, x_129);
lean_ctor_set(x_134, 3, x_130);
x_135 = lean_st_ref_set(x_1, x_134, x_126);
lean_dec(x_1);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec_ref(x_135);
lean_ctor_set(x_83, 1, x_136);
lean_ctor_set(x_83, 0, x_87);
return x_83;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_137 = lean_ctor_get(x_83, 0);
x_138 = lean_ctor_get(x_83, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_83);
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec(x_137);
x_141 = lean_st_ref_take(x_1, x_138);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec_ref(x_141);
x_144 = lean_ctor_get(x_142, 1);
lean_inc_ref(x_144);
x_145 = lean_ctor_get(x_142, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_142, 3);
lean_inc(x_146);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 lean_ctor_release(x_142, 2);
 lean_ctor_release(x_142, 3);
 x_147 = x_142;
} else {
 lean_dec_ref(x_142);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(0, 4, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_140);
lean_ctor_set(x_148, 1, x_144);
lean_ctor_set(x_148, 2, x_145);
lean_ctor_set(x_148, 3, x_146);
x_149 = lean_st_ref_set(x_1, x_148, x_143);
x_150 = lean_unbox(x_139);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_1);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec_ref(x_149);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_139);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_153 = lean_ctor_get(x_149, 1);
lean_inc(x_153);
lean_dec_ref(x_149);
x_154 = lean_st_ref_take(x_1, x_153);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec_ref(x_154);
x_157 = lean_ctor_get(x_155, 0);
lean_inc_ref(x_157);
x_158 = lean_ctor_get(x_155, 1);
lean_inc_ref(x_158);
x_159 = lean_ctor_get(x_155, 2);
lean_inc(x_159);
x_160 = lean_ctor_get(x_155, 3);
lean_inc(x_160);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 lean_ctor_release(x_155, 2);
 lean_ctor_release(x_155, 3);
 x_161 = x_155;
} else {
 lean_dec_ref(x_155);
 x_161 = lean_box(0);
}
x_162 = l_Lean_Meta_Grind_ematchStep___closed__2;
x_163 = lean_array_push(x_158, x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 4, 0);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_157);
lean_ctor_set(x_164, 1, x_163);
lean_ctor_set(x_164, 2, x_159);
lean_ctor_set(x_164, 3, x_160);
x_165 = lean_st_ref_set(x_1, x_164, x_156);
lean_dec(x_1);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec_ref(x_165);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_139);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
else
{
uint8_t x_168; 
lean_dec(x_1);
x_168 = !lean_is_exclusive(x_83);
if (x_168 == 0)
{
return x_83;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_83, 0);
x_170 = lean_ctor_get(x_83, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_83);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
uint8_t x_172; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_172 = !lean_is_exclusive(x_77);
if (x_172 == 0)
{
return x_77;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_77, 0);
x_174 = lean_ctor_get(x_77, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_77);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_176 = lean_ctor_get(x_21, 1);
x_177 = lean_ctor_get(x_21, 2);
x_178 = lean_ctor_get(x_21, 3);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_21);
x_179 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_179, 0, x_19);
lean_ctor_set(x_179, 1, x_176);
lean_ctor_set(x_179, 2, x_177);
lean_ctor_set(x_179, 3, x_178);
x_180 = lean_st_ref_set(x_1, x_179, x_22);
x_181 = lean_ctor_get_uint8(x_18, sizeof(void*)*8);
lean_dec(x_18);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec_ref(x_180);
x_183 = l_Lean_Meta_Grind_getGoal___redArg(x_1, x_182);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec_ref(x_183);
x_186 = lean_ctor_get(x_184, 0);
lean_inc(x_186);
lean_dec(x_184);
x_187 = l_Lean_Meta_Grind_ematchStep___closed__1;
x_188 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_ematchStep___lam__1___boxed), 10, 1);
lean_closure_set(x_188, 0, x_187);
lean_inc(x_1);
x_189 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg(x_186, x_188, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_185);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_192 = x_189;
} else {
 lean_dec_ref(x_189);
 x_192 = lean_box(0);
}
x_193 = lean_ctor_get(x_190, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_190, 1);
lean_inc(x_194);
lean_dec(x_190);
x_195 = lean_st_ref_take(x_1, x_191);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec_ref(x_195);
x_198 = lean_ctor_get(x_196, 1);
lean_inc_ref(x_198);
x_199 = lean_ctor_get(x_196, 2);
lean_inc(x_199);
x_200 = lean_ctor_get(x_196, 3);
lean_inc(x_200);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 lean_ctor_release(x_196, 3);
 x_201 = x_196;
} else {
 lean_dec_ref(x_196);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(0, 4, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_194);
lean_ctor_set(x_202, 1, x_198);
lean_ctor_set(x_202, 2, x_199);
lean_ctor_set(x_202, 3, x_200);
x_203 = lean_st_ref_set(x_1, x_202, x_197);
lean_dec(x_1);
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
lean_dec_ref(x_203);
if (lean_is_scalar(x_192)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_192;
}
lean_ctor_set(x_205, 0, x_193);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_1);
x_206 = lean_ctor_get(x_189, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_189, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_208 = x_189;
} else {
 lean_dec_ref(x_189);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_210 = lean_ctor_get(x_183, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_183, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_212 = x_183;
} else {
 lean_dec_ref(x_183);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_180, 1);
lean_inc(x_214);
lean_dec_ref(x_180);
x_215 = l_Lean_Meta_Grind_getGoal___redArg(x_1, x_214);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec_ref(x_215);
x_218 = lean_ctor_get(x_216, 0);
lean_inc(x_218);
lean_dec(x_216);
x_219 = l_Lean_Meta_Grind_ematchStep___closed__1;
x_220 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_ematchStep___lam__1___boxed), 10, 1);
lean_closure_set(x_220, 0, x_219);
lean_inc(x_1);
x_221 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg(x_218, x_220, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_217);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_224 = x_221;
} else {
 lean_dec_ref(x_221);
 x_224 = lean_box(0);
}
x_225 = lean_ctor_get(x_222, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_222, 1);
lean_inc(x_226);
lean_dec(x_222);
x_227 = lean_st_ref_take(x_1, x_223);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec_ref(x_227);
x_230 = lean_ctor_get(x_228, 1);
lean_inc_ref(x_230);
x_231 = lean_ctor_get(x_228, 2);
lean_inc(x_231);
x_232 = lean_ctor_get(x_228, 3);
lean_inc(x_232);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 lean_ctor_release(x_228, 2);
 lean_ctor_release(x_228, 3);
 x_233 = x_228;
} else {
 lean_dec_ref(x_228);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(0, 4, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_226);
lean_ctor_set(x_234, 1, x_230);
lean_ctor_set(x_234, 2, x_231);
lean_ctor_set(x_234, 3, x_232);
x_235 = lean_st_ref_set(x_1, x_234, x_229);
x_236 = lean_unbox(x_225);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; 
lean_dec(x_1);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec_ref(x_235);
if (lean_is_scalar(x_224)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_224;
}
lean_ctor_set(x_238, 0, x_225);
lean_ctor_set(x_238, 1, x_237);
return x_238;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_239 = lean_ctor_get(x_235, 1);
lean_inc(x_239);
lean_dec_ref(x_235);
x_240 = lean_st_ref_take(x_1, x_239);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec_ref(x_240);
x_243 = lean_ctor_get(x_241, 0);
lean_inc_ref(x_243);
x_244 = lean_ctor_get(x_241, 1);
lean_inc_ref(x_244);
x_245 = lean_ctor_get(x_241, 2);
lean_inc(x_245);
x_246 = lean_ctor_get(x_241, 3);
lean_inc(x_246);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 lean_ctor_release(x_241, 2);
 lean_ctor_release(x_241, 3);
 x_247 = x_241;
} else {
 lean_dec_ref(x_241);
 x_247 = lean_box(0);
}
x_248 = l_Lean_Meta_Grind_ematchStep___closed__2;
x_249 = lean_array_push(x_244, x_248);
if (lean_is_scalar(x_247)) {
 x_250 = lean_alloc_ctor(0, 4, 0);
} else {
 x_250 = x_247;
}
lean_ctor_set(x_250, 0, x_243);
lean_ctor_set(x_250, 1, x_249);
lean_ctor_set(x_250, 2, x_245);
lean_ctor_set(x_250, 3, x_246);
x_251 = lean_st_ref_set(x_1, x_250, x_242);
lean_dec(x_1);
x_252 = lean_ctor_get(x_251, 1);
lean_inc(x_252);
lean_dec_ref(x_251);
if (lean_is_scalar(x_224)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_224;
}
lean_ctor_set(x_253, 0, x_225);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_1);
x_254 = lean_ctor_get(x_221, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_221, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_256 = x_221;
} else {
 lean_dec_ref(x_221);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_258 = lean_ctor_get(x_215, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_215, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_260 = x_215;
} else {
 lean_dec_ref(x_215);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_259);
return x_261;
}
}
}
}
else
{
uint8_t x_262; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_262 = !lean_is_exclusive(x_15);
if (x_262 == 0)
{
return x_15;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_15, 0);
x_264 = lean_ctor_get(x_15, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_15);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
else
{
uint8_t x_266; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_266 = !lean_is_exclusive(x_10);
if (x_266 == 0)
{
return x_10;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_10, 0);
x_268 = lean_ctor_get(x_10, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_10);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ematchStep___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_ematchStep___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtcStep___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtcStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_getGoal___redArg(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mbtcStep___lam__0___boxed), 9, 0);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg(x_13, x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_st_ref_take(x_1, x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
lean_ctor_set(x_22, 0, x_20);
x_26 = lean_st_ref_set(x_1, x_22, x_23);
x_27 = lean_unbox(x_19);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
lean_ctor_set(x_15, 1, x_28);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_free_object(x_15);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec_ref(x_26);
x_30 = l_Lean_Meta_Grind_getGoal___redArg(x_1, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_Grind_ematchStep___closed__0;
lean_inc(x_1);
x_35 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg(x_33, x_34, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_st_ref_take(x_1, x_38);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_42, 0);
lean_dec(x_45);
lean_ctor_set(x_42, 0, x_40);
x_46 = lean_st_ref_set(x_1, x_42, x_43);
x_47 = lean_ctor_get_uint8(x_39, sizeof(void*)*8);
lean_dec(x_39);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_1);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
lean_ctor_set(x_35, 1, x_48);
lean_ctor_set(x_35, 0, x_19);
return x_35;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec_ref(x_46);
x_50 = lean_st_ref_take(x_1, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_51, 1);
x_55 = lean_box(2);
x_56 = lean_array_push(x_54, x_55);
lean_ctor_set(x_51, 1, x_56);
x_57 = lean_st_ref_set(x_1, x_51, x_52);
lean_dec(x_1);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec_ref(x_57);
lean_ctor_set(x_35, 1, x_58);
lean_ctor_set(x_35, 0, x_19);
return x_35;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_51, 0);
x_60 = lean_ctor_get(x_51, 1);
x_61 = lean_ctor_get(x_51, 2);
x_62 = lean_ctor_get(x_51, 3);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_51);
x_63 = lean_box(2);
x_64 = lean_array_push(x_60, x_63);
x_65 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_61);
lean_ctor_set(x_65, 3, x_62);
x_66 = lean_st_ref_set(x_1, x_65, x_52);
lean_dec(x_1);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec_ref(x_66);
lean_ctor_set(x_35, 1, x_67);
lean_ctor_set(x_35, 0, x_19);
return x_35;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_68 = lean_ctor_get(x_42, 1);
x_69 = lean_ctor_get(x_42, 2);
x_70 = lean_ctor_get(x_42, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_42);
x_71 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_71, 0, x_40);
lean_ctor_set(x_71, 1, x_68);
lean_ctor_set(x_71, 2, x_69);
lean_ctor_set(x_71, 3, x_70);
x_72 = lean_st_ref_set(x_1, x_71, x_43);
x_73 = lean_ctor_get_uint8(x_39, sizeof(void*)*8);
lean_dec(x_39);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_1);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec_ref(x_72);
lean_ctor_set(x_35, 1, x_74);
lean_ctor_set(x_35, 0, x_19);
return x_35;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec_ref(x_72);
x_76 = lean_st_ref_take(x_1, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec_ref(x_76);
x_79 = lean_ctor_get(x_77, 0);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_77, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_77, 3);
lean_inc(x_82);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 lean_ctor_release(x_77, 3);
 x_83 = x_77;
} else {
 lean_dec_ref(x_77);
 x_83 = lean_box(0);
}
x_84 = lean_box(2);
x_85 = lean_array_push(x_80, x_84);
if (lean_is_scalar(x_83)) {
 x_86 = lean_alloc_ctor(0, 4, 0);
} else {
 x_86 = x_83;
}
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_86, 2, x_81);
lean_ctor_set(x_86, 3, x_82);
x_87 = lean_st_ref_set(x_1, x_86, x_78);
lean_dec(x_1);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec_ref(x_87);
lean_ctor_set(x_35, 1, x_88);
lean_ctor_set(x_35, 0, x_19);
return x_35;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_89 = lean_ctor_get(x_35, 0);
x_90 = lean_ctor_get(x_35, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_35);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = lean_st_ref_take(x_1, x_90);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec_ref(x_93);
x_96 = lean_ctor_get(x_94, 1);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_94, 2);
lean_inc(x_97);
x_98 = lean_ctor_get(x_94, 3);
lean_inc(x_98);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 lean_ctor_release(x_94, 2);
 lean_ctor_release(x_94, 3);
 x_99 = x_94;
} else {
 lean_dec_ref(x_94);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 4, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_92);
lean_ctor_set(x_100, 1, x_96);
lean_ctor_set(x_100, 2, x_97);
lean_ctor_set(x_100, 3, x_98);
x_101 = lean_st_ref_set(x_1, x_100, x_95);
x_102 = lean_ctor_get_uint8(x_91, sizeof(void*)*8);
lean_dec(x_91);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_1);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec_ref(x_101);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_19);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_105 = lean_ctor_get(x_101, 1);
lean_inc(x_105);
lean_dec_ref(x_101);
x_106 = lean_st_ref_take(x_1, x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec_ref(x_106);
x_109 = lean_ctor_get(x_107, 0);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_107, 1);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_107, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_107, 3);
lean_inc(x_112);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 lean_ctor_release(x_107, 2);
 lean_ctor_release(x_107, 3);
 x_113 = x_107;
} else {
 lean_dec_ref(x_107);
 x_113 = lean_box(0);
}
x_114 = lean_box(2);
x_115 = lean_array_push(x_110, x_114);
if (lean_is_scalar(x_113)) {
 x_116 = lean_alloc_ctor(0, 4, 0);
} else {
 x_116 = x_113;
}
lean_ctor_set(x_116, 0, x_109);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set(x_116, 2, x_111);
lean_ctor_set(x_116, 3, x_112);
x_117 = lean_st_ref_set(x_1, x_116, x_108);
lean_dec(x_1);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec_ref(x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_19);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_19);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_35);
if (x_120 == 0)
{
return x_35;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_35, 0);
x_122 = lean_ctor_get(x_35, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_35);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_30);
if (x_124 == 0)
{
return x_30;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_30, 0);
x_126 = lean_ctor_get(x_30, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_30);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_128 = lean_ctor_get(x_22, 1);
x_129 = lean_ctor_get(x_22, 2);
x_130 = lean_ctor_get(x_22, 3);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_22);
x_131 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_131, 0, x_20);
lean_ctor_set(x_131, 1, x_128);
lean_ctor_set(x_131, 2, x_129);
lean_ctor_set(x_131, 3, x_130);
x_132 = lean_st_ref_set(x_1, x_131, x_23);
x_133 = lean_unbox(x_19);
if (x_133 == 0)
{
lean_object* x_134; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec_ref(x_132);
lean_ctor_set(x_15, 1, x_134);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_free_object(x_15);
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
lean_dec_ref(x_132);
x_136 = l_Lean_Meta_Grind_getGoal___redArg(x_1, x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec_ref(x_136);
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
lean_dec(x_137);
x_140 = l_Lean_Meta_Grind_ematchStep___closed__0;
lean_inc(x_1);
x_141 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg(x_139, x_140, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_138);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
x_145 = lean_ctor_get(x_142, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
lean_dec(x_142);
x_147 = lean_st_ref_take(x_1, x_143);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec_ref(x_147);
x_150 = lean_ctor_get(x_148, 1);
lean_inc_ref(x_150);
x_151 = lean_ctor_get(x_148, 2);
lean_inc(x_151);
x_152 = lean_ctor_get(x_148, 3);
lean_inc(x_152);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 lean_ctor_release(x_148, 2);
 lean_ctor_release(x_148, 3);
 x_153 = x_148;
} else {
 lean_dec_ref(x_148);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(0, 4, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_146);
lean_ctor_set(x_154, 1, x_150);
lean_ctor_set(x_154, 2, x_151);
lean_ctor_set(x_154, 3, x_152);
x_155 = lean_st_ref_set(x_1, x_154, x_149);
x_156 = lean_ctor_get_uint8(x_145, sizeof(void*)*8);
lean_dec(x_145);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_1);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec_ref(x_155);
if (lean_is_scalar(x_144)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_144;
}
lean_ctor_set(x_158, 0, x_19);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_159 = lean_ctor_get(x_155, 1);
lean_inc(x_159);
lean_dec_ref(x_155);
x_160 = lean_st_ref_take(x_1, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec_ref(x_160);
x_163 = lean_ctor_get(x_161, 0);
lean_inc_ref(x_163);
x_164 = lean_ctor_get(x_161, 1);
lean_inc_ref(x_164);
x_165 = lean_ctor_get(x_161, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_161, 3);
lean_inc(x_166);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 lean_ctor_release(x_161, 2);
 lean_ctor_release(x_161, 3);
 x_167 = x_161;
} else {
 lean_dec_ref(x_161);
 x_167 = lean_box(0);
}
x_168 = lean_box(2);
x_169 = lean_array_push(x_164, x_168);
if (lean_is_scalar(x_167)) {
 x_170 = lean_alloc_ctor(0, 4, 0);
} else {
 x_170 = x_167;
}
lean_ctor_set(x_170, 0, x_163);
lean_ctor_set(x_170, 1, x_169);
lean_ctor_set(x_170, 2, x_165);
lean_ctor_set(x_170, 3, x_166);
x_171 = lean_st_ref_set(x_1, x_170, x_162);
lean_dec(x_1);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
lean_dec_ref(x_171);
if (lean_is_scalar(x_144)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_144;
}
lean_ctor_set(x_173, 0, x_19);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_19);
lean_dec(x_1);
x_174 = lean_ctor_get(x_141, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_141, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_176 = x_141;
} else {
 lean_dec_ref(x_141);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_178 = lean_ctor_get(x_136, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_136, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_180 = x_136;
} else {
 lean_dec_ref(x_136);
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
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_182 = lean_ctor_get(x_15, 0);
x_183 = lean_ctor_get(x_15, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_15);
x_184 = lean_ctor_get(x_182, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_182, 1);
lean_inc(x_185);
lean_dec(x_182);
x_186 = lean_st_ref_take(x_1, x_183);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec_ref(x_186);
x_189 = lean_ctor_get(x_187, 1);
lean_inc_ref(x_189);
x_190 = lean_ctor_get(x_187, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_187, 3);
lean_inc(x_191);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 x_192 = x_187;
} else {
 lean_dec_ref(x_187);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(0, 4, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_185);
lean_ctor_set(x_193, 1, x_189);
lean_ctor_set(x_193, 2, x_190);
lean_ctor_set(x_193, 3, x_191);
x_194 = lean_st_ref_set(x_1, x_193, x_188);
x_195 = lean_unbox(x_184);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec_ref(x_194);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_184);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; 
x_198 = lean_ctor_get(x_194, 1);
lean_inc(x_198);
lean_dec_ref(x_194);
x_199 = l_Lean_Meta_Grind_getGoal___redArg(x_1, x_198);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec_ref(x_199);
x_202 = lean_ctor_get(x_200, 0);
lean_inc(x_202);
lean_dec(x_200);
x_203 = l_Lean_Meta_Grind_ematchStep___closed__0;
lean_inc(x_1);
x_204 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg(x_202, x_203, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_201);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_207 = x_204;
} else {
 lean_dec_ref(x_204);
 x_207 = lean_box(0);
}
x_208 = lean_ctor_get(x_205, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_205, 1);
lean_inc(x_209);
lean_dec(x_205);
x_210 = lean_st_ref_take(x_1, x_206);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec_ref(x_210);
x_213 = lean_ctor_get(x_211, 1);
lean_inc_ref(x_213);
x_214 = lean_ctor_get(x_211, 2);
lean_inc(x_214);
x_215 = lean_ctor_get(x_211, 3);
lean_inc(x_215);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 lean_ctor_release(x_211, 2);
 lean_ctor_release(x_211, 3);
 x_216 = x_211;
} else {
 lean_dec_ref(x_211);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(0, 4, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_209);
lean_ctor_set(x_217, 1, x_213);
lean_ctor_set(x_217, 2, x_214);
lean_ctor_set(x_217, 3, x_215);
x_218 = lean_st_ref_set(x_1, x_217, x_212);
x_219 = lean_ctor_get_uint8(x_208, sizeof(void*)*8);
lean_dec(x_208);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_1);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec_ref(x_218);
if (lean_is_scalar(x_207)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_207;
}
lean_ctor_set(x_221, 0, x_184);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_222 = lean_ctor_get(x_218, 1);
lean_inc(x_222);
lean_dec_ref(x_218);
x_223 = lean_st_ref_take(x_1, x_222);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec_ref(x_223);
x_226 = lean_ctor_get(x_224, 0);
lean_inc_ref(x_226);
x_227 = lean_ctor_get(x_224, 1);
lean_inc_ref(x_227);
x_228 = lean_ctor_get(x_224, 2);
lean_inc(x_228);
x_229 = lean_ctor_get(x_224, 3);
lean_inc(x_229);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 lean_ctor_release(x_224, 2);
 lean_ctor_release(x_224, 3);
 x_230 = x_224;
} else {
 lean_dec_ref(x_224);
 x_230 = lean_box(0);
}
x_231 = lean_box(2);
x_232 = lean_array_push(x_227, x_231);
if (lean_is_scalar(x_230)) {
 x_233 = lean_alloc_ctor(0, 4, 0);
} else {
 x_233 = x_230;
}
lean_ctor_set(x_233, 0, x_226);
lean_ctor_set(x_233, 1, x_232);
lean_ctor_set(x_233, 2, x_228);
lean_ctor_set(x_233, 3, x_229);
x_234 = lean_st_ref_set(x_1, x_233, x_225);
lean_dec(x_1);
x_235 = lean_ctor_get(x_234, 1);
lean_inc(x_235);
lean_dec_ref(x_234);
if (lean_is_scalar(x_207)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_207;
}
lean_ctor_set(x_236, 0, x_184);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_184);
lean_dec(x_1);
x_237 = lean_ctor_get(x_204, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_204, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_239 = x_204;
} else {
 lean_dec_ref(x_204);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_184);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_241 = lean_ctor_get(x_199, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_199, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_243 = x_199;
} else {
 lean_dec_ref(x_199);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_242);
return x_244;
}
}
}
}
else
{
uint8_t x_245; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_245 = !lean_is_exclusive(x_15);
if (x_245 == 0)
{
return x_15;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_15, 0);
x_247 = lean_ctor_get(x_15, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_15);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
}
else
{
uint8_t x_249; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_249 = !lean_is_exclusive(x_10);
if (x_249 == 0)
{
return x_10;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_10, 0);
x_251 = lean_ctor_get(x_10, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_10);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mbtcStep___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_mbtcStep___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookaheadStep___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookaheadStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_getGoal___redArg(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_lookaheadStep___lam__0___boxed), 9, 0);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg(x_13, x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_st_ref_take(x_1, x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
lean_ctor_set(x_22, 0, x_20);
x_26 = lean_st_ref_set(x_1, x_22, x_23);
x_27 = lean_unbox(x_19);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
lean_ctor_set(x_15, 1, x_28);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_free_object(x_15);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec_ref(x_26);
x_30 = l_Lean_Meta_Grind_getGoal___redArg(x_1, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_Grind_ematchStep___closed__0;
lean_inc(x_1);
x_35 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg(x_33, x_34, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_st_ref_take(x_1, x_38);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_42, 0);
lean_dec(x_45);
lean_ctor_set(x_42, 0, x_40);
x_46 = lean_st_ref_set(x_1, x_42, x_43);
x_47 = lean_ctor_get_uint8(x_39, sizeof(void*)*8);
lean_dec(x_39);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_1);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
lean_ctor_set(x_35, 1, x_48);
lean_ctor_set(x_35, 0, x_19);
return x_35;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec_ref(x_46);
x_50 = lean_st_ref_take(x_1, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_51, 1);
x_55 = lean_box(1);
x_56 = lean_array_push(x_54, x_55);
lean_ctor_set(x_51, 1, x_56);
x_57 = lean_st_ref_set(x_1, x_51, x_52);
lean_dec(x_1);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec_ref(x_57);
lean_ctor_set(x_35, 1, x_58);
lean_ctor_set(x_35, 0, x_19);
return x_35;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_51, 0);
x_60 = lean_ctor_get(x_51, 1);
x_61 = lean_ctor_get(x_51, 2);
x_62 = lean_ctor_get(x_51, 3);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_51);
x_63 = lean_box(1);
x_64 = lean_array_push(x_60, x_63);
x_65 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_61);
lean_ctor_set(x_65, 3, x_62);
x_66 = lean_st_ref_set(x_1, x_65, x_52);
lean_dec(x_1);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec_ref(x_66);
lean_ctor_set(x_35, 1, x_67);
lean_ctor_set(x_35, 0, x_19);
return x_35;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_68 = lean_ctor_get(x_42, 1);
x_69 = lean_ctor_get(x_42, 2);
x_70 = lean_ctor_get(x_42, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_42);
x_71 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_71, 0, x_40);
lean_ctor_set(x_71, 1, x_68);
lean_ctor_set(x_71, 2, x_69);
lean_ctor_set(x_71, 3, x_70);
x_72 = lean_st_ref_set(x_1, x_71, x_43);
x_73 = lean_ctor_get_uint8(x_39, sizeof(void*)*8);
lean_dec(x_39);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_1);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec_ref(x_72);
lean_ctor_set(x_35, 1, x_74);
lean_ctor_set(x_35, 0, x_19);
return x_35;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec_ref(x_72);
x_76 = lean_st_ref_take(x_1, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec_ref(x_76);
x_79 = lean_ctor_get(x_77, 0);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_77, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_77, 3);
lean_inc(x_82);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 lean_ctor_release(x_77, 3);
 x_83 = x_77;
} else {
 lean_dec_ref(x_77);
 x_83 = lean_box(0);
}
x_84 = lean_box(1);
x_85 = lean_array_push(x_80, x_84);
if (lean_is_scalar(x_83)) {
 x_86 = lean_alloc_ctor(0, 4, 0);
} else {
 x_86 = x_83;
}
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_86, 2, x_81);
lean_ctor_set(x_86, 3, x_82);
x_87 = lean_st_ref_set(x_1, x_86, x_78);
lean_dec(x_1);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec_ref(x_87);
lean_ctor_set(x_35, 1, x_88);
lean_ctor_set(x_35, 0, x_19);
return x_35;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_89 = lean_ctor_get(x_35, 0);
x_90 = lean_ctor_get(x_35, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_35);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = lean_st_ref_take(x_1, x_90);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec_ref(x_93);
x_96 = lean_ctor_get(x_94, 1);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_94, 2);
lean_inc(x_97);
x_98 = lean_ctor_get(x_94, 3);
lean_inc(x_98);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 lean_ctor_release(x_94, 2);
 lean_ctor_release(x_94, 3);
 x_99 = x_94;
} else {
 lean_dec_ref(x_94);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 4, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_92);
lean_ctor_set(x_100, 1, x_96);
lean_ctor_set(x_100, 2, x_97);
lean_ctor_set(x_100, 3, x_98);
x_101 = lean_st_ref_set(x_1, x_100, x_95);
x_102 = lean_ctor_get_uint8(x_91, sizeof(void*)*8);
lean_dec(x_91);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_1);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec_ref(x_101);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_19);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_105 = lean_ctor_get(x_101, 1);
lean_inc(x_105);
lean_dec_ref(x_101);
x_106 = lean_st_ref_take(x_1, x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec_ref(x_106);
x_109 = lean_ctor_get(x_107, 0);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_107, 1);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_107, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_107, 3);
lean_inc(x_112);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 lean_ctor_release(x_107, 2);
 lean_ctor_release(x_107, 3);
 x_113 = x_107;
} else {
 lean_dec_ref(x_107);
 x_113 = lean_box(0);
}
x_114 = lean_box(1);
x_115 = lean_array_push(x_110, x_114);
if (lean_is_scalar(x_113)) {
 x_116 = lean_alloc_ctor(0, 4, 0);
} else {
 x_116 = x_113;
}
lean_ctor_set(x_116, 0, x_109);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set(x_116, 2, x_111);
lean_ctor_set(x_116, 3, x_112);
x_117 = lean_st_ref_set(x_1, x_116, x_108);
lean_dec(x_1);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec_ref(x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_19);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_19);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_35);
if (x_120 == 0)
{
return x_35;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_35, 0);
x_122 = lean_ctor_get(x_35, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_35);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_30);
if (x_124 == 0)
{
return x_30;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_30, 0);
x_126 = lean_ctor_get(x_30, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_30);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_128 = lean_ctor_get(x_22, 1);
x_129 = lean_ctor_get(x_22, 2);
x_130 = lean_ctor_get(x_22, 3);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_22);
x_131 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_131, 0, x_20);
lean_ctor_set(x_131, 1, x_128);
lean_ctor_set(x_131, 2, x_129);
lean_ctor_set(x_131, 3, x_130);
x_132 = lean_st_ref_set(x_1, x_131, x_23);
x_133 = lean_unbox(x_19);
if (x_133 == 0)
{
lean_object* x_134; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec_ref(x_132);
lean_ctor_set(x_15, 1, x_134);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_free_object(x_15);
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
lean_dec_ref(x_132);
x_136 = l_Lean_Meta_Grind_getGoal___redArg(x_1, x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec_ref(x_136);
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
lean_dec(x_137);
x_140 = l_Lean_Meta_Grind_ematchStep___closed__0;
lean_inc(x_1);
x_141 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg(x_139, x_140, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_138);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
x_145 = lean_ctor_get(x_142, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
lean_dec(x_142);
x_147 = lean_st_ref_take(x_1, x_143);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec_ref(x_147);
x_150 = lean_ctor_get(x_148, 1);
lean_inc_ref(x_150);
x_151 = lean_ctor_get(x_148, 2);
lean_inc(x_151);
x_152 = lean_ctor_get(x_148, 3);
lean_inc(x_152);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 lean_ctor_release(x_148, 2);
 lean_ctor_release(x_148, 3);
 x_153 = x_148;
} else {
 lean_dec_ref(x_148);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(0, 4, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_146);
lean_ctor_set(x_154, 1, x_150);
lean_ctor_set(x_154, 2, x_151);
lean_ctor_set(x_154, 3, x_152);
x_155 = lean_st_ref_set(x_1, x_154, x_149);
x_156 = lean_ctor_get_uint8(x_145, sizeof(void*)*8);
lean_dec(x_145);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_1);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec_ref(x_155);
if (lean_is_scalar(x_144)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_144;
}
lean_ctor_set(x_158, 0, x_19);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_159 = lean_ctor_get(x_155, 1);
lean_inc(x_159);
lean_dec_ref(x_155);
x_160 = lean_st_ref_take(x_1, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec_ref(x_160);
x_163 = lean_ctor_get(x_161, 0);
lean_inc_ref(x_163);
x_164 = lean_ctor_get(x_161, 1);
lean_inc_ref(x_164);
x_165 = lean_ctor_get(x_161, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_161, 3);
lean_inc(x_166);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 lean_ctor_release(x_161, 2);
 lean_ctor_release(x_161, 3);
 x_167 = x_161;
} else {
 lean_dec_ref(x_161);
 x_167 = lean_box(0);
}
x_168 = lean_box(1);
x_169 = lean_array_push(x_164, x_168);
if (lean_is_scalar(x_167)) {
 x_170 = lean_alloc_ctor(0, 4, 0);
} else {
 x_170 = x_167;
}
lean_ctor_set(x_170, 0, x_163);
lean_ctor_set(x_170, 1, x_169);
lean_ctor_set(x_170, 2, x_165);
lean_ctor_set(x_170, 3, x_166);
x_171 = lean_st_ref_set(x_1, x_170, x_162);
lean_dec(x_1);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
lean_dec_ref(x_171);
if (lean_is_scalar(x_144)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_144;
}
lean_ctor_set(x_173, 0, x_19);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_19);
lean_dec(x_1);
x_174 = lean_ctor_get(x_141, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_141, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_176 = x_141;
} else {
 lean_dec_ref(x_141);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_178 = lean_ctor_get(x_136, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_136, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_180 = x_136;
} else {
 lean_dec_ref(x_136);
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
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_182 = lean_ctor_get(x_15, 0);
x_183 = lean_ctor_get(x_15, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_15);
x_184 = lean_ctor_get(x_182, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_182, 1);
lean_inc(x_185);
lean_dec(x_182);
x_186 = lean_st_ref_take(x_1, x_183);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec_ref(x_186);
x_189 = lean_ctor_get(x_187, 1);
lean_inc_ref(x_189);
x_190 = lean_ctor_get(x_187, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_187, 3);
lean_inc(x_191);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 x_192 = x_187;
} else {
 lean_dec_ref(x_187);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(0, 4, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_185);
lean_ctor_set(x_193, 1, x_189);
lean_ctor_set(x_193, 2, x_190);
lean_ctor_set(x_193, 3, x_191);
x_194 = lean_st_ref_set(x_1, x_193, x_188);
x_195 = lean_unbox(x_184);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec_ref(x_194);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_184);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; 
x_198 = lean_ctor_get(x_194, 1);
lean_inc(x_198);
lean_dec_ref(x_194);
x_199 = l_Lean_Meta_Grind_getGoal___redArg(x_1, x_198);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec_ref(x_199);
x_202 = lean_ctor_get(x_200, 0);
lean_inc(x_202);
lean_dec(x_200);
x_203 = l_Lean_Meta_Grind_ematchStep___closed__0;
lean_inc(x_1);
x_204 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg(x_202, x_203, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_201);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_207 = x_204;
} else {
 lean_dec_ref(x_204);
 x_207 = lean_box(0);
}
x_208 = lean_ctor_get(x_205, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_205, 1);
lean_inc(x_209);
lean_dec(x_205);
x_210 = lean_st_ref_take(x_1, x_206);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec_ref(x_210);
x_213 = lean_ctor_get(x_211, 1);
lean_inc_ref(x_213);
x_214 = lean_ctor_get(x_211, 2);
lean_inc(x_214);
x_215 = lean_ctor_get(x_211, 3);
lean_inc(x_215);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 lean_ctor_release(x_211, 2);
 lean_ctor_release(x_211, 3);
 x_216 = x_211;
} else {
 lean_dec_ref(x_211);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(0, 4, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_209);
lean_ctor_set(x_217, 1, x_213);
lean_ctor_set(x_217, 2, x_214);
lean_ctor_set(x_217, 3, x_215);
x_218 = lean_st_ref_set(x_1, x_217, x_212);
x_219 = lean_ctor_get_uint8(x_208, sizeof(void*)*8);
lean_dec(x_208);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_1);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec_ref(x_218);
if (lean_is_scalar(x_207)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_207;
}
lean_ctor_set(x_221, 0, x_184);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_222 = lean_ctor_get(x_218, 1);
lean_inc(x_222);
lean_dec_ref(x_218);
x_223 = lean_st_ref_take(x_1, x_222);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec_ref(x_223);
x_226 = lean_ctor_get(x_224, 0);
lean_inc_ref(x_226);
x_227 = lean_ctor_get(x_224, 1);
lean_inc_ref(x_227);
x_228 = lean_ctor_get(x_224, 2);
lean_inc(x_228);
x_229 = lean_ctor_get(x_224, 3);
lean_inc(x_229);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 lean_ctor_release(x_224, 2);
 lean_ctor_release(x_224, 3);
 x_230 = x_224;
} else {
 lean_dec_ref(x_224);
 x_230 = lean_box(0);
}
x_231 = lean_box(1);
x_232 = lean_array_push(x_227, x_231);
if (lean_is_scalar(x_230)) {
 x_233 = lean_alloc_ctor(0, 4, 0);
} else {
 x_233 = x_230;
}
lean_ctor_set(x_233, 0, x_226);
lean_ctor_set(x_233, 1, x_232);
lean_ctor_set(x_233, 2, x_228);
lean_ctor_set(x_233, 3, x_229);
x_234 = lean_st_ref_set(x_1, x_233, x_225);
lean_dec(x_1);
x_235 = lean_ctor_get(x_234, 1);
lean_inc(x_235);
lean_dec_ref(x_234);
if (lean_is_scalar(x_207)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_207;
}
lean_ctor_set(x_236, 0, x_184);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_184);
lean_dec(x_1);
x_237 = lean_ctor_get(x_204, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_204, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_239 = x_204;
} else {
 lean_dec_ref(x_204);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_184);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_241 = lean_ctor_get(x_199, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_199, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_243 = x_199;
} else {
 lean_dec_ref(x_199);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_242);
return x_244;
}
}
}
}
else
{
uint8_t x_245; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_245 = !lean_is_exclusive(x_15);
if (x_245 == 0)
{
return x_15;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_15, 0);
x_247 = lean_ctor_get(x_15, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_15);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
}
else
{
uint8_t x_249; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_249 = !lean_is_exclusive(x_10);
if (x_249 == 0)
{
return x_10;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_10, 0);
x_251 = lean_ctor_get(x_10, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_10);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_lookaheadStep___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_lookaheadStep___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_71; 
x_71 = l_Lean_Meta_Grind_getGoal___redArg(x_3, x_11);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get_uint8(x_72, sizeof(void*)*17);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec_ref(x_71);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_40 = x_3;
x_41 = x_4;
x_42 = x_5;
x_43 = x_6;
x_44 = x_7;
x_45 = x_8;
x_46 = x_9;
x_47 = x_10;
x_48 = x_74;
goto block_70;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_dec_ref(x_71);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_76 = l_Lean_Meta_Grind_nextGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_78 = !lean_is_exclusive(x_76);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_76, 0);
lean_dec(x_79);
lean_ctor_set(x_76, 0, x_2);
return x_76;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
lean_dec(x_76);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_2);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
lean_dec_ref(x_76);
x_83 = lean_ctor_get(x_77, 0);
lean_inc(x_83);
lean_dec_ref(x_77);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_84 = l_Lean_Meta_Grind_intros(x_83, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_82);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec_ref(x_84);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_40 = x_3;
x_41 = x_4;
x_42 = x_5;
x_43 = x_6;
x_44 = x_7;
x_45 = x_8;
x_46 = x_9;
x_47 = x_10;
x_48 = x_85;
goto block_70;
}
else
{
uint8_t x_86; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_86 = !lean_is_exclusive(x_84);
if (x_86 == 0)
{
return x_84;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_84, 0);
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_84);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_90 = !lean_is_exclusive(x_76);
if (x_90 == 0)
{
return x_76;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_76, 0);
x_92 = lean_ctor_get(x_76, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_76);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_94 = !lean_is_exclusive(x_71);
if (x_94 == 0)
{
return x_71;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_71, 0);
x_96 = lean_ctor_get(x_71, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_71);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
block_39:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
x_15 = lean_unbox(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec_ref(x_13);
x_17 = l_Lean_Meta_Grind_getGoal___redArg(x_12, x_16);
lean_dec(x_12);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_1);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
return x_17;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_12);
x_33 = lean_ctor_get(x_13, 1);
lean_inc(x_33);
lean_dec_ref(x_13);
x_11 = x_33;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
return x_13;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_13);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
block_70:
{
lean_object* x_49; 
lean_inc(x_47);
lean_inc_ref(x_46);
lean_inc(x_45);
lean_inc_ref(x_44);
lean_inc(x_43);
lean_inc_ref(x_42);
lean_inc(x_41);
lean_inc(x_40);
x_49 = l_Lean_Meta_Grind_assertAll(x_40, x_41, x_42, x_43, x_44, x_45, x_46, x_47, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec_ref(x_49);
lean_inc(x_47);
lean_inc_ref(x_46);
lean_inc(x_45);
lean_inc_ref(x_44);
lean_inc(x_43);
lean_inc_ref(x_42);
lean_inc(x_41);
lean_inc(x_40);
x_53 = l_Lean_Meta_Grind_checkSolvers(x_40, x_41, x_42, x_43, x_44, x_45, x_46, x_47, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec_ref(x_53);
lean_inc(x_47);
lean_inc_ref(x_46);
lean_inc(x_45);
lean_inc_ref(x_44);
lean_inc(x_43);
lean_inc_ref(x_42);
lean_inc(x_41);
lean_inc(x_40);
x_57 = l_Lean_Meta_Grind_ematchStep(x_40, x_41, x_42, x_43, x_44, x_45, x_46, x_47, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec_ref(x_57);
lean_inc(x_47);
lean_inc_ref(x_46);
lean_inc(x_45);
lean_inc_ref(x_44);
lean_inc(x_43);
lean_inc_ref(x_42);
lean_inc(x_41);
lean_inc(x_40);
x_61 = l_Lean_Meta_Grind_lookaheadStep(x_40, x_41, x_42, x_43, x_44, x_45, x_46, x_47, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec_ref(x_61);
lean_inc(x_47);
lean_inc_ref(x_46);
lean_inc(x_45);
lean_inc_ref(x_44);
lean_inc(x_43);
lean_inc_ref(x_42);
lean_inc(x_41);
lean_inc(x_40);
x_65 = l_Lean_Meta_Grind_splitNext(x_40, x_41, x_42, x_43, x_44, x_45, x_46, x_47, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_unbox(x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec_ref(x_65);
lean_inc(x_40);
x_69 = l_Lean_Meta_Grind_mbtcStep(x_40, x_41, x_42, x_43, x_44, x_45, x_46, x_47, x_68);
x_12 = x_40;
x_13 = x_69;
goto block_39;
}
else
{
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
x_12 = x_40;
x_13 = x_65;
goto block_39;
}
}
else
{
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
x_12 = x_40;
x_13 = x_65;
goto block_39;
}
}
else
{
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
x_12 = x_40;
x_13 = x_61;
goto block_39;
}
}
else
{
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
x_12 = x_40;
x_13 = x_61;
goto block_39;
}
}
else
{
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
x_12 = x_40;
x_13 = x_57;
goto block_39;
}
}
else
{
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
x_12 = x_40;
x_13 = x_57;
goto block_39;
}
}
else
{
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
x_12 = x_40;
x_13 = x_53;
goto block_39;
}
}
else
{
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
x_12 = x_40;
x_13 = x_53;
goto block_39;
}
}
else
{
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
x_12 = x_40;
x_13 = x_49;
goto block_39;
}
}
else
{
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
x_12 = x_40;
x_13 = x_49;
goto block_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
x_16 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_14, x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_3);
return x_13;
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
lean_object* x_29; uint8_t x_30; uint8_t x_125; 
x_29 = l_Lean_Meta_Grind_ematchStep___closed__0;
x_125 = l_Lean_Exception_isMaxHeartbeat(x_26);
if (x_125 == 0)
{
uint8_t x_126; 
x_126 = l_Lean_Exception_isMaxRecDepth(x_26);
x_30 = x_126;
goto block_124;
}
else
{
x_30 = x_125;
goto block_124;
}
block_124:
{
if (x_30 == 0)
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
x_35 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg(x_34, x_29, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_33);
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
x_55 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg(x_52, x_54, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_51);
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
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_60, 1);
x_67 = lean_ctor_get(x_60, 2);
x_68 = lean_ctor_get(x_60, 3);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_60);
x_69 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set(x_69, 1, x_66);
lean_ctor_set(x_69, 2, x_67);
lean_ctor_set(x_69, 3, x_68);
x_70 = lean_st_ref_set(x_1, x_69, x_61);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec_ref(x_70);
x_10 = x_1;
x_11 = x_71;
goto block_24;
}
}
else
{
uint8_t x_72; 
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_55);
if (x_72 == 0)
{
return x_55;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_55, 0);
x_74 = lean_ctor_get(x_55, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_55);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_49);
if (x_76 == 0)
{
return x_49;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_49, 0);
x_78 = lean_ctor_get(x_49, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_49);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_80 = lean_ctor_get(x_41, 1);
x_81 = lean_ctor_get(x_41, 2);
x_82 = lean_ctor_get(x_41, 3);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_41);
x_83 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_83, 0, x_39);
lean_ctor_set(x_83, 1, x_80);
lean_ctor_set(x_83, 2, x_81);
lean_ctor_set(x_83, 3, x_82);
x_84 = lean_st_ref_set(x_1, x_83, x_42);
x_85 = lean_ctor_get_uint8(x_38, sizeof(void*)*8 + 11);
lean_dec(x_38);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec_ref(x_84);
x_10 = x_1;
x_11 = x_86;
goto block_24;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec_ref(x_84);
x_88 = l_Lean_Meta_Grind_getGoal___redArg(x_1, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec_ref(x_88);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Lean_Exception_toMessageData(x_26);
x_93 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main___lam__1___boxed), 10, 1);
lean_closure_set(x_93, 0, x_92);
lean_inc(x_1);
x_94 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_checkSolvers_spec__0___redArg(x_91, x_93, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_90);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec_ref(x_94);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_st_ref_take(x_1, x_96);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec_ref(x_98);
x_101 = lean_ctor_get(x_99, 1);
lean_inc_ref(x_101);
x_102 = lean_ctor_get(x_99, 2);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 3);
lean_inc(x_103);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 lean_ctor_release(x_99, 2);
 lean_ctor_release(x_99, 3);
 x_104 = x_99;
} else {
 lean_dec_ref(x_99);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(0, 4, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_97);
lean_ctor_set(x_105, 1, x_101);
lean_ctor_set(x_105, 2, x_102);
lean_ctor_set(x_105, 3, x_103);
x_106 = lean_st_ref_set(x_1, x_105, x_100);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec_ref(x_106);
x_10 = x_1;
x_11 = x_107;
goto block_24;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_1);
x_108 = lean_ctor_get(x_94, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_94, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_110 = x_94;
} else {
 lean_dec_ref(x_94);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_112 = lean_ctor_get(x_88, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_88, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_114 = x_88;
} else {
 lean_dec_ref(x_88);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_35);
if (x_116 == 0)
{
return x_35;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_35, 0);
x_118 = lean_ctor_get(x_35, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_35);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_31);
if (x_120 == 0)
{
return x_31;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_31, 0);
x_122 = lean_ctor_get(x_31, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_31);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
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
static lean_object* _init_l_Lean_Meta_Grind_solve___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_solve(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = l_Lean_Meta_Grind_solve___closed__0;
x_12 = lean_box(0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set(x_14, 3, x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_solve___lam__0), 9, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_solve_spec__0___redArg(x_10, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
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
l_Lean_Meta_Grind_ematchStep___closed__0 = _init_l_Lean_Meta_Grind_ematchStep___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_ematchStep___closed__0);
l_Lean_Meta_Grind_ematchStep___closed__1 = _init_l_Lean_Meta_Grind_ematchStep___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_ematchStep___closed__1);
l_Lean_Meta_Grind_ematchStep___closed__2 = _init_l_Lean_Meta_Grind_ematchStep___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_ematchStep___closed__2);
l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop___closed__0);
l_Lean_Meta_Grind_solve___closed__0 = _init_l_Lean_Meta_Grind_solve___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_solve___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
