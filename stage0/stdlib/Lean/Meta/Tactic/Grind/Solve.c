// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Solve
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.SearchM Lean.Meta.Tactic.Grind.Split Lean.Meta.Tactic.Grind.EMatch Lean.Meta.Tactic.Grind.Arith Lean.Meta.Tactic.Grind.Lookahead Lean.Meta.Tactic.Grind.Intro Lean.Meta.Tactic.Grind.Check
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_solve_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isMaxHeartbeat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isMaxRecDepth(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_splitNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Solvers_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_solve_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_solve___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Solvers_mbtc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mbtc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryFallback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_mbtc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_solve_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Meta_Grind_lookahead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* l_Lean_Meta_Grind_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGoal___redArg(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Meta_Grind_assertAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ematch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop___closed__0;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0___redArg___closed__0;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_nextGoal_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0___redArg___closed__1;
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = l_Lean_instBEqMVarId_beq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0_spec__0___redArg(x_2, x_5, x_6);
return x_7;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0___redArg___closed__1;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_instBEqMVarId_beq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0_spec__0___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_instHashableMVarId_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 7);
lean_inc_ref(x_9);
lean_dec_ref(x_6);
x_10 = l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0___redArg(x_9, x_1);
x_11 = lean_box(x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_6, 7);
lean_inc_ref(x_13);
lean_dec_ref(x_6);
x_14 = l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0___redArg(x_13, x_1);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0___redArg(x_1, x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryFallback(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_10);
lean_inc(x_6);
lean_inc(x_1);
x_11 = lean_apply_9(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Lean_Meta_Grind_isInconsistent___redArg(x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec_ref(x_13);
x_17 = lean_st_ref_get(x_1, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0___redArg(x_20, x_6, x_19);
lean_dec(x_6);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_1);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec_ref(x_21);
x_25 = lean_st_ref_take(x_1, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
uint8_t x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_unbox(x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*17, x_29);
x_30 = lean_st_ref_set(x_1, x_26, x_27);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_22);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_ctor_get(x_26, 1);
x_37 = lean_ctor_get(x_26, 2);
x_38 = lean_ctor_get(x_26, 3);
x_39 = lean_ctor_get(x_26, 4);
x_40 = lean_ctor_get(x_26, 5);
x_41 = lean_ctor_get(x_26, 6);
x_42 = lean_ctor_get(x_26, 7);
x_43 = lean_ctor_get(x_26, 8);
x_44 = lean_ctor_get(x_26, 9);
x_45 = lean_ctor_get(x_26, 10);
x_46 = lean_ctor_get(x_26, 11);
x_47 = lean_ctor_get(x_26, 12);
x_48 = lean_ctor_get(x_26, 13);
x_49 = lean_ctor_get(x_26, 14);
x_50 = lean_ctor_get(x_26, 15);
x_51 = lean_ctor_get(x_26, 16);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_26);
x_52 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_52, 0, x_35);
lean_ctor_set(x_52, 1, x_36);
lean_ctor_set(x_52, 2, x_37);
lean_ctor_set(x_52, 3, x_38);
lean_ctor_set(x_52, 4, x_39);
lean_ctor_set(x_52, 5, x_40);
lean_ctor_set(x_52, 6, x_41);
lean_ctor_set(x_52, 7, x_42);
lean_ctor_set(x_52, 8, x_43);
lean_ctor_set(x_52, 9, x_44);
lean_ctor_set(x_52, 10, x_45);
lean_ctor_set(x_52, 11, x_46);
lean_ctor_set(x_52, 12, x_47);
lean_ctor_set(x_52, 13, x_48);
lean_ctor_set(x_52, 14, x_49);
lean_ctor_set(x_52, 15, x_50);
lean_ctor_set(x_52, 16, x_51);
x_53 = lean_unbox(x_22);
lean_ctor_set_uint8(x_52, sizeof(void*)*17, x_53);
x_54 = lean_st_ref_set(x_1, x_52, x_27);
lean_dec(x_1);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_22);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_1);
return x_13;
}
}
else
{
lean_dec(x_6);
lean_dec(x_1);
return x_13;
}
}
else
{
uint8_t x_58; 
lean_dec(x_6);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_11);
if (x_58 == 0)
{
return x_11;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_11, 0);
x_60 = lean_ctor_get(x_11, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_11);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
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
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_18 = l_Lean_Meta_Grind_check(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_st_ref_get(x_16, x_20);
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_14, 1, x_23);
lean_ctor_set(x_14, 0, x_19);
lean_ctor_set(x_21, 0, x_14);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_14, 1, x_24);
lean_ctor_set(x_14, 0, x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_14);
lean_dec(x_16);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
lean_inc(x_31);
x_33 = l_Lean_Meta_Grind_check(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = lean_st_ref_get(x_31, x_35);
lean_dec(x_31);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_37);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_31);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_44 = x_33;
} else {
 lean_dec_ref(x_33);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
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
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_18 = l_Lean_Meta_Grind_Solvers_check(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_st_ref_get(x_16, x_20);
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_14, 1, x_23);
lean_ctor_set(x_14, 0, x_19);
lean_ctor_set(x_21, 0, x_14);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_14, 1, x_24);
lean_ctor_set(x_14, 0, x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_14);
lean_dec(x_16);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
lean_inc(x_31);
x_33 = l_Lean_Meta_Grind_Solvers_check(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = lean_st_ref_get(x_31, x_35);
lean_dec(x_31);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_37);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_31);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_44 = x_33;
} else {
 lean_dec_ref(x_33);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
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
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_18 = l_Lean_Meta_Grind_ematch(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_st_ref_get(x_16, x_20);
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_14, 1, x_23);
lean_ctor_set(x_14, 0, x_19);
lean_ctor_set(x_21, 0, x_14);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_14, 1, x_24);
lean_ctor_set(x_14, 0, x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_14);
lean_dec(x_16);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
lean_inc(x_31);
x_33 = l_Lean_Meta_Grind_ematch(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = lean_st_ref_get(x_31, x_35);
lean_dec(x_31);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_37);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_31);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_44 = x_33;
} else {
 lean_dec_ref(x_33);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
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
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_18 = l_Lean_Meta_Grind_lookahead(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_st_ref_get(x_16, x_20);
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_14, 1, x_23);
lean_ctor_set(x_14, 0, x_19);
lean_ctor_set(x_21, 0, x_14);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_14, 1, x_24);
lean_ctor_set(x_14, 0, x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_14);
lean_dec(x_16);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
lean_inc(x_31);
x_33 = l_Lean_Meta_Grind_lookahead(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = lean_st_ref_get(x_31, x_35);
lean_dec(x_31);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_37);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_31);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_44 = x_33;
} else {
 lean_dec_ref(x_33);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
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
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_18 = l_Lean_Meta_Grind_Arith_Cutsat_mbtc(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_st_ref_get(x_16, x_20);
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_14, 1, x_23);
lean_ctor_set(x_14, 0, x_19);
lean_ctor_set(x_21, 0, x_14);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_14, 1, x_24);
lean_ctor_set(x_14, 0, x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_14);
lean_dec(x_16);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
lean_inc(x_31);
x_33 = l_Lean_Meta_Grind_Arith_Cutsat_mbtc(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = lean_st_ref_get(x_31, x_35);
lean_dec(x_31);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_37);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_31);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_44 = x_33;
} else {
 lean_dec_ref(x_33);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
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
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_18 = l_Lean_Meta_Grind_Arith_Linear_mbtc(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_st_ref_get(x_16, x_20);
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_14, 1, x_23);
lean_ctor_set(x_14, 0, x_19);
lean_ctor_set(x_21, 0, x_14);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_14, 1, x_24);
lean_ctor_set(x_14, 0, x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_14);
lean_dec(x_16);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
lean_inc(x_31);
x_33 = l_Lean_Meta_Grind_Arith_Linear_mbtc(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = lean_st_ref_get(x_31, x_35);
lean_dec(x_31);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_37);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_31);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_44 = x_33;
} else {
 lean_dec_ref(x_33);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
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
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_18 = l_Lean_Meta_Grind_Solvers_mbtc(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_st_ref_get(x_16, x_20);
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_14, 1, x_23);
lean_ctor_set(x_14, 0, x_19);
lean_ctor_set(x_21, 0, x_14);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_14, 1, x_24);
lean_ctor_set(x_14, 0, x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_14);
lean_dec(x_16);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
lean_inc(x_31);
x_33 = l_Lean_Meta_Grind_Solvers_mbtc(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = lean_st_ref_get(x_31, x_35);
lean_dec(x_31);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_37);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_31);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_44 = x_33;
} else {
 lean_dec_ref(x_33);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
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
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_18 = l_Lean_Meta_Grind_tryFallback(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_st_ref_get(x_16, x_20);
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_14, 1, x_23);
lean_ctor_set(x_14, 0, x_19);
lean_ctor_set(x_21, 0, x_14);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_14, 1, x_24);
lean_ctor_set(x_14, 0, x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_14);
lean_dec(x_16);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
lean_inc(x_31);
x_33 = l_Lean_Meta_Grind_tryFallback(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = lean_st_ref_get(x_31, x_35);
lean_dec(x_31);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_37);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_31);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_44 = x_33;
} else {
 lean_dec_ref(x_33);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
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
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
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
x_51 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__4___boxed), 9, 0);
x_52 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__5___boxed), 9, 0);
x_53 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__6___boxed), 9, 0);
x_54 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__7___boxed), 9, 0);
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
x_55 = x_3;
x_56 = x_4;
x_57 = x_5;
x_58 = x_6;
x_59 = x_7;
x_60 = x_8;
x_61 = x_9;
x_62 = x_10;
x_63 = x_45;
goto block_1126;
}
else
{
lean_object* x_1127; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1127 = l_Lean_Meta_Grind_nextGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_45);
if (lean_obj_tag(x_1127) == 0)
{
lean_object* x_1128; 
x_1128 = lean_ctor_get(x_1127, 0);
lean_inc(x_1128);
if (lean_obj_tag(x_1128) == 0)
{
uint8_t x_1129; 
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_1129 = !lean_is_exclusive(x_1127);
if (x_1129 == 0)
{
lean_object* x_1130; 
x_1130 = lean_ctor_get(x_1127, 0);
lean_dec(x_1130);
lean_ctor_set(x_1127, 0, x_1);
return x_1127;
}
else
{
lean_object* x_1131; lean_object* x_1132; 
x_1131 = lean_ctor_get(x_1127, 1);
lean_inc(x_1131);
lean_dec(x_1127);
x_1132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1132, 0, x_1);
lean_ctor_set(x_1132, 1, x_1131);
return x_1132;
}
}
else
{
lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; 
x_1133 = lean_ctor_get(x_1127, 1);
lean_inc(x_1133);
lean_dec_ref(x_1127);
x_1134 = lean_ctor_get(x_1128, 0);
lean_inc(x_1134);
lean_dec_ref(x_1128);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1135 = l_Lean_Meta_Grind_intros(x_1134, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1133);
if (lean_obj_tag(x_1135) == 0)
{
lean_object* x_1136; 
x_1136 = lean_ctor_get(x_1135, 1);
lean_inc(x_1136);
lean_dec_ref(x_1135);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_55 = x_3;
x_56 = x_4;
x_57 = x_5;
x_58 = x_6;
x_59 = x_7;
x_60 = x_8;
x_61 = x_9;
x_62 = x_10;
x_63 = x_1136;
goto block_1126;
}
else
{
uint8_t x_1137; 
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_1137 = !lean_is_exclusive(x_1135);
if (x_1137 == 0)
{
return x_1135;
}
else
{
lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; 
x_1138 = lean_ctor_get(x_1135, 0);
x_1139 = lean_ctor_get(x_1135, 1);
lean_inc(x_1139);
lean_inc(x_1138);
lean_dec(x_1135);
x_1140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1140, 0, x_1138);
lean_ctor_set(x_1140, 1, x_1139);
return x_1140;
}
}
}
}
else
{
uint8_t x_1141; 
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_1141 = !lean_is_exclusive(x_1127);
if (x_1141 == 0)
{
return x_1127;
}
else
{
lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; 
x_1142 = lean_ctor_get(x_1127, 0);
x_1143 = lean_ctor_get(x_1127, 1);
lean_inc(x_1143);
lean_inc(x_1142);
lean_dec(x_1127);
x_1144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1144, 0, x_1142);
lean_ctor_set(x_1144, 1, x_1143);
return x_1144;
}
}
}
block_1126:
{
lean_object* x_64; 
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_64 = l_Lean_Meta_Grind_assertAll(x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec_ref(x_64);
x_68 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_72 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_71, x_47, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec_ref(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_st_ref_take(x_55, x_74);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec_ref(x_77);
x_80 = !lean_is_exclusive(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_81 = lean_ctor_get(x_78, 0);
lean_dec(x_81);
lean_ctor_set(x_78, 0, x_76);
x_82 = lean_st_ref_set(x_55, x_78, x_79);
x_83 = lean_unbox(x_75);
lean_dec(x_75);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec_ref(x_82);
x_85 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec_ref(x_85);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
lean_dec(x_86);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_89 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_88, x_48, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_87);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec_ref(x_89);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_st_ref_take(x_55, x_91);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec_ref(x_94);
x_97 = !lean_is_exclusive(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = lean_ctor_get(x_95, 0);
lean_dec(x_98);
lean_ctor_set(x_95, 0, x_93);
x_99 = lean_st_ref_set(x_55, x_95, x_96);
x_100 = lean_unbox(x_92);
lean_dec(x_92);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec_ref(x_99);
x_102 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec_ref(x_102);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_106 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_105, x_49, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_104);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec_ref(x_106);
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
lean_dec(x_107);
x_111 = lean_st_ref_take(x_55, x_108);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec_ref(x_111);
x_114 = !lean_is_exclusive(x_112);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = lean_ctor_get(x_112, 0);
lean_dec(x_115);
lean_ctor_set(x_112, 0, x_110);
x_116 = lean_st_ref_set(x_55, x_112, x_113);
x_117 = lean_unbox(x_109);
lean_dec(x_109);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec_ref(x_116);
x_119 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_118);
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
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_123 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_122, x_50, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_121);
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
x_128 = lean_st_ref_take(x_55, x_125);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec_ref(x_128);
x_131 = !lean_is_exclusive(x_129);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = lean_ctor_get(x_129, 0);
lean_dec(x_132);
lean_ctor_set(x_129, 0, x_127);
x_133 = lean_st_ref_set(x_55, x_129, x_130);
x_134 = lean_unbox(x_126);
lean_dec(x_126);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec_ref(x_133);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_136 = l_Lean_Meta_Grind_splitNext(x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_unbox(x_137);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec_ref(x_136);
x_140 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec_ref(x_140);
x_143 = lean_ctor_get(x_141, 0);
lean_inc(x_143);
lean_dec(x_141);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_144 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_143, x_51, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_142);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec_ref(x_144);
x_147 = lean_ctor_get(x_145, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
lean_dec(x_145);
x_149 = lean_st_ref_take(x_55, x_146);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec_ref(x_149);
x_152 = !lean_is_exclusive(x_150);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_153 = lean_ctor_get(x_150, 0);
lean_dec(x_153);
lean_ctor_set(x_150, 0, x_148);
x_154 = lean_st_ref_set(x_55, x_150, x_151);
x_155 = lean_unbox(x_147);
lean_dec(x_147);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec_ref(x_154);
x_157 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec_ref(x_157);
x_160 = lean_ctor_get(x_158, 0);
lean_inc(x_160);
lean_dec(x_158);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_161 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_160, x_52, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_159);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec_ref(x_161);
x_164 = lean_ctor_get(x_162, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_dec(x_162);
x_166 = lean_st_ref_take(x_55, x_163);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec_ref(x_166);
x_169 = !lean_is_exclusive(x_167);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_170 = lean_ctor_get(x_167, 0);
lean_dec(x_170);
lean_ctor_set(x_167, 0, x_165);
x_171 = lean_st_ref_set(x_55, x_167, x_168);
x_172 = lean_unbox(x_164);
lean_dec(x_164);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec_ref(x_171);
x_174 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_173);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec_ref(x_174);
x_177 = lean_ctor_get(x_175, 0);
lean_inc(x_177);
lean_dec(x_175);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_178 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_177, x_53, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_176);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec_ref(x_178);
x_181 = lean_ctor_get(x_179, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
lean_dec(x_179);
x_183 = lean_st_ref_take(x_55, x_180);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec_ref(x_183);
x_186 = !lean_is_exclusive(x_184);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_187 = lean_ctor_get(x_184, 0);
lean_dec(x_187);
lean_ctor_set(x_184, 0, x_182);
x_188 = lean_st_ref_set(x_55, x_184, x_185);
x_189 = lean_unbox(x_181);
lean_dec(x_181);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec_ref(x_188);
x_191 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_190);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec_ref(x_191);
x_194 = lean_ctor_get(x_192, 0);
lean_inc(x_194);
lean_dec(x_192);
lean_inc(x_55);
x_195 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_194, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_193);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec_ref(x_195);
x_198 = lean_ctor_get(x_196, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_196, 1);
lean_inc(x_199);
lean_dec(x_196);
x_200 = lean_st_ref_take(x_55, x_197);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec_ref(x_200);
x_203 = !lean_is_exclusive(x_201);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_204 = lean_ctor_get(x_201, 0);
lean_dec(x_204);
lean_ctor_set(x_201, 0, x_199);
x_205 = lean_st_ref_set(x_55, x_201, x_202);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
lean_dec_ref(x_205);
x_207 = lean_unbox(x_198);
lean_dec(x_198);
x_12 = x_55;
x_13 = x_207;
x_14 = x_206;
goto block_32;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_208 = lean_ctor_get(x_201, 1);
lean_inc(x_208);
lean_dec(x_201);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_199);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_st_ref_set(x_55, x_209, x_202);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec_ref(x_210);
x_212 = lean_unbox(x_198);
lean_dec(x_198);
x_12 = x_55;
x_13 = x_212;
x_14 = x_211;
goto block_32;
}
}
else
{
uint8_t x_213; 
lean_dec(x_55);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_213 = !lean_is_exclusive(x_195);
if (x_213 == 0)
{
return x_195;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_195, 0);
x_215 = lean_ctor_get(x_195, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_195);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
else
{
uint8_t x_217; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_217 = !lean_is_exclusive(x_191);
if (x_217 == 0)
{
return x_191;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_191, 0);
x_219 = lean_ctor_get(x_191, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_191);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
else
{
lean_object* x_221; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
x_221 = lean_ctor_get(x_188, 1);
lean_inc(x_221);
lean_dec_ref(x_188);
x_11 = x_221;
goto _start;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_223 = lean_ctor_get(x_184, 1);
lean_inc(x_223);
lean_dec(x_184);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_182);
lean_ctor_set(x_224, 1, x_223);
x_225 = lean_st_ref_set(x_55, x_224, x_185);
x_226 = lean_unbox(x_181);
lean_dec(x_181);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec_ref(x_225);
x_228 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_227);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec_ref(x_228);
x_231 = lean_ctor_get(x_229, 0);
lean_inc(x_231);
lean_dec(x_229);
lean_inc(x_55);
x_232 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_231, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_230);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec_ref(x_232);
x_235 = lean_ctor_get(x_233, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_233, 1);
lean_inc(x_236);
lean_dec(x_233);
x_237 = lean_st_ref_take(x_55, x_234);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec_ref(x_237);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_241 = x_238;
} else {
 lean_dec_ref(x_238);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_241;
}
lean_ctor_set(x_242, 0, x_236);
lean_ctor_set(x_242, 1, x_240);
x_243 = lean_st_ref_set(x_55, x_242, x_239);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec_ref(x_243);
x_245 = lean_unbox(x_235);
lean_dec(x_235);
x_12 = x_55;
x_13 = x_245;
x_14 = x_244;
goto block_32;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_55);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_246 = lean_ctor_get(x_232, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_232, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_248 = x_232;
} else {
 lean_dec_ref(x_232);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_250 = lean_ctor_get(x_228, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_228, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_252 = x_228;
} else {
 lean_dec_ref(x_228);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_250);
lean_ctor_set(x_253, 1, x_251);
return x_253;
}
}
else
{
lean_object* x_254; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
x_254 = lean_ctor_get(x_225, 1);
lean_inc(x_254);
lean_dec_ref(x_225);
x_11 = x_254;
goto _start;
}
}
}
else
{
uint8_t x_256; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_256 = !lean_is_exclusive(x_178);
if (x_256 == 0)
{
return x_178;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_178, 0);
x_258 = lean_ctor_get(x_178, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_178);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
}
}
else
{
uint8_t x_260; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_260 = !lean_is_exclusive(x_174);
if (x_260 == 0)
{
return x_174;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_174, 0);
x_262 = lean_ctor_get(x_174, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_174);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
return x_263;
}
}
}
else
{
lean_object* x_264; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
x_264 = lean_ctor_get(x_171, 1);
lean_inc(x_264);
lean_dec_ref(x_171);
x_11 = x_264;
goto _start;
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_266 = lean_ctor_get(x_167, 1);
lean_inc(x_266);
lean_dec(x_167);
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_165);
lean_ctor_set(x_267, 1, x_266);
x_268 = lean_st_ref_set(x_55, x_267, x_168);
x_269 = lean_unbox(x_164);
lean_dec(x_164);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec_ref(x_268);
x_271 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_270);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec_ref(x_271);
x_274 = lean_ctor_get(x_272, 0);
lean_inc(x_274);
lean_dec(x_272);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_275 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_274, x_53, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_273);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec_ref(x_275);
x_278 = lean_ctor_get(x_276, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_276, 1);
lean_inc(x_279);
lean_dec(x_276);
x_280 = lean_st_ref_take(x_55, x_277);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec_ref(x_280);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_284 = x_281;
} else {
 lean_dec_ref(x_281);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_279);
lean_ctor_set(x_285, 1, x_283);
x_286 = lean_st_ref_set(x_55, x_285, x_282);
x_287 = lean_unbox(x_278);
lean_dec(x_278);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; 
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec_ref(x_286);
x_289 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_288);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
lean_dec_ref(x_289);
x_292 = lean_ctor_get(x_290, 0);
lean_inc(x_292);
lean_dec(x_290);
lean_inc(x_55);
x_293 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_292, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_291);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec_ref(x_293);
x_296 = lean_ctor_get(x_294, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_294, 1);
lean_inc(x_297);
lean_dec(x_294);
x_298 = lean_st_ref_take(x_55, x_295);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
lean_dec_ref(x_298);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_302 = x_299;
} else {
 lean_dec_ref(x_299);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_297);
lean_ctor_set(x_303, 1, x_301);
x_304 = lean_st_ref_set(x_55, x_303, x_300);
x_305 = lean_ctor_get(x_304, 1);
lean_inc(x_305);
lean_dec_ref(x_304);
x_306 = lean_unbox(x_296);
lean_dec(x_296);
x_12 = x_55;
x_13 = x_306;
x_14 = x_305;
goto block_32;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_55);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_307 = lean_ctor_get(x_293, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_293, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_309 = x_293;
} else {
 lean_dec_ref(x_293);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(1, 2, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_307);
lean_ctor_set(x_310, 1, x_308);
return x_310;
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_311 = lean_ctor_get(x_289, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_289, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_313 = x_289;
} else {
 lean_dec_ref(x_289);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(1, 2, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_312);
return x_314;
}
}
else
{
lean_object* x_315; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
x_315 = lean_ctor_get(x_286, 1);
lean_inc(x_315);
lean_dec_ref(x_286);
x_11 = x_315;
goto _start;
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_317 = lean_ctor_get(x_275, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_275, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_319 = x_275;
} else {
 lean_dec_ref(x_275);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(1, 2, 0);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_317);
lean_ctor_set(x_320, 1, x_318);
return x_320;
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_321 = lean_ctor_get(x_271, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_271, 1);
lean_inc(x_322);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_323 = x_271;
} else {
 lean_dec_ref(x_271);
 x_323 = lean_box(0);
}
if (lean_is_scalar(x_323)) {
 x_324 = lean_alloc_ctor(1, 2, 0);
} else {
 x_324 = x_323;
}
lean_ctor_set(x_324, 0, x_321);
lean_ctor_set(x_324, 1, x_322);
return x_324;
}
}
else
{
lean_object* x_325; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
x_325 = lean_ctor_get(x_268, 1);
lean_inc(x_325);
lean_dec_ref(x_268);
x_11 = x_325;
goto _start;
}
}
}
else
{
uint8_t x_327; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_327 = !lean_is_exclusive(x_161);
if (x_327 == 0)
{
return x_161;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_161, 0);
x_329 = lean_ctor_get(x_161, 1);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_161);
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_328);
lean_ctor_set(x_330, 1, x_329);
return x_330;
}
}
}
else
{
uint8_t x_331; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_331 = !lean_is_exclusive(x_157);
if (x_331 == 0)
{
return x_157;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_157, 0);
x_333 = lean_ctor_get(x_157, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_157);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
return x_334;
}
}
}
else
{
lean_object* x_335; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
x_335 = lean_ctor_get(x_154, 1);
lean_inc(x_335);
lean_dec_ref(x_154);
x_11 = x_335;
goto _start;
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_337 = lean_ctor_get(x_150, 1);
lean_inc(x_337);
lean_dec(x_150);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_148);
lean_ctor_set(x_338, 1, x_337);
x_339 = lean_st_ref_set(x_55, x_338, x_151);
x_340 = lean_unbox(x_147);
lean_dec(x_147);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; 
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
lean_dec_ref(x_339);
x_342 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_341);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec_ref(x_342);
x_345 = lean_ctor_get(x_343, 0);
lean_inc(x_345);
lean_dec(x_343);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_346 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_345, x_52, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_344);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
lean_dec_ref(x_346);
x_349 = lean_ctor_get(x_347, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_347, 1);
lean_inc(x_350);
lean_dec(x_347);
x_351 = lean_st_ref_take(x_55, x_348);
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec_ref(x_351);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_355 = x_352;
} else {
 lean_dec_ref(x_352);
 x_355 = lean_box(0);
}
if (lean_is_scalar(x_355)) {
 x_356 = lean_alloc_ctor(0, 2, 0);
} else {
 x_356 = x_355;
}
lean_ctor_set(x_356, 0, x_350);
lean_ctor_set(x_356, 1, x_354);
x_357 = lean_st_ref_set(x_55, x_356, x_353);
x_358 = lean_unbox(x_349);
lean_dec(x_349);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; 
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
lean_dec_ref(x_357);
x_360 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_359);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec_ref(x_360);
x_363 = lean_ctor_get(x_361, 0);
lean_inc(x_363);
lean_dec(x_361);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_364 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_363, x_53, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_362);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; uint8_t x_376; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
lean_dec_ref(x_364);
x_367 = lean_ctor_get(x_365, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_365, 1);
lean_inc(x_368);
lean_dec(x_365);
x_369 = lean_st_ref_take(x_55, x_366);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec_ref(x_369);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_373 = x_370;
} else {
 lean_dec_ref(x_370);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_374 = lean_alloc_ctor(0, 2, 0);
} else {
 x_374 = x_373;
}
lean_ctor_set(x_374, 0, x_368);
lean_ctor_set(x_374, 1, x_372);
x_375 = lean_st_ref_set(x_55, x_374, x_371);
x_376 = lean_unbox(x_367);
lean_dec(x_367);
if (x_376 == 0)
{
lean_object* x_377; lean_object* x_378; 
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
lean_dec_ref(x_375);
x_378 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_377);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec_ref(x_378);
x_381 = lean_ctor_get(x_379, 0);
lean_inc(x_381);
lean_dec(x_379);
lean_inc(x_55);
x_382 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_381, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_380);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; uint8_t x_395; 
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_382, 1);
lean_inc(x_384);
lean_dec_ref(x_382);
x_385 = lean_ctor_get(x_383, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_383, 1);
lean_inc(x_386);
lean_dec(x_383);
x_387 = lean_st_ref_take(x_55, x_384);
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
lean_dec_ref(x_387);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 x_391 = x_388;
} else {
 lean_dec_ref(x_388);
 x_391 = lean_box(0);
}
if (lean_is_scalar(x_391)) {
 x_392 = lean_alloc_ctor(0, 2, 0);
} else {
 x_392 = x_391;
}
lean_ctor_set(x_392, 0, x_386);
lean_ctor_set(x_392, 1, x_390);
x_393 = lean_st_ref_set(x_55, x_392, x_389);
x_394 = lean_ctor_get(x_393, 1);
lean_inc(x_394);
lean_dec_ref(x_393);
x_395 = lean_unbox(x_385);
lean_dec(x_385);
x_12 = x_55;
x_13 = x_395;
x_14 = x_394;
goto block_32;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_55);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_396 = lean_ctor_get(x_382, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_382, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 x_398 = x_382;
} else {
 lean_dec_ref(x_382);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 2, 0);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_396);
lean_ctor_set(x_399, 1, x_397);
return x_399;
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_400 = lean_ctor_get(x_378, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_378, 1);
lean_inc(x_401);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_402 = x_378;
} else {
 lean_dec_ref(x_378);
 x_402 = lean_box(0);
}
if (lean_is_scalar(x_402)) {
 x_403 = lean_alloc_ctor(1, 2, 0);
} else {
 x_403 = x_402;
}
lean_ctor_set(x_403, 0, x_400);
lean_ctor_set(x_403, 1, x_401);
return x_403;
}
}
else
{
lean_object* x_404; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
x_404 = lean_ctor_get(x_375, 1);
lean_inc(x_404);
lean_dec_ref(x_375);
x_11 = x_404;
goto _start;
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_406 = lean_ctor_get(x_364, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_364, 1);
lean_inc(x_407);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_408 = x_364;
} else {
 lean_dec_ref(x_364);
 x_408 = lean_box(0);
}
if (lean_is_scalar(x_408)) {
 x_409 = lean_alloc_ctor(1, 2, 0);
} else {
 x_409 = x_408;
}
lean_ctor_set(x_409, 0, x_406);
lean_ctor_set(x_409, 1, x_407);
return x_409;
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_410 = lean_ctor_get(x_360, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_360, 1);
lean_inc(x_411);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_412 = x_360;
} else {
 lean_dec_ref(x_360);
 x_412 = lean_box(0);
}
if (lean_is_scalar(x_412)) {
 x_413 = lean_alloc_ctor(1, 2, 0);
} else {
 x_413 = x_412;
}
lean_ctor_set(x_413, 0, x_410);
lean_ctor_set(x_413, 1, x_411);
return x_413;
}
}
else
{
lean_object* x_414; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
x_414 = lean_ctor_get(x_357, 1);
lean_inc(x_414);
lean_dec_ref(x_357);
x_11 = x_414;
goto _start;
}
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_416 = lean_ctor_get(x_346, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_346, 1);
lean_inc(x_417);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_418 = x_346;
} else {
 lean_dec_ref(x_346);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_418)) {
 x_419 = lean_alloc_ctor(1, 2, 0);
} else {
 x_419 = x_418;
}
lean_ctor_set(x_419, 0, x_416);
lean_ctor_set(x_419, 1, x_417);
return x_419;
}
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_420 = lean_ctor_get(x_342, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_342, 1);
lean_inc(x_421);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_422 = x_342;
} else {
 lean_dec_ref(x_342);
 x_422 = lean_box(0);
}
if (lean_is_scalar(x_422)) {
 x_423 = lean_alloc_ctor(1, 2, 0);
} else {
 x_423 = x_422;
}
lean_ctor_set(x_423, 0, x_420);
lean_ctor_set(x_423, 1, x_421);
return x_423;
}
}
else
{
lean_object* x_424; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
x_424 = lean_ctor_get(x_339, 1);
lean_inc(x_424);
lean_dec_ref(x_339);
x_11 = x_424;
goto _start;
}
}
}
else
{
uint8_t x_426; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_426 = !lean_is_exclusive(x_144);
if (x_426 == 0)
{
return x_144;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_144, 0);
x_428 = lean_ctor_get(x_144, 1);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_144);
x_429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
return x_429;
}
}
}
else
{
uint8_t x_430; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_430 = !lean_is_exclusive(x_140);
if (x_430 == 0)
{
return x_140;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_431 = lean_ctor_get(x_140, 0);
x_432 = lean_ctor_get(x_140, 1);
lean_inc(x_432);
lean_inc(x_431);
lean_dec(x_140);
x_433 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set(x_433, 1, x_432);
return x_433;
}
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_33 = x_55;
x_34 = x_136;
goto block_42;
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_33 = x_55;
x_34 = x_136;
goto block_42;
}
}
else
{
lean_object* x_434; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_434 = lean_ctor_get(x_133, 1);
lean_inc(x_434);
lean_dec_ref(x_133);
x_11 = x_434;
goto _start;
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; 
x_436 = lean_ctor_get(x_129, 1);
lean_inc(x_436);
lean_dec(x_129);
x_437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_437, 0, x_127);
lean_ctor_set(x_437, 1, x_436);
x_438 = lean_st_ref_set(x_55, x_437, x_130);
x_439 = lean_unbox(x_126);
lean_dec(x_126);
if (x_439 == 0)
{
lean_object* x_440; lean_object* x_441; 
x_440 = lean_ctor_get(x_438, 1);
lean_inc(x_440);
lean_dec_ref(x_438);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_441 = l_Lean_Meta_Grind_splitNext(x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_440);
if (lean_obj_tag(x_441) == 0)
{
lean_object* x_442; uint8_t x_443; 
x_442 = lean_ctor_get(x_441, 0);
lean_inc(x_442);
x_443 = lean_unbox(x_442);
lean_dec(x_442);
if (x_443 == 0)
{
lean_object* x_444; lean_object* x_445; 
x_444 = lean_ctor_get(x_441, 1);
lean_inc(x_444);
lean_dec_ref(x_441);
x_445 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_444);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_445, 1);
lean_inc(x_447);
lean_dec_ref(x_445);
x_448 = lean_ctor_get(x_446, 0);
lean_inc(x_448);
lean_dec(x_446);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_449 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_448, x_51, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_447);
if (lean_obj_tag(x_449) == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; 
x_450 = lean_ctor_get(x_449, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_449, 1);
lean_inc(x_451);
lean_dec_ref(x_449);
x_452 = lean_ctor_get(x_450, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_450, 1);
lean_inc(x_453);
lean_dec(x_450);
x_454 = lean_st_ref_take(x_55, x_451);
x_455 = lean_ctor_get(x_454, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_454, 1);
lean_inc(x_456);
lean_dec_ref(x_454);
x_457 = lean_ctor_get(x_455, 1);
lean_inc(x_457);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 lean_ctor_release(x_455, 1);
 x_458 = x_455;
} else {
 lean_dec_ref(x_455);
 x_458 = lean_box(0);
}
if (lean_is_scalar(x_458)) {
 x_459 = lean_alloc_ctor(0, 2, 0);
} else {
 x_459 = x_458;
}
lean_ctor_set(x_459, 0, x_453);
lean_ctor_set(x_459, 1, x_457);
x_460 = lean_st_ref_set(x_55, x_459, x_456);
x_461 = lean_unbox(x_452);
lean_dec(x_452);
if (x_461 == 0)
{
lean_object* x_462; lean_object* x_463; 
x_462 = lean_ctor_get(x_460, 1);
lean_inc(x_462);
lean_dec_ref(x_460);
x_463 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_462);
if (lean_obj_tag(x_463) == 0)
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_463, 1);
lean_inc(x_465);
lean_dec_ref(x_463);
x_466 = lean_ctor_get(x_464, 0);
lean_inc(x_466);
lean_dec(x_464);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_467 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_466, x_52, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_465);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; 
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
lean_dec_ref(x_467);
x_470 = lean_ctor_get(x_468, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_468, 1);
lean_inc(x_471);
lean_dec(x_468);
x_472 = lean_st_ref_take(x_55, x_469);
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_472, 1);
lean_inc(x_474);
lean_dec_ref(x_472);
x_475 = lean_ctor_get(x_473, 1);
lean_inc(x_475);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 lean_ctor_release(x_473, 1);
 x_476 = x_473;
} else {
 lean_dec_ref(x_473);
 x_476 = lean_box(0);
}
if (lean_is_scalar(x_476)) {
 x_477 = lean_alloc_ctor(0, 2, 0);
} else {
 x_477 = x_476;
}
lean_ctor_set(x_477, 0, x_471);
lean_ctor_set(x_477, 1, x_475);
x_478 = lean_st_ref_set(x_55, x_477, x_474);
x_479 = lean_unbox(x_470);
lean_dec(x_470);
if (x_479 == 0)
{
lean_object* x_480; lean_object* x_481; 
x_480 = lean_ctor_get(x_478, 1);
lean_inc(x_480);
lean_dec_ref(x_478);
x_481 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_480);
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_481, 1);
lean_inc(x_483);
lean_dec_ref(x_481);
x_484 = lean_ctor_get(x_482, 0);
lean_inc(x_484);
lean_dec(x_482);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_485 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_484, x_53, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_483);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; uint8_t x_497; 
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_485, 1);
lean_inc(x_487);
lean_dec_ref(x_485);
x_488 = lean_ctor_get(x_486, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_486, 1);
lean_inc(x_489);
lean_dec(x_486);
x_490 = lean_st_ref_take(x_55, x_487);
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_490, 1);
lean_inc(x_492);
lean_dec_ref(x_490);
x_493 = lean_ctor_get(x_491, 1);
lean_inc(x_493);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 x_494 = x_491;
} else {
 lean_dec_ref(x_491);
 x_494 = lean_box(0);
}
if (lean_is_scalar(x_494)) {
 x_495 = lean_alloc_ctor(0, 2, 0);
} else {
 x_495 = x_494;
}
lean_ctor_set(x_495, 0, x_489);
lean_ctor_set(x_495, 1, x_493);
x_496 = lean_st_ref_set(x_55, x_495, x_492);
x_497 = lean_unbox(x_488);
lean_dec(x_488);
if (x_497 == 0)
{
lean_object* x_498; lean_object* x_499; 
x_498 = lean_ctor_get(x_496, 1);
lean_inc(x_498);
lean_dec_ref(x_496);
x_499 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_498);
if (lean_obj_tag(x_499) == 0)
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_500 = lean_ctor_get(x_499, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_499, 1);
lean_inc(x_501);
lean_dec_ref(x_499);
x_502 = lean_ctor_get(x_500, 0);
lean_inc(x_502);
lean_dec(x_500);
lean_inc(x_55);
x_503 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_502, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_501);
if (lean_obj_tag(x_503) == 0)
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; uint8_t x_516; 
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_503, 1);
lean_inc(x_505);
lean_dec_ref(x_503);
x_506 = lean_ctor_get(x_504, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_504, 1);
lean_inc(x_507);
lean_dec(x_504);
x_508 = lean_st_ref_take(x_55, x_505);
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
lean_dec_ref(x_508);
x_511 = lean_ctor_get(x_509, 1);
lean_inc(x_511);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 x_512 = x_509;
} else {
 lean_dec_ref(x_509);
 x_512 = lean_box(0);
}
if (lean_is_scalar(x_512)) {
 x_513 = lean_alloc_ctor(0, 2, 0);
} else {
 x_513 = x_512;
}
lean_ctor_set(x_513, 0, x_507);
lean_ctor_set(x_513, 1, x_511);
x_514 = lean_st_ref_set(x_55, x_513, x_510);
x_515 = lean_ctor_get(x_514, 1);
lean_inc(x_515);
lean_dec_ref(x_514);
x_516 = lean_unbox(x_506);
lean_dec(x_506);
x_12 = x_55;
x_13 = x_516;
x_14 = x_515;
goto block_32;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
lean_dec(x_55);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_517 = lean_ctor_get(x_503, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_503, 1);
lean_inc(x_518);
if (lean_is_exclusive(x_503)) {
 lean_ctor_release(x_503, 0);
 lean_ctor_release(x_503, 1);
 x_519 = x_503;
} else {
 lean_dec_ref(x_503);
 x_519 = lean_box(0);
}
if (lean_is_scalar(x_519)) {
 x_520 = lean_alloc_ctor(1, 2, 0);
} else {
 x_520 = x_519;
}
lean_ctor_set(x_520, 0, x_517);
lean_ctor_set(x_520, 1, x_518);
return x_520;
}
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_521 = lean_ctor_get(x_499, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_499, 1);
lean_inc(x_522);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 lean_ctor_release(x_499, 1);
 x_523 = x_499;
} else {
 lean_dec_ref(x_499);
 x_523 = lean_box(0);
}
if (lean_is_scalar(x_523)) {
 x_524 = lean_alloc_ctor(1, 2, 0);
} else {
 x_524 = x_523;
}
lean_ctor_set(x_524, 0, x_521);
lean_ctor_set(x_524, 1, x_522);
return x_524;
}
}
else
{
lean_object* x_525; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
x_525 = lean_ctor_get(x_496, 1);
lean_inc(x_525);
lean_dec_ref(x_496);
x_11 = x_525;
goto _start;
}
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_527 = lean_ctor_get(x_485, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_485, 1);
lean_inc(x_528);
if (lean_is_exclusive(x_485)) {
 lean_ctor_release(x_485, 0);
 lean_ctor_release(x_485, 1);
 x_529 = x_485;
} else {
 lean_dec_ref(x_485);
 x_529 = lean_box(0);
}
if (lean_is_scalar(x_529)) {
 x_530 = lean_alloc_ctor(1, 2, 0);
} else {
 x_530 = x_529;
}
lean_ctor_set(x_530, 0, x_527);
lean_ctor_set(x_530, 1, x_528);
return x_530;
}
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_531 = lean_ctor_get(x_481, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_481, 1);
lean_inc(x_532);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 x_533 = x_481;
} else {
 lean_dec_ref(x_481);
 x_533 = lean_box(0);
}
if (lean_is_scalar(x_533)) {
 x_534 = lean_alloc_ctor(1, 2, 0);
} else {
 x_534 = x_533;
}
lean_ctor_set(x_534, 0, x_531);
lean_ctor_set(x_534, 1, x_532);
return x_534;
}
}
else
{
lean_object* x_535; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
x_535 = lean_ctor_get(x_478, 1);
lean_inc(x_535);
lean_dec_ref(x_478);
x_11 = x_535;
goto _start;
}
}
else
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_537 = lean_ctor_get(x_467, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_467, 1);
lean_inc(x_538);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 x_539 = x_467;
} else {
 lean_dec_ref(x_467);
 x_539 = lean_box(0);
}
if (lean_is_scalar(x_539)) {
 x_540 = lean_alloc_ctor(1, 2, 0);
} else {
 x_540 = x_539;
}
lean_ctor_set(x_540, 0, x_537);
lean_ctor_set(x_540, 1, x_538);
return x_540;
}
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_541 = lean_ctor_get(x_463, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_463, 1);
lean_inc(x_542);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 x_543 = x_463;
} else {
 lean_dec_ref(x_463);
 x_543 = lean_box(0);
}
if (lean_is_scalar(x_543)) {
 x_544 = lean_alloc_ctor(1, 2, 0);
} else {
 x_544 = x_543;
}
lean_ctor_set(x_544, 0, x_541);
lean_ctor_set(x_544, 1, x_542);
return x_544;
}
}
else
{
lean_object* x_545; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
x_545 = lean_ctor_get(x_460, 1);
lean_inc(x_545);
lean_dec_ref(x_460);
x_11 = x_545;
goto _start;
}
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_547 = lean_ctor_get(x_449, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_449, 1);
lean_inc(x_548);
if (lean_is_exclusive(x_449)) {
 lean_ctor_release(x_449, 0);
 lean_ctor_release(x_449, 1);
 x_549 = x_449;
} else {
 lean_dec_ref(x_449);
 x_549 = lean_box(0);
}
if (lean_is_scalar(x_549)) {
 x_550 = lean_alloc_ctor(1, 2, 0);
} else {
 x_550 = x_549;
}
lean_ctor_set(x_550, 0, x_547);
lean_ctor_set(x_550, 1, x_548);
return x_550;
}
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_551 = lean_ctor_get(x_445, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_445, 1);
lean_inc(x_552);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 x_553 = x_445;
} else {
 lean_dec_ref(x_445);
 x_553 = lean_box(0);
}
if (lean_is_scalar(x_553)) {
 x_554 = lean_alloc_ctor(1, 2, 0);
} else {
 x_554 = x_553;
}
lean_ctor_set(x_554, 0, x_551);
lean_ctor_set(x_554, 1, x_552);
return x_554;
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_33 = x_55;
x_34 = x_441;
goto block_42;
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_33 = x_55;
x_34 = x_441;
goto block_42;
}
}
else
{
lean_object* x_555; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_555 = lean_ctor_get(x_438, 1);
lean_inc(x_555);
lean_dec_ref(x_438);
x_11 = x_555;
goto _start;
}
}
}
else
{
uint8_t x_557; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_557 = !lean_is_exclusive(x_123);
if (x_557 == 0)
{
return x_123;
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_558 = lean_ctor_get(x_123, 0);
x_559 = lean_ctor_get(x_123, 1);
lean_inc(x_559);
lean_inc(x_558);
lean_dec(x_123);
x_560 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_560, 0, x_558);
lean_ctor_set(x_560, 1, x_559);
return x_560;
}
}
}
else
{
uint8_t x_561; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_561 = !lean_is_exclusive(x_119);
if (x_561 == 0)
{
return x_119;
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_562 = lean_ctor_get(x_119, 0);
x_563 = lean_ctor_get(x_119, 1);
lean_inc(x_563);
lean_inc(x_562);
lean_dec(x_119);
x_564 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_564, 0, x_562);
lean_ctor_set(x_564, 1, x_563);
return x_564;
}
}
}
else
{
lean_object* x_565; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
x_565 = lean_ctor_get(x_116, 1);
lean_inc(x_565);
lean_dec_ref(x_116);
x_11 = x_565;
goto _start;
}
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; uint8_t x_570; 
x_567 = lean_ctor_get(x_112, 1);
lean_inc(x_567);
lean_dec(x_112);
x_568 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_568, 0, x_110);
lean_ctor_set(x_568, 1, x_567);
x_569 = lean_st_ref_set(x_55, x_568, x_113);
x_570 = lean_unbox(x_109);
lean_dec(x_109);
if (x_570 == 0)
{
lean_object* x_571; lean_object* x_572; 
x_571 = lean_ctor_get(x_569, 1);
lean_inc(x_571);
lean_dec_ref(x_569);
x_572 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_571);
if (lean_obj_tag(x_572) == 0)
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_572, 1);
lean_inc(x_574);
lean_dec_ref(x_572);
x_575 = lean_ctor_get(x_573, 0);
lean_inc(x_575);
lean_dec(x_573);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_576 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_575, x_50, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_574);
if (lean_obj_tag(x_576) == 0)
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; uint8_t x_588; 
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_576, 1);
lean_inc(x_578);
lean_dec_ref(x_576);
x_579 = lean_ctor_get(x_577, 0);
lean_inc(x_579);
x_580 = lean_ctor_get(x_577, 1);
lean_inc(x_580);
lean_dec(x_577);
x_581 = lean_st_ref_take(x_55, x_578);
x_582 = lean_ctor_get(x_581, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_581, 1);
lean_inc(x_583);
lean_dec_ref(x_581);
x_584 = lean_ctor_get(x_582, 1);
lean_inc(x_584);
if (lean_is_exclusive(x_582)) {
 lean_ctor_release(x_582, 0);
 lean_ctor_release(x_582, 1);
 x_585 = x_582;
} else {
 lean_dec_ref(x_582);
 x_585 = lean_box(0);
}
if (lean_is_scalar(x_585)) {
 x_586 = lean_alloc_ctor(0, 2, 0);
} else {
 x_586 = x_585;
}
lean_ctor_set(x_586, 0, x_580);
lean_ctor_set(x_586, 1, x_584);
x_587 = lean_st_ref_set(x_55, x_586, x_583);
x_588 = lean_unbox(x_579);
lean_dec(x_579);
if (x_588 == 0)
{
lean_object* x_589; lean_object* x_590; 
x_589 = lean_ctor_get(x_587, 1);
lean_inc(x_589);
lean_dec_ref(x_587);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_590 = l_Lean_Meta_Grind_splitNext(x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_589);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; uint8_t x_592; 
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
x_592 = lean_unbox(x_591);
lean_dec(x_591);
if (x_592 == 0)
{
lean_object* x_593; lean_object* x_594; 
x_593 = lean_ctor_get(x_590, 1);
lean_inc(x_593);
lean_dec_ref(x_590);
x_594 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_593);
if (lean_obj_tag(x_594) == 0)
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_595 = lean_ctor_get(x_594, 0);
lean_inc(x_595);
x_596 = lean_ctor_get(x_594, 1);
lean_inc(x_596);
lean_dec_ref(x_594);
x_597 = lean_ctor_get(x_595, 0);
lean_inc(x_597);
lean_dec(x_595);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_598 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_597, x_51, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_596);
if (lean_obj_tag(x_598) == 0)
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; uint8_t x_610; 
x_599 = lean_ctor_get(x_598, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_598, 1);
lean_inc(x_600);
lean_dec_ref(x_598);
x_601 = lean_ctor_get(x_599, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_599, 1);
lean_inc(x_602);
lean_dec(x_599);
x_603 = lean_st_ref_take(x_55, x_600);
x_604 = lean_ctor_get(x_603, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_603, 1);
lean_inc(x_605);
lean_dec_ref(x_603);
x_606 = lean_ctor_get(x_604, 1);
lean_inc(x_606);
if (lean_is_exclusive(x_604)) {
 lean_ctor_release(x_604, 0);
 lean_ctor_release(x_604, 1);
 x_607 = x_604;
} else {
 lean_dec_ref(x_604);
 x_607 = lean_box(0);
}
if (lean_is_scalar(x_607)) {
 x_608 = lean_alloc_ctor(0, 2, 0);
} else {
 x_608 = x_607;
}
lean_ctor_set(x_608, 0, x_602);
lean_ctor_set(x_608, 1, x_606);
x_609 = lean_st_ref_set(x_55, x_608, x_605);
x_610 = lean_unbox(x_601);
lean_dec(x_601);
if (x_610 == 0)
{
lean_object* x_611; lean_object* x_612; 
x_611 = lean_ctor_get(x_609, 1);
lean_inc(x_611);
lean_dec_ref(x_609);
x_612 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_611);
if (lean_obj_tag(x_612) == 0)
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_612, 1);
lean_inc(x_614);
lean_dec_ref(x_612);
x_615 = lean_ctor_get(x_613, 0);
lean_inc(x_615);
lean_dec(x_613);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_616 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_615, x_52, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_614);
if (lean_obj_tag(x_616) == 0)
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; uint8_t x_628; 
x_617 = lean_ctor_get(x_616, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_616, 1);
lean_inc(x_618);
lean_dec_ref(x_616);
x_619 = lean_ctor_get(x_617, 0);
lean_inc(x_619);
x_620 = lean_ctor_get(x_617, 1);
lean_inc(x_620);
lean_dec(x_617);
x_621 = lean_st_ref_take(x_55, x_618);
x_622 = lean_ctor_get(x_621, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_621, 1);
lean_inc(x_623);
lean_dec_ref(x_621);
x_624 = lean_ctor_get(x_622, 1);
lean_inc(x_624);
if (lean_is_exclusive(x_622)) {
 lean_ctor_release(x_622, 0);
 lean_ctor_release(x_622, 1);
 x_625 = x_622;
} else {
 lean_dec_ref(x_622);
 x_625 = lean_box(0);
}
if (lean_is_scalar(x_625)) {
 x_626 = lean_alloc_ctor(0, 2, 0);
} else {
 x_626 = x_625;
}
lean_ctor_set(x_626, 0, x_620);
lean_ctor_set(x_626, 1, x_624);
x_627 = lean_st_ref_set(x_55, x_626, x_623);
x_628 = lean_unbox(x_619);
lean_dec(x_619);
if (x_628 == 0)
{
lean_object* x_629; lean_object* x_630; 
x_629 = lean_ctor_get(x_627, 1);
lean_inc(x_629);
lean_dec_ref(x_627);
x_630 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_629);
if (lean_obj_tag(x_630) == 0)
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
x_631 = lean_ctor_get(x_630, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_630, 1);
lean_inc(x_632);
lean_dec_ref(x_630);
x_633 = lean_ctor_get(x_631, 0);
lean_inc(x_633);
lean_dec(x_631);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_634 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_633, x_53, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_632);
if (lean_obj_tag(x_634) == 0)
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; uint8_t x_646; 
x_635 = lean_ctor_get(x_634, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_634, 1);
lean_inc(x_636);
lean_dec_ref(x_634);
x_637 = lean_ctor_get(x_635, 0);
lean_inc(x_637);
x_638 = lean_ctor_get(x_635, 1);
lean_inc(x_638);
lean_dec(x_635);
x_639 = lean_st_ref_take(x_55, x_636);
x_640 = lean_ctor_get(x_639, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_639, 1);
lean_inc(x_641);
lean_dec_ref(x_639);
x_642 = lean_ctor_get(x_640, 1);
lean_inc(x_642);
if (lean_is_exclusive(x_640)) {
 lean_ctor_release(x_640, 0);
 lean_ctor_release(x_640, 1);
 x_643 = x_640;
} else {
 lean_dec_ref(x_640);
 x_643 = lean_box(0);
}
if (lean_is_scalar(x_643)) {
 x_644 = lean_alloc_ctor(0, 2, 0);
} else {
 x_644 = x_643;
}
lean_ctor_set(x_644, 0, x_638);
lean_ctor_set(x_644, 1, x_642);
x_645 = lean_st_ref_set(x_55, x_644, x_641);
x_646 = lean_unbox(x_637);
lean_dec(x_637);
if (x_646 == 0)
{
lean_object* x_647; lean_object* x_648; 
x_647 = lean_ctor_get(x_645, 1);
lean_inc(x_647);
lean_dec_ref(x_645);
x_648 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_647);
if (lean_obj_tag(x_648) == 0)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
x_649 = lean_ctor_get(x_648, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_648, 1);
lean_inc(x_650);
lean_dec_ref(x_648);
x_651 = lean_ctor_get(x_649, 0);
lean_inc(x_651);
lean_dec(x_649);
lean_inc(x_55);
x_652 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_651, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_650);
if (lean_obj_tag(x_652) == 0)
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; uint8_t x_665; 
x_653 = lean_ctor_get(x_652, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_652, 1);
lean_inc(x_654);
lean_dec_ref(x_652);
x_655 = lean_ctor_get(x_653, 0);
lean_inc(x_655);
x_656 = lean_ctor_get(x_653, 1);
lean_inc(x_656);
lean_dec(x_653);
x_657 = lean_st_ref_take(x_55, x_654);
x_658 = lean_ctor_get(x_657, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_657, 1);
lean_inc(x_659);
lean_dec_ref(x_657);
x_660 = lean_ctor_get(x_658, 1);
lean_inc(x_660);
if (lean_is_exclusive(x_658)) {
 lean_ctor_release(x_658, 0);
 lean_ctor_release(x_658, 1);
 x_661 = x_658;
} else {
 lean_dec_ref(x_658);
 x_661 = lean_box(0);
}
if (lean_is_scalar(x_661)) {
 x_662 = lean_alloc_ctor(0, 2, 0);
} else {
 x_662 = x_661;
}
lean_ctor_set(x_662, 0, x_656);
lean_ctor_set(x_662, 1, x_660);
x_663 = lean_st_ref_set(x_55, x_662, x_659);
x_664 = lean_ctor_get(x_663, 1);
lean_inc(x_664);
lean_dec_ref(x_663);
x_665 = lean_unbox(x_655);
lean_dec(x_655);
x_12 = x_55;
x_13 = x_665;
x_14 = x_664;
goto block_32;
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
lean_dec(x_55);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_666 = lean_ctor_get(x_652, 0);
lean_inc(x_666);
x_667 = lean_ctor_get(x_652, 1);
lean_inc(x_667);
if (lean_is_exclusive(x_652)) {
 lean_ctor_release(x_652, 0);
 lean_ctor_release(x_652, 1);
 x_668 = x_652;
} else {
 lean_dec_ref(x_652);
 x_668 = lean_box(0);
}
if (lean_is_scalar(x_668)) {
 x_669 = lean_alloc_ctor(1, 2, 0);
} else {
 x_669 = x_668;
}
lean_ctor_set(x_669, 0, x_666);
lean_ctor_set(x_669, 1, x_667);
return x_669;
}
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_670 = lean_ctor_get(x_648, 0);
lean_inc(x_670);
x_671 = lean_ctor_get(x_648, 1);
lean_inc(x_671);
if (lean_is_exclusive(x_648)) {
 lean_ctor_release(x_648, 0);
 lean_ctor_release(x_648, 1);
 x_672 = x_648;
} else {
 lean_dec_ref(x_648);
 x_672 = lean_box(0);
}
if (lean_is_scalar(x_672)) {
 x_673 = lean_alloc_ctor(1, 2, 0);
} else {
 x_673 = x_672;
}
lean_ctor_set(x_673, 0, x_670);
lean_ctor_set(x_673, 1, x_671);
return x_673;
}
}
else
{
lean_object* x_674; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
x_674 = lean_ctor_get(x_645, 1);
lean_inc(x_674);
lean_dec_ref(x_645);
x_11 = x_674;
goto _start;
}
}
else
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_676 = lean_ctor_get(x_634, 0);
lean_inc(x_676);
x_677 = lean_ctor_get(x_634, 1);
lean_inc(x_677);
if (lean_is_exclusive(x_634)) {
 lean_ctor_release(x_634, 0);
 lean_ctor_release(x_634, 1);
 x_678 = x_634;
} else {
 lean_dec_ref(x_634);
 x_678 = lean_box(0);
}
if (lean_is_scalar(x_678)) {
 x_679 = lean_alloc_ctor(1, 2, 0);
} else {
 x_679 = x_678;
}
lean_ctor_set(x_679, 0, x_676);
lean_ctor_set(x_679, 1, x_677);
return x_679;
}
}
else
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_680 = lean_ctor_get(x_630, 0);
lean_inc(x_680);
x_681 = lean_ctor_get(x_630, 1);
lean_inc(x_681);
if (lean_is_exclusive(x_630)) {
 lean_ctor_release(x_630, 0);
 lean_ctor_release(x_630, 1);
 x_682 = x_630;
} else {
 lean_dec_ref(x_630);
 x_682 = lean_box(0);
}
if (lean_is_scalar(x_682)) {
 x_683 = lean_alloc_ctor(1, 2, 0);
} else {
 x_683 = x_682;
}
lean_ctor_set(x_683, 0, x_680);
lean_ctor_set(x_683, 1, x_681);
return x_683;
}
}
else
{
lean_object* x_684; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
x_684 = lean_ctor_get(x_627, 1);
lean_inc(x_684);
lean_dec_ref(x_627);
x_11 = x_684;
goto _start;
}
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_686 = lean_ctor_get(x_616, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_616, 1);
lean_inc(x_687);
if (lean_is_exclusive(x_616)) {
 lean_ctor_release(x_616, 0);
 lean_ctor_release(x_616, 1);
 x_688 = x_616;
} else {
 lean_dec_ref(x_616);
 x_688 = lean_box(0);
}
if (lean_is_scalar(x_688)) {
 x_689 = lean_alloc_ctor(1, 2, 0);
} else {
 x_689 = x_688;
}
lean_ctor_set(x_689, 0, x_686);
lean_ctor_set(x_689, 1, x_687);
return x_689;
}
}
else
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_690 = lean_ctor_get(x_612, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_612, 1);
lean_inc(x_691);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 x_692 = x_612;
} else {
 lean_dec_ref(x_612);
 x_692 = lean_box(0);
}
if (lean_is_scalar(x_692)) {
 x_693 = lean_alloc_ctor(1, 2, 0);
} else {
 x_693 = x_692;
}
lean_ctor_set(x_693, 0, x_690);
lean_ctor_set(x_693, 1, x_691);
return x_693;
}
}
else
{
lean_object* x_694; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
x_694 = lean_ctor_get(x_609, 1);
lean_inc(x_694);
lean_dec_ref(x_609);
x_11 = x_694;
goto _start;
}
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_696 = lean_ctor_get(x_598, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_598, 1);
lean_inc(x_697);
if (lean_is_exclusive(x_598)) {
 lean_ctor_release(x_598, 0);
 lean_ctor_release(x_598, 1);
 x_698 = x_598;
} else {
 lean_dec_ref(x_598);
 x_698 = lean_box(0);
}
if (lean_is_scalar(x_698)) {
 x_699 = lean_alloc_ctor(1, 2, 0);
} else {
 x_699 = x_698;
}
lean_ctor_set(x_699, 0, x_696);
lean_ctor_set(x_699, 1, x_697);
return x_699;
}
}
else
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_700 = lean_ctor_get(x_594, 0);
lean_inc(x_700);
x_701 = lean_ctor_get(x_594, 1);
lean_inc(x_701);
if (lean_is_exclusive(x_594)) {
 lean_ctor_release(x_594, 0);
 lean_ctor_release(x_594, 1);
 x_702 = x_594;
} else {
 lean_dec_ref(x_594);
 x_702 = lean_box(0);
}
if (lean_is_scalar(x_702)) {
 x_703 = lean_alloc_ctor(1, 2, 0);
} else {
 x_703 = x_702;
}
lean_ctor_set(x_703, 0, x_700);
lean_ctor_set(x_703, 1, x_701);
return x_703;
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_33 = x_55;
x_34 = x_590;
goto block_42;
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_33 = x_55;
x_34 = x_590;
goto block_42;
}
}
else
{
lean_object* x_704; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_704 = lean_ctor_get(x_587, 1);
lean_inc(x_704);
lean_dec_ref(x_587);
x_11 = x_704;
goto _start;
}
}
else
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_706 = lean_ctor_get(x_576, 0);
lean_inc(x_706);
x_707 = lean_ctor_get(x_576, 1);
lean_inc(x_707);
if (lean_is_exclusive(x_576)) {
 lean_ctor_release(x_576, 0);
 lean_ctor_release(x_576, 1);
 x_708 = x_576;
} else {
 lean_dec_ref(x_576);
 x_708 = lean_box(0);
}
if (lean_is_scalar(x_708)) {
 x_709 = lean_alloc_ctor(1, 2, 0);
} else {
 x_709 = x_708;
}
lean_ctor_set(x_709, 0, x_706);
lean_ctor_set(x_709, 1, x_707);
return x_709;
}
}
else
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_710 = lean_ctor_get(x_572, 0);
lean_inc(x_710);
x_711 = lean_ctor_get(x_572, 1);
lean_inc(x_711);
if (lean_is_exclusive(x_572)) {
 lean_ctor_release(x_572, 0);
 lean_ctor_release(x_572, 1);
 x_712 = x_572;
} else {
 lean_dec_ref(x_572);
 x_712 = lean_box(0);
}
if (lean_is_scalar(x_712)) {
 x_713 = lean_alloc_ctor(1, 2, 0);
} else {
 x_713 = x_712;
}
lean_ctor_set(x_713, 0, x_710);
lean_ctor_set(x_713, 1, x_711);
return x_713;
}
}
else
{
lean_object* x_714; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
x_714 = lean_ctor_get(x_569, 1);
lean_inc(x_714);
lean_dec_ref(x_569);
x_11 = x_714;
goto _start;
}
}
}
else
{
uint8_t x_716; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_716 = !lean_is_exclusive(x_106);
if (x_716 == 0)
{
return x_106;
}
else
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_717 = lean_ctor_get(x_106, 0);
x_718 = lean_ctor_get(x_106, 1);
lean_inc(x_718);
lean_inc(x_717);
lean_dec(x_106);
x_719 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_719, 0, x_717);
lean_ctor_set(x_719, 1, x_718);
return x_719;
}
}
}
else
{
uint8_t x_720; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_720 = !lean_is_exclusive(x_102);
if (x_720 == 0)
{
return x_102;
}
else
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; 
x_721 = lean_ctor_get(x_102, 0);
x_722 = lean_ctor_get(x_102, 1);
lean_inc(x_722);
lean_inc(x_721);
lean_dec(x_102);
x_723 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_723, 0, x_721);
lean_ctor_set(x_723, 1, x_722);
return x_723;
}
}
}
else
{
lean_object* x_724; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
x_724 = lean_ctor_get(x_99, 1);
lean_inc(x_724);
lean_dec_ref(x_99);
x_11 = x_724;
goto _start;
}
}
else
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; uint8_t x_729; 
x_726 = lean_ctor_get(x_95, 1);
lean_inc(x_726);
lean_dec(x_95);
x_727 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_727, 0, x_93);
lean_ctor_set(x_727, 1, x_726);
x_728 = lean_st_ref_set(x_55, x_727, x_96);
x_729 = lean_unbox(x_92);
lean_dec(x_92);
if (x_729 == 0)
{
lean_object* x_730; lean_object* x_731; 
x_730 = lean_ctor_get(x_728, 1);
lean_inc(x_730);
lean_dec_ref(x_728);
x_731 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_730);
if (lean_obj_tag(x_731) == 0)
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; 
x_732 = lean_ctor_get(x_731, 0);
lean_inc(x_732);
x_733 = lean_ctor_get(x_731, 1);
lean_inc(x_733);
lean_dec_ref(x_731);
x_734 = lean_ctor_get(x_732, 0);
lean_inc(x_734);
lean_dec(x_732);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_735 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_734, x_49, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_733);
if (lean_obj_tag(x_735) == 0)
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; uint8_t x_747; 
x_736 = lean_ctor_get(x_735, 0);
lean_inc(x_736);
x_737 = lean_ctor_get(x_735, 1);
lean_inc(x_737);
lean_dec_ref(x_735);
x_738 = lean_ctor_get(x_736, 0);
lean_inc(x_738);
x_739 = lean_ctor_get(x_736, 1);
lean_inc(x_739);
lean_dec(x_736);
x_740 = lean_st_ref_take(x_55, x_737);
x_741 = lean_ctor_get(x_740, 0);
lean_inc(x_741);
x_742 = lean_ctor_get(x_740, 1);
lean_inc(x_742);
lean_dec_ref(x_740);
x_743 = lean_ctor_get(x_741, 1);
lean_inc(x_743);
if (lean_is_exclusive(x_741)) {
 lean_ctor_release(x_741, 0);
 lean_ctor_release(x_741, 1);
 x_744 = x_741;
} else {
 lean_dec_ref(x_741);
 x_744 = lean_box(0);
}
if (lean_is_scalar(x_744)) {
 x_745 = lean_alloc_ctor(0, 2, 0);
} else {
 x_745 = x_744;
}
lean_ctor_set(x_745, 0, x_739);
lean_ctor_set(x_745, 1, x_743);
x_746 = lean_st_ref_set(x_55, x_745, x_742);
x_747 = lean_unbox(x_738);
lean_dec(x_738);
if (x_747 == 0)
{
lean_object* x_748; lean_object* x_749; 
x_748 = lean_ctor_get(x_746, 1);
lean_inc(x_748);
lean_dec_ref(x_746);
x_749 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_748);
if (lean_obj_tag(x_749) == 0)
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; 
x_750 = lean_ctor_get(x_749, 0);
lean_inc(x_750);
x_751 = lean_ctor_get(x_749, 1);
lean_inc(x_751);
lean_dec_ref(x_749);
x_752 = lean_ctor_get(x_750, 0);
lean_inc(x_752);
lean_dec(x_750);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_753 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_752, x_50, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_751);
if (lean_obj_tag(x_753) == 0)
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; uint8_t x_765; 
x_754 = lean_ctor_get(x_753, 0);
lean_inc(x_754);
x_755 = lean_ctor_get(x_753, 1);
lean_inc(x_755);
lean_dec_ref(x_753);
x_756 = lean_ctor_get(x_754, 0);
lean_inc(x_756);
x_757 = lean_ctor_get(x_754, 1);
lean_inc(x_757);
lean_dec(x_754);
x_758 = lean_st_ref_take(x_55, x_755);
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_758, 1);
lean_inc(x_760);
lean_dec_ref(x_758);
x_761 = lean_ctor_get(x_759, 1);
lean_inc(x_761);
if (lean_is_exclusive(x_759)) {
 lean_ctor_release(x_759, 0);
 lean_ctor_release(x_759, 1);
 x_762 = x_759;
} else {
 lean_dec_ref(x_759);
 x_762 = lean_box(0);
}
if (lean_is_scalar(x_762)) {
 x_763 = lean_alloc_ctor(0, 2, 0);
} else {
 x_763 = x_762;
}
lean_ctor_set(x_763, 0, x_757);
lean_ctor_set(x_763, 1, x_761);
x_764 = lean_st_ref_set(x_55, x_763, x_760);
x_765 = lean_unbox(x_756);
lean_dec(x_756);
if (x_765 == 0)
{
lean_object* x_766; lean_object* x_767; 
x_766 = lean_ctor_get(x_764, 1);
lean_inc(x_766);
lean_dec_ref(x_764);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_767 = l_Lean_Meta_Grind_splitNext(x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_766);
if (lean_obj_tag(x_767) == 0)
{
lean_object* x_768; uint8_t x_769; 
x_768 = lean_ctor_get(x_767, 0);
lean_inc(x_768);
x_769 = lean_unbox(x_768);
lean_dec(x_768);
if (x_769 == 0)
{
lean_object* x_770; lean_object* x_771; 
x_770 = lean_ctor_get(x_767, 1);
lean_inc(x_770);
lean_dec_ref(x_767);
x_771 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_770);
if (lean_obj_tag(x_771) == 0)
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; 
x_772 = lean_ctor_get(x_771, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_771, 1);
lean_inc(x_773);
lean_dec_ref(x_771);
x_774 = lean_ctor_get(x_772, 0);
lean_inc(x_774);
lean_dec(x_772);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_775 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_774, x_51, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_773);
if (lean_obj_tag(x_775) == 0)
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; uint8_t x_787; 
x_776 = lean_ctor_get(x_775, 0);
lean_inc(x_776);
x_777 = lean_ctor_get(x_775, 1);
lean_inc(x_777);
lean_dec_ref(x_775);
x_778 = lean_ctor_get(x_776, 0);
lean_inc(x_778);
x_779 = lean_ctor_get(x_776, 1);
lean_inc(x_779);
lean_dec(x_776);
x_780 = lean_st_ref_take(x_55, x_777);
x_781 = lean_ctor_get(x_780, 0);
lean_inc(x_781);
x_782 = lean_ctor_get(x_780, 1);
lean_inc(x_782);
lean_dec_ref(x_780);
x_783 = lean_ctor_get(x_781, 1);
lean_inc(x_783);
if (lean_is_exclusive(x_781)) {
 lean_ctor_release(x_781, 0);
 lean_ctor_release(x_781, 1);
 x_784 = x_781;
} else {
 lean_dec_ref(x_781);
 x_784 = lean_box(0);
}
if (lean_is_scalar(x_784)) {
 x_785 = lean_alloc_ctor(0, 2, 0);
} else {
 x_785 = x_784;
}
lean_ctor_set(x_785, 0, x_779);
lean_ctor_set(x_785, 1, x_783);
x_786 = lean_st_ref_set(x_55, x_785, x_782);
x_787 = lean_unbox(x_778);
lean_dec(x_778);
if (x_787 == 0)
{
lean_object* x_788; lean_object* x_789; 
x_788 = lean_ctor_get(x_786, 1);
lean_inc(x_788);
lean_dec_ref(x_786);
x_789 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_788);
if (lean_obj_tag(x_789) == 0)
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; 
x_790 = lean_ctor_get(x_789, 0);
lean_inc(x_790);
x_791 = lean_ctor_get(x_789, 1);
lean_inc(x_791);
lean_dec_ref(x_789);
x_792 = lean_ctor_get(x_790, 0);
lean_inc(x_792);
lean_dec(x_790);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_793 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_792, x_52, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_791);
if (lean_obj_tag(x_793) == 0)
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; uint8_t x_805; 
x_794 = lean_ctor_get(x_793, 0);
lean_inc(x_794);
x_795 = lean_ctor_get(x_793, 1);
lean_inc(x_795);
lean_dec_ref(x_793);
x_796 = lean_ctor_get(x_794, 0);
lean_inc(x_796);
x_797 = lean_ctor_get(x_794, 1);
lean_inc(x_797);
lean_dec(x_794);
x_798 = lean_st_ref_take(x_55, x_795);
x_799 = lean_ctor_get(x_798, 0);
lean_inc(x_799);
x_800 = lean_ctor_get(x_798, 1);
lean_inc(x_800);
lean_dec_ref(x_798);
x_801 = lean_ctor_get(x_799, 1);
lean_inc(x_801);
if (lean_is_exclusive(x_799)) {
 lean_ctor_release(x_799, 0);
 lean_ctor_release(x_799, 1);
 x_802 = x_799;
} else {
 lean_dec_ref(x_799);
 x_802 = lean_box(0);
}
if (lean_is_scalar(x_802)) {
 x_803 = lean_alloc_ctor(0, 2, 0);
} else {
 x_803 = x_802;
}
lean_ctor_set(x_803, 0, x_797);
lean_ctor_set(x_803, 1, x_801);
x_804 = lean_st_ref_set(x_55, x_803, x_800);
x_805 = lean_unbox(x_796);
lean_dec(x_796);
if (x_805 == 0)
{
lean_object* x_806; lean_object* x_807; 
x_806 = lean_ctor_get(x_804, 1);
lean_inc(x_806);
lean_dec_ref(x_804);
x_807 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_806);
if (lean_obj_tag(x_807) == 0)
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_808 = lean_ctor_get(x_807, 0);
lean_inc(x_808);
x_809 = lean_ctor_get(x_807, 1);
lean_inc(x_809);
lean_dec_ref(x_807);
x_810 = lean_ctor_get(x_808, 0);
lean_inc(x_810);
lean_dec(x_808);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_811 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_810, x_53, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_809);
if (lean_obj_tag(x_811) == 0)
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; uint8_t x_823; 
x_812 = lean_ctor_get(x_811, 0);
lean_inc(x_812);
x_813 = lean_ctor_get(x_811, 1);
lean_inc(x_813);
lean_dec_ref(x_811);
x_814 = lean_ctor_get(x_812, 0);
lean_inc(x_814);
x_815 = lean_ctor_get(x_812, 1);
lean_inc(x_815);
lean_dec(x_812);
x_816 = lean_st_ref_take(x_55, x_813);
x_817 = lean_ctor_get(x_816, 0);
lean_inc(x_817);
x_818 = lean_ctor_get(x_816, 1);
lean_inc(x_818);
lean_dec_ref(x_816);
x_819 = lean_ctor_get(x_817, 1);
lean_inc(x_819);
if (lean_is_exclusive(x_817)) {
 lean_ctor_release(x_817, 0);
 lean_ctor_release(x_817, 1);
 x_820 = x_817;
} else {
 lean_dec_ref(x_817);
 x_820 = lean_box(0);
}
if (lean_is_scalar(x_820)) {
 x_821 = lean_alloc_ctor(0, 2, 0);
} else {
 x_821 = x_820;
}
lean_ctor_set(x_821, 0, x_815);
lean_ctor_set(x_821, 1, x_819);
x_822 = lean_st_ref_set(x_55, x_821, x_818);
x_823 = lean_unbox(x_814);
lean_dec(x_814);
if (x_823 == 0)
{
lean_object* x_824; lean_object* x_825; 
x_824 = lean_ctor_get(x_822, 1);
lean_inc(x_824);
lean_dec_ref(x_822);
x_825 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_824);
if (lean_obj_tag(x_825) == 0)
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; 
x_826 = lean_ctor_get(x_825, 0);
lean_inc(x_826);
x_827 = lean_ctor_get(x_825, 1);
lean_inc(x_827);
lean_dec_ref(x_825);
x_828 = lean_ctor_get(x_826, 0);
lean_inc(x_828);
lean_dec(x_826);
lean_inc(x_55);
x_829 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_828, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_827);
if (lean_obj_tag(x_829) == 0)
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; uint8_t x_842; 
x_830 = lean_ctor_get(x_829, 0);
lean_inc(x_830);
x_831 = lean_ctor_get(x_829, 1);
lean_inc(x_831);
lean_dec_ref(x_829);
x_832 = lean_ctor_get(x_830, 0);
lean_inc(x_832);
x_833 = lean_ctor_get(x_830, 1);
lean_inc(x_833);
lean_dec(x_830);
x_834 = lean_st_ref_take(x_55, x_831);
x_835 = lean_ctor_get(x_834, 0);
lean_inc(x_835);
x_836 = lean_ctor_get(x_834, 1);
lean_inc(x_836);
lean_dec_ref(x_834);
x_837 = lean_ctor_get(x_835, 1);
lean_inc(x_837);
if (lean_is_exclusive(x_835)) {
 lean_ctor_release(x_835, 0);
 lean_ctor_release(x_835, 1);
 x_838 = x_835;
} else {
 lean_dec_ref(x_835);
 x_838 = lean_box(0);
}
if (lean_is_scalar(x_838)) {
 x_839 = lean_alloc_ctor(0, 2, 0);
} else {
 x_839 = x_838;
}
lean_ctor_set(x_839, 0, x_833);
lean_ctor_set(x_839, 1, x_837);
x_840 = lean_st_ref_set(x_55, x_839, x_836);
x_841 = lean_ctor_get(x_840, 1);
lean_inc(x_841);
lean_dec_ref(x_840);
x_842 = lean_unbox(x_832);
lean_dec(x_832);
x_12 = x_55;
x_13 = x_842;
x_14 = x_841;
goto block_32;
}
else
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; 
lean_dec(x_55);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_843 = lean_ctor_get(x_829, 0);
lean_inc(x_843);
x_844 = lean_ctor_get(x_829, 1);
lean_inc(x_844);
if (lean_is_exclusive(x_829)) {
 lean_ctor_release(x_829, 0);
 lean_ctor_release(x_829, 1);
 x_845 = x_829;
} else {
 lean_dec_ref(x_829);
 x_845 = lean_box(0);
}
if (lean_is_scalar(x_845)) {
 x_846 = lean_alloc_ctor(1, 2, 0);
} else {
 x_846 = x_845;
}
lean_ctor_set(x_846, 0, x_843);
lean_ctor_set(x_846, 1, x_844);
return x_846;
}
}
else
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_847 = lean_ctor_get(x_825, 0);
lean_inc(x_847);
x_848 = lean_ctor_get(x_825, 1);
lean_inc(x_848);
if (lean_is_exclusive(x_825)) {
 lean_ctor_release(x_825, 0);
 lean_ctor_release(x_825, 1);
 x_849 = x_825;
} else {
 lean_dec_ref(x_825);
 x_849 = lean_box(0);
}
if (lean_is_scalar(x_849)) {
 x_850 = lean_alloc_ctor(1, 2, 0);
} else {
 x_850 = x_849;
}
lean_ctor_set(x_850, 0, x_847);
lean_ctor_set(x_850, 1, x_848);
return x_850;
}
}
else
{
lean_object* x_851; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
x_851 = lean_ctor_get(x_822, 1);
lean_inc(x_851);
lean_dec_ref(x_822);
x_11 = x_851;
goto _start;
}
}
else
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_853 = lean_ctor_get(x_811, 0);
lean_inc(x_853);
x_854 = lean_ctor_get(x_811, 1);
lean_inc(x_854);
if (lean_is_exclusive(x_811)) {
 lean_ctor_release(x_811, 0);
 lean_ctor_release(x_811, 1);
 x_855 = x_811;
} else {
 lean_dec_ref(x_811);
 x_855 = lean_box(0);
}
if (lean_is_scalar(x_855)) {
 x_856 = lean_alloc_ctor(1, 2, 0);
} else {
 x_856 = x_855;
}
lean_ctor_set(x_856, 0, x_853);
lean_ctor_set(x_856, 1, x_854);
return x_856;
}
}
else
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_857 = lean_ctor_get(x_807, 0);
lean_inc(x_857);
x_858 = lean_ctor_get(x_807, 1);
lean_inc(x_858);
if (lean_is_exclusive(x_807)) {
 lean_ctor_release(x_807, 0);
 lean_ctor_release(x_807, 1);
 x_859 = x_807;
} else {
 lean_dec_ref(x_807);
 x_859 = lean_box(0);
}
if (lean_is_scalar(x_859)) {
 x_860 = lean_alloc_ctor(1, 2, 0);
} else {
 x_860 = x_859;
}
lean_ctor_set(x_860, 0, x_857);
lean_ctor_set(x_860, 1, x_858);
return x_860;
}
}
else
{
lean_object* x_861; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
x_861 = lean_ctor_get(x_804, 1);
lean_inc(x_861);
lean_dec_ref(x_804);
x_11 = x_861;
goto _start;
}
}
else
{
lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_863 = lean_ctor_get(x_793, 0);
lean_inc(x_863);
x_864 = lean_ctor_get(x_793, 1);
lean_inc(x_864);
if (lean_is_exclusive(x_793)) {
 lean_ctor_release(x_793, 0);
 lean_ctor_release(x_793, 1);
 x_865 = x_793;
} else {
 lean_dec_ref(x_793);
 x_865 = lean_box(0);
}
if (lean_is_scalar(x_865)) {
 x_866 = lean_alloc_ctor(1, 2, 0);
} else {
 x_866 = x_865;
}
lean_ctor_set(x_866, 0, x_863);
lean_ctor_set(x_866, 1, x_864);
return x_866;
}
}
else
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_867 = lean_ctor_get(x_789, 0);
lean_inc(x_867);
x_868 = lean_ctor_get(x_789, 1);
lean_inc(x_868);
if (lean_is_exclusive(x_789)) {
 lean_ctor_release(x_789, 0);
 lean_ctor_release(x_789, 1);
 x_869 = x_789;
} else {
 lean_dec_ref(x_789);
 x_869 = lean_box(0);
}
if (lean_is_scalar(x_869)) {
 x_870 = lean_alloc_ctor(1, 2, 0);
} else {
 x_870 = x_869;
}
lean_ctor_set(x_870, 0, x_867);
lean_ctor_set(x_870, 1, x_868);
return x_870;
}
}
else
{
lean_object* x_871; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
x_871 = lean_ctor_get(x_786, 1);
lean_inc(x_871);
lean_dec_ref(x_786);
x_11 = x_871;
goto _start;
}
}
else
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_873 = lean_ctor_get(x_775, 0);
lean_inc(x_873);
x_874 = lean_ctor_get(x_775, 1);
lean_inc(x_874);
if (lean_is_exclusive(x_775)) {
 lean_ctor_release(x_775, 0);
 lean_ctor_release(x_775, 1);
 x_875 = x_775;
} else {
 lean_dec_ref(x_775);
 x_875 = lean_box(0);
}
if (lean_is_scalar(x_875)) {
 x_876 = lean_alloc_ctor(1, 2, 0);
} else {
 x_876 = x_875;
}
lean_ctor_set(x_876, 0, x_873);
lean_ctor_set(x_876, 1, x_874);
return x_876;
}
}
else
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_877 = lean_ctor_get(x_771, 0);
lean_inc(x_877);
x_878 = lean_ctor_get(x_771, 1);
lean_inc(x_878);
if (lean_is_exclusive(x_771)) {
 lean_ctor_release(x_771, 0);
 lean_ctor_release(x_771, 1);
 x_879 = x_771;
} else {
 lean_dec_ref(x_771);
 x_879 = lean_box(0);
}
if (lean_is_scalar(x_879)) {
 x_880 = lean_alloc_ctor(1, 2, 0);
} else {
 x_880 = x_879;
}
lean_ctor_set(x_880, 0, x_877);
lean_ctor_set(x_880, 1, x_878);
return x_880;
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_33 = x_55;
x_34 = x_767;
goto block_42;
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_33 = x_55;
x_34 = x_767;
goto block_42;
}
}
else
{
lean_object* x_881; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_881 = lean_ctor_get(x_764, 1);
lean_inc(x_881);
lean_dec_ref(x_764);
x_11 = x_881;
goto _start;
}
}
else
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_883 = lean_ctor_get(x_753, 0);
lean_inc(x_883);
x_884 = lean_ctor_get(x_753, 1);
lean_inc(x_884);
if (lean_is_exclusive(x_753)) {
 lean_ctor_release(x_753, 0);
 lean_ctor_release(x_753, 1);
 x_885 = x_753;
} else {
 lean_dec_ref(x_753);
 x_885 = lean_box(0);
}
if (lean_is_scalar(x_885)) {
 x_886 = lean_alloc_ctor(1, 2, 0);
} else {
 x_886 = x_885;
}
lean_ctor_set(x_886, 0, x_883);
lean_ctor_set(x_886, 1, x_884);
return x_886;
}
}
else
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_887 = lean_ctor_get(x_749, 0);
lean_inc(x_887);
x_888 = lean_ctor_get(x_749, 1);
lean_inc(x_888);
if (lean_is_exclusive(x_749)) {
 lean_ctor_release(x_749, 0);
 lean_ctor_release(x_749, 1);
 x_889 = x_749;
} else {
 lean_dec_ref(x_749);
 x_889 = lean_box(0);
}
if (lean_is_scalar(x_889)) {
 x_890 = lean_alloc_ctor(1, 2, 0);
} else {
 x_890 = x_889;
}
lean_ctor_set(x_890, 0, x_887);
lean_ctor_set(x_890, 1, x_888);
return x_890;
}
}
else
{
lean_object* x_891; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
x_891 = lean_ctor_get(x_746, 1);
lean_inc(x_891);
lean_dec_ref(x_746);
x_11 = x_891;
goto _start;
}
}
else
{
lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_893 = lean_ctor_get(x_735, 0);
lean_inc(x_893);
x_894 = lean_ctor_get(x_735, 1);
lean_inc(x_894);
if (lean_is_exclusive(x_735)) {
 lean_ctor_release(x_735, 0);
 lean_ctor_release(x_735, 1);
 x_895 = x_735;
} else {
 lean_dec_ref(x_735);
 x_895 = lean_box(0);
}
if (lean_is_scalar(x_895)) {
 x_896 = lean_alloc_ctor(1, 2, 0);
} else {
 x_896 = x_895;
}
lean_ctor_set(x_896, 0, x_893);
lean_ctor_set(x_896, 1, x_894);
return x_896;
}
}
else
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_897 = lean_ctor_get(x_731, 0);
lean_inc(x_897);
x_898 = lean_ctor_get(x_731, 1);
lean_inc(x_898);
if (lean_is_exclusive(x_731)) {
 lean_ctor_release(x_731, 0);
 lean_ctor_release(x_731, 1);
 x_899 = x_731;
} else {
 lean_dec_ref(x_731);
 x_899 = lean_box(0);
}
if (lean_is_scalar(x_899)) {
 x_900 = lean_alloc_ctor(1, 2, 0);
} else {
 x_900 = x_899;
}
lean_ctor_set(x_900, 0, x_897);
lean_ctor_set(x_900, 1, x_898);
return x_900;
}
}
else
{
lean_object* x_901; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
x_901 = lean_ctor_get(x_728, 1);
lean_inc(x_901);
lean_dec_ref(x_728);
x_11 = x_901;
goto _start;
}
}
}
else
{
uint8_t x_903; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_903 = !lean_is_exclusive(x_89);
if (x_903 == 0)
{
return x_89;
}
else
{
lean_object* x_904; lean_object* x_905; lean_object* x_906; 
x_904 = lean_ctor_get(x_89, 0);
x_905 = lean_ctor_get(x_89, 1);
lean_inc(x_905);
lean_inc(x_904);
lean_dec(x_89);
x_906 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_906, 0, x_904);
lean_ctor_set(x_906, 1, x_905);
return x_906;
}
}
}
else
{
uint8_t x_907; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_907 = !lean_is_exclusive(x_85);
if (x_907 == 0)
{
return x_85;
}
else
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; 
x_908 = lean_ctor_get(x_85, 0);
x_909 = lean_ctor_get(x_85, 1);
lean_inc(x_909);
lean_inc(x_908);
lean_dec(x_85);
x_910 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_910, 0, x_908);
lean_ctor_set(x_910, 1, x_909);
return x_910;
}
}
}
else
{
lean_object* x_911; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
x_911 = lean_ctor_get(x_82, 1);
lean_inc(x_911);
lean_dec_ref(x_82);
x_11 = x_911;
goto _start;
}
}
else
{
lean_object* x_913; lean_object* x_914; lean_object* x_915; uint8_t x_916; 
x_913 = lean_ctor_get(x_78, 1);
lean_inc(x_913);
lean_dec(x_78);
x_914 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_914, 0, x_76);
lean_ctor_set(x_914, 1, x_913);
x_915 = lean_st_ref_set(x_55, x_914, x_79);
x_916 = lean_unbox(x_75);
lean_dec(x_75);
if (x_916 == 0)
{
lean_object* x_917; lean_object* x_918; 
x_917 = lean_ctor_get(x_915, 1);
lean_inc(x_917);
lean_dec_ref(x_915);
x_918 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_917);
if (lean_obj_tag(x_918) == 0)
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; 
x_919 = lean_ctor_get(x_918, 0);
lean_inc(x_919);
x_920 = lean_ctor_get(x_918, 1);
lean_inc(x_920);
lean_dec_ref(x_918);
x_921 = lean_ctor_get(x_919, 0);
lean_inc(x_921);
lean_dec(x_919);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_922 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_921, x_48, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_920);
if (lean_obj_tag(x_922) == 0)
{
lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; uint8_t x_934; 
x_923 = lean_ctor_get(x_922, 0);
lean_inc(x_923);
x_924 = lean_ctor_get(x_922, 1);
lean_inc(x_924);
lean_dec_ref(x_922);
x_925 = lean_ctor_get(x_923, 0);
lean_inc(x_925);
x_926 = lean_ctor_get(x_923, 1);
lean_inc(x_926);
lean_dec(x_923);
x_927 = lean_st_ref_take(x_55, x_924);
x_928 = lean_ctor_get(x_927, 0);
lean_inc(x_928);
x_929 = lean_ctor_get(x_927, 1);
lean_inc(x_929);
lean_dec_ref(x_927);
x_930 = lean_ctor_get(x_928, 1);
lean_inc(x_930);
if (lean_is_exclusive(x_928)) {
 lean_ctor_release(x_928, 0);
 lean_ctor_release(x_928, 1);
 x_931 = x_928;
} else {
 lean_dec_ref(x_928);
 x_931 = lean_box(0);
}
if (lean_is_scalar(x_931)) {
 x_932 = lean_alloc_ctor(0, 2, 0);
} else {
 x_932 = x_931;
}
lean_ctor_set(x_932, 0, x_926);
lean_ctor_set(x_932, 1, x_930);
x_933 = lean_st_ref_set(x_55, x_932, x_929);
x_934 = lean_unbox(x_925);
lean_dec(x_925);
if (x_934 == 0)
{
lean_object* x_935; lean_object* x_936; 
x_935 = lean_ctor_get(x_933, 1);
lean_inc(x_935);
lean_dec_ref(x_933);
x_936 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_935);
if (lean_obj_tag(x_936) == 0)
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; 
x_937 = lean_ctor_get(x_936, 0);
lean_inc(x_937);
x_938 = lean_ctor_get(x_936, 1);
lean_inc(x_938);
lean_dec_ref(x_936);
x_939 = lean_ctor_get(x_937, 0);
lean_inc(x_939);
lean_dec(x_937);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_940 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_939, x_49, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_938);
if (lean_obj_tag(x_940) == 0)
{
lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; uint8_t x_952; 
x_941 = lean_ctor_get(x_940, 0);
lean_inc(x_941);
x_942 = lean_ctor_get(x_940, 1);
lean_inc(x_942);
lean_dec_ref(x_940);
x_943 = lean_ctor_get(x_941, 0);
lean_inc(x_943);
x_944 = lean_ctor_get(x_941, 1);
lean_inc(x_944);
lean_dec(x_941);
x_945 = lean_st_ref_take(x_55, x_942);
x_946 = lean_ctor_get(x_945, 0);
lean_inc(x_946);
x_947 = lean_ctor_get(x_945, 1);
lean_inc(x_947);
lean_dec_ref(x_945);
x_948 = lean_ctor_get(x_946, 1);
lean_inc(x_948);
if (lean_is_exclusive(x_946)) {
 lean_ctor_release(x_946, 0);
 lean_ctor_release(x_946, 1);
 x_949 = x_946;
} else {
 lean_dec_ref(x_946);
 x_949 = lean_box(0);
}
if (lean_is_scalar(x_949)) {
 x_950 = lean_alloc_ctor(0, 2, 0);
} else {
 x_950 = x_949;
}
lean_ctor_set(x_950, 0, x_944);
lean_ctor_set(x_950, 1, x_948);
x_951 = lean_st_ref_set(x_55, x_950, x_947);
x_952 = lean_unbox(x_943);
lean_dec(x_943);
if (x_952 == 0)
{
lean_object* x_953; lean_object* x_954; 
x_953 = lean_ctor_get(x_951, 1);
lean_inc(x_953);
lean_dec_ref(x_951);
x_954 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_953);
if (lean_obj_tag(x_954) == 0)
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; 
x_955 = lean_ctor_get(x_954, 0);
lean_inc(x_955);
x_956 = lean_ctor_get(x_954, 1);
lean_inc(x_956);
lean_dec_ref(x_954);
x_957 = lean_ctor_get(x_955, 0);
lean_inc(x_957);
lean_dec(x_955);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_958 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_957, x_50, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_956);
if (lean_obj_tag(x_958) == 0)
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; uint8_t x_970; 
x_959 = lean_ctor_get(x_958, 0);
lean_inc(x_959);
x_960 = lean_ctor_get(x_958, 1);
lean_inc(x_960);
lean_dec_ref(x_958);
x_961 = lean_ctor_get(x_959, 0);
lean_inc(x_961);
x_962 = lean_ctor_get(x_959, 1);
lean_inc(x_962);
lean_dec(x_959);
x_963 = lean_st_ref_take(x_55, x_960);
x_964 = lean_ctor_get(x_963, 0);
lean_inc(x_964);
x_965 = lean_ctor_get(x_963, 1);
lean_inc(x_965);
lean_dec_ref(x_963);
x_966 = lean_ctor_get(x_964, 1);
lean_inc(x_966);
if (lean_is_exclusive(x_964)) {
 lean_ctor_release(x_964, 0);
 lean_ctor_release(x_964, 1);
 x_967 = x_964;
} else {
 lean_dec_ref(x_964);
 x_967 = lean_box(0);
}
if (lean_is_scalar(x_967)) {
 x_968 = lean_alloc_ctor(0, 2, 0);
} else {
 x_968 = x_967;
}
lean_ctor_set(x_968, 0, x_962);
lean_ctor_set(x_968, 1, x_966);
x_969 = lean_st_ref_set(x_55, x_968, x_965);
x_970 = lean_unbox(x_961);
lean_dec(x_961);
if (x_970 == 0)
{
lean_object* x_971; lean_object* x_972; 
x_971 = lean_ctor_get(x_969, 1);
lean_inc(x_971);
lean_dec_ref(x_969);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_972 = l_Lean_Meta_Grind_splitNext(x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_971);
if (lean_obj_tag(x_972) == 0)
{
lean_object* x_973; uint8_t x_974; 
x_973 = lean_ctor_get(x_972, 0);
lean_inc(x_973);
x_974 = lean_unbox(x_973);
lean_dec(x_973);
if (x_974 == 0)
{
lean_object* x_975; lean_object* x_976; 
x_975 = lean_ctor_get(x_972, 1);
lean_inc(x_975);
lean_dec_ref(x_972);
x_976 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_975);
if (lean_obj_tag(x_976) == 0)
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; 
x_977 = lean_ctor_get(x_976, 0);
lean_inc(x_977);
x_978 = lean_ctor_get(x_976, 1);
lean_inc(x_978);
lean_dec_ref(x_976);
x_979 = lean_ctor_get(x_977, 0);
lean_inc(x_979);
lean_dec(x_977);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_980 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_979, x_51, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_978);
if (lean_obj_tag(x_980) == 0)
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; uint8_t x_992; 
x_981 = lean_ctor_get(x_980, 0);
lean_inc(x_981);
x_982 = lean_ctor_get(x_980, 1);
lean_inc(x_982);
lean_dec_ref(x_980);
x_983 = lean_ctor_get(x_981, 0);
lean_inc(x_983);
x_984 = lean_ctor_get(x_981, 1);
lean_inc(x_984);
lean_dec(x_981);
x_985 = lean_st_ref_take(x_55, x_982);
x_986 = lean_ctor_get(x_985, 0);
lean_inc(x_986);
x_987 = lean_ctor_get(x_985, 1);
lean_inc(x_987);
lean_dec_ref(x_985);
x_988 = lean_ctor_get(x_986, 1);
lean_inc(x_988);
if (lean_is_exclusive(x_986)) {
 lean_ctor_release(x_986, 0);
 lean_ctor_release(x_986, 1);
 x_989 = x_986;
} else {
 lean_dec_ref(x_986);
 x_989 = lean_box(0);
}
if (lean_is_scalar(x_989)) {
 x_990 = lean_alloc_ctor(0, 2, 0);
} else {
 x_990 = x_989;
}
lean_ctor_set(x_990, 0, x_984);
lean_ctor_set(x_990, 1, x_988);
x_991 = lean_st_ref_set(x_55, x_990, x_987);
x_992 = lean_unbox(x_983);
lean_dec(x_983);
if (x_992 == 0)
{
lean_object* x_993; lean_object* x_994; 
x_993 = lean_ctor_get(x_991, 1);
lean_inc(x_993);
lean_dec_ref(x_991);
x_994 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_993);
if (lean_obj_tag(x_994) == 0)
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; 
x_995 = lean_ctor_get(x_994, 0);
lean_inc(x_995);
x_996 = lean_ctor_get(x_994, 1);
lean_inc(x_996);
lean_dec_ref(x_994);
x_997 = lean_ctor_get(x_995, 0);
lean_inc(x_997);
lean_dec(x_995);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_998 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_997, x_52, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_996);
if (lean_obj_tag(x_998) == 0)
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; uint8_t x_1010; 
x_999 = lean_ctor_get(x_998, 0);
lean_inc(x_999);
x_1000 = lean_ctor_get(x_998, 1);
lean_inc(x_1000);
lean_dec_ref(x_998);
x_1001 = lean_ctor_get(x_999, 0);
lean_inc(x_1001);
x_1002 = lean_ctor_get(x_999, 1);
lean_inc(x_1002);
lean_dec(x_999);
x_1003 = lean_st_ref_take(x_55, x_1000);
x_1004 = lean_ctor_get(x_1003, 0);
lean_inc(x_1004);
x_1005 = lean_ctor_get(x_1003, 1);
lean_inc(x_1005);
lean_dec_ref(x_1003);
x_1006 = lean_ctor_get(x_1004, 1);
lean_inc(x_1006);
if (lean_is_exclusive(x_1004)) {
 lean_ctor_release(x_1004, 0);
 lean_ctor_release(x_1004, 1);
 x_1007 = x_1004;
} else {
 lean_dec_ref(x_1004);
 x_1007 = lean_box(0);
}
if (lean_is_scalar(x_1007)) {
 x_1008 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1008 = x_1007;
}
lean_ctor_set(x_1008, 0, x_1002);
lean_ctor_set(x_1008, 1, x_1006);
x_1009 = lean_st_ref_set(x_55, x_1008, x_1005);
x_1010 = lean_unbox(x_1001);
lean_dec(x_1001);
if (x_1010 == 0)
{
lean_object* x_1011; lean_object* x_1012; 
x_1011 = lean_ctor_get(x_1009, 1);
lean_inc(x_1011);
lean_dec_ref(x_1009);
x_1012 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_1011);
if (lean_obj_tag(x_1012) == 0)
{
lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; 
x_1013 = lean_ctor_get(x_1012, 0);
lean_inc(x_1013);
x_1014 = lean_ctor_get(x_1012, 1);
lean_inc(x_1014);
lean_dec_ref(x_1012);
x_1015 = lean_ctor_get(x_1013, 0);
lean_inc(x_1015);
lean_dec(x_1013);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_1016 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_1015, x_53, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_1014);
if (lean_obj_tag(x_1016) == 0)
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; uint8_t x_1028; 
x_1017 = lean_ctor_get(x_1016, 0);
lean_inc(x_1017);
x_1018 = lean_ctor_get(x_1016, 1);
lean_inc(x_1018);
lean_dec_ref(x_1016);
x_1019 = lean_ctor_get(x_1017, 0);
lean_inc(x_1019);
x_1020 = lean_ctor_get(x_1017, 1);
lean_inc(x_1020);
lean_dec(x_1017);
x_1021 = lean_st_ref_take(x_55, x_1018);
x_1022 = lean_ctor_get(x_1021, 0);
lean_inc(x_1022);
x_1023 = lean_ctor_get(x_1021, 1);
lean_inc(x_1023);
lean_dec_ref(x_1021);
x_1024 = lean_ctor_get(x_1022, 1);
lean_inc(x_1024);
if (lean_is_exclusive(x_1022)) {
 lean_ctor_release(x_1022, 0);
 lean_ctor_release(x_1022, 1);
 x_1025 = x_1022;
} else {
 lean_dec_ref(x_1022);
 x_1025 = lean_box(0);
}
if (lean_is_scalar(x_1025)) {
 x_1026 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1026 = x_1025;
}
lean_ctor_set(x_1026, 0, x_1020);
lean_ctor_set(x_1026, 1, x_1024);
x_1027 = lean_st_ref_set(x_55, x_1026, x_1023);
x_1028 = lean_unbox(x_1019);
lean_dec(x_1019);
if (x_1028 == 0)
{
lean_object* x_1029; lean_object* x_1030; 
x_1029 = lean_ctor_get(x_1027, 1);
lean_inc(x_1029);
lean_dec_ref(x_1027);
x_1030 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_1029);
if (lean_obj_tag(x_1030) == 0)
{
lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; 
x_1031 = lean_ctor_get(x_1030, 0);
lean_inc(x_1031);
x_1032 = lean_ctor_get(x_1030, 1);
lean_inc(x_1032);
lean_dec_ref(x_1030);
x_1033 = lean_ctor_get(x_1031, 0);
lean_inc(x_1033);
lean_dec(x_1031);
lean_inc(x_55);
x_1034 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_1033, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_1032);
if (lean_obj_tag(x_1034) == 0)
{
lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; uint8_t x_1047; 
x_1035 = lean_ctor_get(x_1034, 0);
lean_inc(x_1035);
x_1036 = lean_ctor_get(x_1034, 1);
lean_inc(x_1036);
lean_dec_ref(x_1034);
x_1037 = lean_ctor_get(x_1035, 0);
lean_inc(x_1037);
x_1038 = lean_ctor_get(x_1035, 1);
lean_inc(x_1038);
lean_dec(x_1035);
x_1039 = lean_st_ref_take(x_55, x_1036);
x_1040 = lean_ctor_get(x_1039, 0);
lean_inc(x_1040);
x_1041 = lean_ctor_get(x_1039, 1);
lean_inc(x_1041);
lean_dec_ref(x_1039);
x_1042 = lean_ctor_get(x_1040, 1);
lean_inc(x_1042);
if (lean_is_exclusive(x_1040)) {
 lean_ctor_release(x_1040, 0);
 lean_ctor_release(x_1040, 1);
 x_1043 = x_1040;
} else {
 lean_dec_ref(x_1040);
 x_1043 = lean_box(0);
}
if (lean_is_scalar(x_1043)) {
 x_1044 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1044 = x_1043;
}
lean_ctor_set(x_1044, 0, x_1038);
lean_ctor_set(x_1044, 1, x_1042);
x_1045 = lean_st_ref_set(x_55, x_1044, x_1041);
x_1046 = lean_ctor_get(x_1045, 1);
lean_inc(x_1046);
lean_dec_ref(x_1045);
x_1047 = lean_unbox(x_1037);
lean_dec(x_1037);
x_12 = x_55;
x_13 = x_1047;
x_14 = x_1046;
goto block_32;
}
else
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
lean_dec(x_55);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1048 = lean_ctor_get(x_1034, 0);
lean_inc(x_1048);
x_1049 = lean_ctor_get(x_1034, 1);
lean_inc(x_1049);
if (lean_is_exclusive(x_1034)) {
 lean_ctor_release(x_1034, 0);
 lean_ctor_release(x_1034, 1);
 x_1050 = x_1034;
} else {
 lean_dec_ref(x_1034);
 x_1050 = lean_box(0);
}
if (lean_is_scalar(x_1050)) {
 x_1051 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1051 = x_1050;
}
lean_ctor_set(x_1051, 0, x_1048);
lean_ctor_set(x_1051, 1, x_1049);
return x_1051;
}
}
else
{
lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1052 = lean_ctor_get(x_1030, 0);
lean_inc(x_1052);
x_1053 = lean_ctor_get(x_1030, 1);
lean_inc(x_1053);
if (lean_is_exclusive(x_1030)) {
 lean_ctor_release(x_1030, 0);
 lean_ctor_release(x_1030, 1);
 x_1054 = x_1030;
} else {
 lean_dec_ref(x_1030);
 x_1054 = lean_box(0);
}
if (lean_is_scalar(x_1054)) {
 x_1055 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1055 = x_1054;
}
lean_ctor_set(x_1055, 0, x_1052);
lean_ctor_set(x_1055, 1, x_1053);
return x_1055;
}
}
else
{
lean_object* x_1056; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
x_1056 = lean_ctor_get(x_1027, 1);
lean_inc(x_1056);
lean_dec_ref(x_1027);
x_11 = x_1056;
goto _start;
}
}
else
{
lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1058 = lean_ctor_get(x_1016, 0);
lean_inc(x_1058);
x_1059 = lean_ctor_get(x_1016, 1);
lean_inc(x_1059);
if (lean_is_exclusive(x_1016)) {
 lean_ctor_release(x_1016, 0);
 lean_ctor_release(x_1016, 1);
 x_1060 = x_1016;
} else {
 lean_dec_ref(x_1016);
 x_1060 = lean_box(0);
}
if (lean_is_scalar(x_1060)) {
 x_1061 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1061 = x_1060;
}
lean_ctor_set(x_1061, 0, x_1058);
lean_ctor_set(x_1061, 1, x_1059);
return x_1061;
}
}
else
{
lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1062 = lean_ctor_get(x_1012, 0);
lean_inc(x_1062);
x_1063 = lean_ctor_get(x_1012, 1);
lean_inc(x_1063);
if (lean_is_exclusive(x_1012)) {
 lean_ctor_release(x_1012, 0);
 lean_ctor_release(x_1012, 1);
 x_1064 = x_1012;
} else {
 lean_dec_ref(x_1012);
 x_1064 = lean_box(0);
}
if (lean_is_scalar(x_1064)) {
 x_1065 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1065 = x_1064;
}
lean_ctor_set(x_1065, 0, x_1062);
lean_ctor_set(x_1065, 1, x_1063);
return x_1065;
}
}
else
{
lean_object* x_1066; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
x_1066 = lean_ctor_get(x_1009, 1);
lean_inc(x_1066);
lean_dec_ref(x_1009);
x_11 = x_1066;
goto _start;
}
}
else
{
lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1068 = lean_ctor_get(x_998, 0);
lean_inc(x_1068);
x_1069 = lean_ctor_get(x_998, 1);
lean_inc(x_1069);
if (lean_is_exclusive(x_998)) {
 lean_ctor_release(x_998, 0);
 lean_ctor_release(x_998, 1);
 x_1070 = x_998;
} else {
 lean_dec_ref(x_998);
 x_1070 = lean_box(0);
}
if (lean_is_scalar(x_1070)) {
 x_1071 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1071 = x_1070;
}
lean_ctor_set(x_1071, 0, x_1068);
lean_ctor_set(x_1071, 1, x_1069);
return x_1071;
}
}
else
{
lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1072 = lean_ctor_get(x_994, 0);
lean_inc(x_1072);
x_1073 = lean_ctor_get(x_994, 1);
lean_inc(x_1073);
if (lean_is_exclusive(x_994)) {
 lean_ctor_release(x_994, 0);
 lean_ctor_release(x_994, 1);
 x_1074 = x_994;
} else {
 lean_dec_ref(x_994);
 x_1074 = lean_box(0);
}
if (lean_is_scalar(x_1074)) {
 x_1075 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1075 = x_1074;
}
lean_ctor_set(x_1075, 0, x_1072);
lean_ctor_set(x_1075, 1, x_1073);
return x_1075;
}
}
else
{
lean_object* x_1076; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
x_1076 = lean_ctor_get(x_991, 1);
lean_inc(x_1076);
lean_dec_ref(x_991);
x_11 = x_1076;
goto _start;
}
}
else
{
lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1078 = lean_ctor_get(x_980, 0);
lean_inc(x_1078);
x_1079 = lean_ctor_get(x_980, 1);
lean_inc(x_1079);
if (lean_is_exclusive(x_980)) {
 lean_ctor_release(x_980, 0);
 lean_ctor_release(x_980, 1);
 x_1080 = x_980;
} else {
 lean_dec_ref(x_980);
 x_1080 = lean_box(0);
}
if (lean_is_scalar(x_1080)) {
 x_1081 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1081 = x_1080;
}
lean_ctor_set(x_1081, 0, x_1078);
lean_ctor_set(x_1081, 1, x_1079);
return x_1081;
}
}
else
{
lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1082 = lean_ctor_get(x_976, 0);
lean_inc(x_1082);
x_1083 = lean_ctor_get(x_976, 1);
lean_inc(x_1083);
if (lean_is_exclusive(x_976)) {
 lean_ctor_release(x_976, 0);
 lean_ctor_release(x_976, 1);
 x_1084 = x_976;
} else {
 lean_dec_ref(x_976);
 x_1084 = lean_box(0);
}
if (lean_is_scalar(x_1084)) {
 x_1085 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1085 = x_1084;
}
lean_ctor_set(x_1085, 0, x_1082);
lean_ctor_set(x_1085, 1, x_1083);
return x_1085;
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_33 = x_55;
x_34 = x_972;
goto block_42;
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_33 = x_55;
x_34 = x_972;
goto block_42;
}
}
else
{
lean_object* x_1086; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_1086 = lean_ctor_get(x_969, 1);
lean_inc(x_1086);
lean_dec_ref(x_969);
x_11 = x_1086;
goto _start;
}
}
else
{
lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1088 = lean_ctor_get(x_958, 0);
lean_inc(x_1088);
x_1089 = lean_ctor_get(x_958, 1);
lean_inc(x_1089);
if (lean_is_exclusive(x_958)) {
 lean_ctor_release(x_958, 0);
 lean_ctor_release(x_958, 1);
 x_1090 = x_958;
} else {
 lean_dec_ref(x_958);
 x_1090 = lean_box(0);
}
if (lean_is_scalar(x_1090)) {
 x_1091 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1091 = x_1090;
}
lean_ctor_set(x_1091, 0, x_1088);
lean_ctor_set(x_1091, 1, x_1089);
return x_1091;
}
}
else
{
lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_1092 = lean_ctor_get(x_954, 0);
lean_inc(x_1092);
x_1093 = lean_ctor_get(x_954, 1);
lean_inc(x_1093);
if (lean_is_exclusive(x_954)) {
 lean_ctor_release(x_954, 0);
 lean_ctor_release(x_954, 1);
 x_1094 = x_954;
} else {
 lean_dec_ref(x_954);
 x_1094 = lean_box(0);
}
if (lean_is_scalar(x_1094)) {
 x_1095 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1095 = x_1094;
}
lean_ctor_set(x_1095, 0, x_1092);
lean_ctor_set(x_1095, 1, x_1093);
return x_1095;
}
}
else
{
lean_object* x_1096; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
x_1096 = lean_ctor_get(x_951, 1);
lean_inc(x_1096);
lean_dec_ref(x_951);
x_11 = x_1096;
goto _start;
}
}
else
{
lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_1098 = lean_ctor_get(x_940, 0);
lean_inc(x_1098);
x_1099 = lean_ctor_get(x_940, 1);
lean_inc(x_1099);
if (lean_is_exclusive(x_940)) {
 lean_ctor_release(x_940, 0);
 lean_ctor_release(x_940, 1);
 x_1100 = x_940;
} else {
 lean_dec_ref(x_940);
 x_1100 = lean_box(0);
}
if (lean_is_scalar(x_1100)) {
 x_1101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1101 = x_1100;
}
lean_ctor_set(x_1101, 0, x_1098);
lean_ctor_set(x_1101, 1, x_1099);
return x_1101;
}
}
else
{
lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_1102 = lean_ctor_get(x_936, 0);
lean_inc(x_1102);
x_1103 = lean_ctor_get(x_936, 1);
lean_inc(x_1103);
if (lean_is_exclusive(x_936)) {
 lean_ctor_release(x_936, 0);
 lean_ctor_release(x_936, 1);
 x_1104 = x_936;
} else {
 lean_dec_ref(x_936);
 x_1104 = lean_box(0);
}
if (lean_is_scalar(x_1104)) {
 x_1105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1105 = x_1104;
}
lean_ctor_set(x_1105, 0, x_1102);
lean_ctor_set(x_1105, 1, x_1103);
return x_1105;
}
}
else
{
lean_object* x_1106; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
x_1106 = lean_ctor_get(x_933, 1);
lean_inc(x_1106);
lean_dec_ref(x_933);
x_11 = x_1106;
goto _start;
}
}
else
{
lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_1108 = lean_ctor_get(x_922, 0);
lean_inc(x_1108);
x_1109 = lean_ctor_get(x_922, 1);
lean_inc(x_1109);
if (lean_is_exclusive(x_922)) {
 lean_ctor_release(x_922, 0);
 lean_ctor_release(x_922, 1);
 x_1110 = x_922;
} else {
 lean_dec_ref(x_922);
 x_1110 = lean_box(0);
}
if (lean_is_scalar(x_1110)) {
 x_1111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1111 = x_1110;
}
lean_ctor_set(x_1111, 0, x_1108);
lean_ctor_set(x_1111, 1, x_1109);
return x_1111;
}
}
else
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_1112 = lean_ctor_get(x_918, 0);
lean_inc(x_1112);
x_1113 = lean_ctor_get(x_918, 1);
lean_inc(x_1113);
if (lean_is_exclusive(x_918)) {
 lean_ctor_release(x_918, 0);
 lean_ctor_release(x_918, 1);
 x_1114 = x_918;
} else {
 lean_dec_ref(x_918);
 x_1114 = lean_box(0);
}
if (lean_is_scalar(x_1114)) {
 x_1115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1115 = x_1114;
}
lean_ctor_set(x_1115, 0, x_1112);
lean_ctor_set(x_1115, 1, x_1113);
return x_1115;
}
}
else
{
lean_object* x_1116; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
x_1116 = lean_ctor_get(x_915, 1);
lean_inc(x_1116);
lean_dec_ref(x_915);
x_11 = x_1116;
goto _start;
}
}
}
else
{
uint8_t x_1118; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_1118 = !lean_is_exclusive(x_72);
if (x_1118 == 0)
{
return x_72;
}
else
{
lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; 
x_1119 = lean_ctor_get(x_72, 0);
x_1120 = lean_ctor_get(x_72, 1);
lean_inc(x_1120);
lean_inc(x_1119);
lean_dec(x_72);
x_1121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1121, 0, x_1119);
lean_ctor_set(x_1121, 1, x_1120);
return x_1121;
}
}
}
else
{
uint8_t x_1122; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_1122 = !lean_is_exclusive(x_68);
if (x_1122 == 0)
{
return x_68;
}
else
{
lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; 
x_1123 = lean_ctor_get(x_68, 0);
x_1124 = lean_ctor_get(x_68, 1);
lean_inc(x_1124);
lean_inc(x_1123);
lean_dec(x_68);
x_1125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1125, 0, x_1123);
lean_ctor_set(x_1125, 1, x_1124);
return x_1125;
}
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
x_33 = x_55;
x_34 = x_64;
goto block_42;
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
x_33 = x_55;
x_34 = x_64;
goto block_42;
}
}
}
else
{
uint8_t x_1145; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1145 = !lean_is_exclusive(x_43);
if (x_1145 == 0)
{
return x_43;
}
else
{
lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; 
x_1146 = lean_ctor_get(x_43, 0);
x_1147 = lean_ctor_get(x_43, 1);
lean_inc(x_1147);
lean_inc(x_1146);
lean_dec(x_43);
x_1148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1148, 0, x_1146);
lean_ctor_set(x_1148, 1, x_1147);
return x_1148;
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
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
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
x_51 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__4___boxed), 9, 0);
x_52 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__5___boxed), 9, 0);
x_53 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__6___boxed), 9, 0);
x_54 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__7___boxed), 9, 0);
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
x_55 = x_3;
x_56 = x_4;
x_57 = x_5;
x_58 = x_6;
x_59 = x_7;
x_60 = x_8;
x_61 = x_9;
x_62 = x_10;
x_63 = x_45;
goto block_1126;
}
else
{
lean_object* x_1127; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1127 = l_Lean_Meta_Grind_nextGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_45);
if (lean_obj_tag(x_1127) == 0)
{
lean_object* x_1128; 
x_1128 = lean_ctor_get(x_1127, 0);
lean_inc(x_1128);
if (lean_obj_tag(x_1128) == 0)
{
uint8_t x_1129; 
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_1129 = !lean_is_exclusive(x_1127);
if (x_1129 == 0)
{
lean_object* x_1130; 
x_1130 = lean_ctor_get(x_1127, 0);
lean_dec(x_1130);
lean_ctor_set(x_1127, 0, x_1);
return x_1127;
}
else
{
lean_object* x_1131; lean_object* x_1132; 
x_1131 = lean_ctor_get(x_1127, 1);
lean_inc(x_1131);
lean_dec(x_1127);
x_1132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1132, 0, x_1);
lean_ctor_set(x_1132, 1, x_1131);
return x_1132;
}
}
else
{
lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; 
x_1133 = lean_ctor_get(x_1127, 1);
lean_inc(x_1133);
lean_dec_ref(x_1127);
x_1134 = lean_ctor_get(x_1128, 0);
lean_inc(x_1134);
lean_dec_ref(x_1128);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1135 = l_Lean_Meta_Grind_intros(x_1134, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1133);
if (lean_obj_tag(x_1135) == 0)
{
lean_object* x_1136; 
x_1136 = lean_ctor_get(x_1135, 1);
lean_inc(x_1136);
lean_dec_ref(x_1135);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_55 = x_3;
x_56 = x_4;
x_57 = x_5;
x_58 = x_6;
x_59 = x_7;
x_60 = x_8;
x_61 = x_9;
x_62 = x_10;
x_63 = x_1136;
goto block_1126;
}
else
{
uint8_t x_1137; 
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_1137 = !lean_is_exclusive(x_1135);
if (x_1137 == 0)
{
return x_1135;
}
else
{
lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; 
x_1138 = lean_ctor_get(x_1135, 0);
x_1139 = lean_ctor_get(x_1135, 1);
lean_inc(x_1139);
lean_inc(x_1138);
lean_dec(x_1135);
x_1140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1140, 0, x_1138);
lean_ctor_set(x_1140, 1, x_1139);
return x_1140;
}
}
}
}
else
{
uint8_t x_1141; 
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_1141 = !lean_is_exclusive(x_1127);
if (x_1141 == 0)
{
return x_1127;
}
else
{
lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; 
x_1142 = lean_ctor_get(x_1127, 0);
x_1143 = lean_ctor_get(x_1127, 1);
lean_inc(x_1143);
lean_inc(x_1142);
lean_dec(x_1127);
x_1144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1144, 0, x_1142);
lean_ctor_set(x_1144, 1, x_1143);
return x_1144;
}
}
}
block_1126:
{
lean_object* x_64; 
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_64 = l_Lean_Meta_Grind_assertAll(x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec_ref(x_64);
x_68 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_72 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_71, x_47, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec_ref(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_st_ref_take(x_55, x_74);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec_ref(x_77);
x_80 = !lean_is_exclusive(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_81 = lean_ctor_get(x_78, 0);
lean_dec(x_81);
lean_ctor_set(x_78, 0, x_76);
x_82 = lean_st_ref_set(x_55, x_78, x_79);
x_83 = lean_unbox(x_75);
lean_dec(x_75);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec_ref(x_82);
x_85 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec_ref(x_85);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
lean_dec(x_86);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_89 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_88, x_48, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_87);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec_ref(x_89);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_st_ref_take(x_55, x_91);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec_ref(x_94);
x_97 = !lean_is_exclusive(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = lean_ctor_get(x_95, 0);
lean_dec(x_98);
lean_ctor_set(x_95, 0, x_93);
x_99 = lean_st_ref_set(x_55, x_95, x_96);
x_100 = lean_unbox(x_92);
lean_dec(x_92);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec_ref(x_99);
x_102 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec_ref(x_102);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_106 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_105, x_49, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_104);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec_ref(x_106);
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
lean_dec(x_107);
x_111 = lean_st_ref_take(x_55, x_108);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec_ref(x_111);
x_114 = !lean_is_exclusive(x_112);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = lean_ctor_get(x_112, 0);
lean_dec(x_115);
lean_ctor_set(x_112, 0, x_110);
x_116 = lean_st_ref_set(x_55, x_112, x_113);
x_117 = lean_unbox(x_109);
lean_dec(x_109);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec_ref(x_116);
x_119 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_118);
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
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_123 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_122, x_50, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_121);
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
x_128 = lean_st_ref_take(x_55, x_125);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec_ref(x_128);
x_131 = !lean_is_exclusive(x_129);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = lean_ctor_get(x_129, 0);
lean_dec(x_132);
lean_ctor_set(x_129, 0, x_127);
x_133 = lean_st_ref_set(x_55, x_129, x_130);
x_134 = lean_unbox(x_126);
lean_dec(x_126);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec_ref(x_133);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_136 = l_Lean_Meta_Grind_splitNext(x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_unbox(x_137);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec_ref(x_136);
x_140 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec_ref(x_140);
x_143 = lean_ctor_get(x_141, 0);
lean_inc(x_143);
lean_dec(x_141);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_144 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_143, x_51, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_142);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec_ref(x_144);
x_147 = lean_ctor_get(x_145, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
lean_dec(x_145);
x_149 = lean_st_ref_take(x_55, x_146);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec_ref(x_149);
x_152 = !lean_is_exclusive(x_150);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_153 = lean_ctor_get(x_150, 0);
lean_dec(x_153);
lean_ctor_set(x_150, 0, x_148);
x_154 = lean_st_ref_set(x_55, x_150, x_151);
x_155 = lean_unbox(x_147);
lean_dec(x_147);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec_ref(x_154);
x_157 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec_ref(x_157);
x_160 = lean_ctor_get(x_158, 0);
lean_inc(x_160);
lean_dec(x_158);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_161 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_160, x_52, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_159);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec_ref(x_161);
x_164 = lean_ctor_get(x_162, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_dec(x_162);
x_166 = lean_st_ref_take(x_55, x_163);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec_ref(x_166);
x_169 = !lean_is_exclusive(x_167);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_170 = lean_ctor_get(x_167, 0);
lean_dec(x_170);
lean_ctor_set(x_167, 0, x_165);
x_171 = lean_st_ref_set(x_55, x_167, x_168);
x_172 = lean_unbox(x_164);
lean_dec(x_164);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec_ref(x_171);
x_174 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_173);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec_ref(x_174);
x_177 = lean_ctor_get(x_175, 0);
lean_inc(x_177);
lean_dec(x_175);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_178 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_177, x_53, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_176);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec_ref(x_178);
x_181 = lean_ctor_get(x_179, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
lean_dec(x_179);
x_183 = lean_st_ref_take(x_55, x_180);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec_ref(x_183);
x_186 = !lean_is_exclusive(x_184);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_187 = lean_ctor_get(x_184, 0);
lean_dec(x_187);
lean_ctor_set(x_184, 0, x_182);
x_188 = lean_st_ref_set(x_55, x_184, x_185);
x_189 = lean_unbox(x_181);
lean_dec(x_181);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec_ref(x_188);
x_191 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_190);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec_ref(x_191);
x_194 = lean_ctor_get(x_192, 0);
lean_inc(x_194);
lean_dec(x_192);
lean_inc(x_55);
x_195 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_194, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_193);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec_ref(x_195);
x_198 = lean_ctor_get(x_196, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_196, 1);
lean_inc(x_199);
lean_dec(x_196);
x_200 = lean_st_ref_take(x_55, x_197);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec_ref(x_200);
x_203 = !lean_is_exclusive(x_201);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_204 = lean_ctor_get(x_201, 0);
lean_dec(x_204);
lean_ctor_set(x_201, 0, x_199);
x_205 = lean_st_ref_set(x_55, x_201, x_202);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
lean_dec_ref(x_205);
x_207 = lean_unbox(x_198);
lean_dec(x_198);
x_12 = x_55;
x_13 = x_207;
x_14 = x_206;
goto block_32;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_208 = lean_ctor_get(x_201, 1);
lean_inc(x_208);
lean_dec(x_201);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_199);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_st_ref_set(x_55, x_209, x_202);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec_ref(x_210);
x_212 = lean_unbox(x_198);
lean_dec(x_198);
x_12 = x_55;
x_13 = x_212;
x_14 = x_211;
goto block_32;
}
}
else
{
uint8_t x_213; 
lean_dec(x_55);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_213 = !lean_is_exclusive(x_195);
if (x_213 == 0)
{
return x_195;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_195, 0);
x_215 = lean_ctor_get(x_195, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_195);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
else
{
uint8_t x_217; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_217 = !lean_is_exclusive(x_191);
if (x_217 == 0)
{
return x_191;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_191, 0);
x_219 = lean_ctor_get(x_191, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_191);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
else
{
lean_object* x_221; lean_object* x_222; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
x_221 = lean_ctor_get(x_188, 1);
lean_inc(x_221);
lean_dec_ref(x_188);
x_222 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_221);
return x_222;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_223 = lean_ctor_get(x_184, 1);
lean_inc(x_223);
lean_dec(x_184);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_182);
lean_ctor_set(x_224, 1, x_223);
x_225 = lean_st_ref_set(x_55, x_224, x_185);
x_226 = lean_unbox(x_181);
lean_dec(x_181);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec_ref(x_225);
x_228 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_227);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec_ref(x_228);
x_231 = lean_ctor_get(x_229, 0);
lean_inc(x_231);
lean_dec(x_229);
lean_inc(x_55);
x_232 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_231, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_230);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec_ref(x_232);
x_235 = lean_ctor_get(x_233, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_233, 1);
lean_inc(x_236);
lean_dec(x_233);
x_237 = lean_st_ref_take(x_55, x_234);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec_ref(x_237);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_241 = x_238;
} else {
 lean_dec_ref(x_238);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_241;
}
lean_ctor_set(x_242, 0, x_236);
lean_ctor_set(x_242, 1, x_240);
x_243 = lean_st_ref_set(x_55, x_242, x_239);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec_ref(x_243);
x_245 = lean_unbox(x_235);
lean_dec(x_235);
x_12 = x_55;
x_13 = x_245;
x_14 = x_244;
goto block_32;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_55);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_246 = lean_ctor_get(x_232, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_232, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_248 = x_232;
} else {
 lean_dec_ref(x_232);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_250 = lean_ctor_get(x_228, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_228, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_252 = x_228;
} else {
 lean_dec_ref(x_228);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_250);
lean_ctor_set(x_253, 1, x_251);
return x_253;
}
}
else
{
lean_object* x_254; lean_object* x_255; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
x_254 = lean_ctor_get(x_225, 1);
lean_inc(x_254);
lean_dec_ref(x_225);
x_255 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_254);
return x_255;
}
}
}
else
{
uint8_t x_256; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_256 = !lean_is_exclusive(x_178);
if (x_256 == 0)
{
return x_178;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_178, 0);
x_258 = lean_ctor_get(x_178, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_178);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
}
}
else
{
uint8_t x_260; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_260 = !lean_is_exclusive(x_174);
if (x_260 == 0)
{
return x_174;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_174, 0);
x_262 = lean_ctor_get(x_174, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_174);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
return x_263;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
x_264 = lean_ctor_get(x_171, 1);
lean_inc(x_264);
lean_dec_ref(x_171);
x_265 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_264);
return x_265;
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_266 = lean_ctor_get(x_167, 1);
lean_inc(x_266);
lean_dec(x_167);
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_165);
lean_ctor_set(x_267, 1, x_266);
x_268 = lean_st_ref_set(x_55, x_267, x_168);
x_269 = lean_unbox(x_164);
lean_dec(x_164);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec_ref(x_268);
x_271 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_270);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec_ref(x_271);
x_274 = lean_ctor_get(x_272, 0);
lean_inc(x_274);
lean_dec(x_272);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_275 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_274, x_53, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_273);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec_ref(x_275);
x_278 = lean_ctor_get(x_276, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_276, 1);
lean_inc(x_279);
lean_dec(x_276);
x_280 = lean_st_ref_take(x_55, x_277);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec_ref(x_280);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_284 = x_281;
} else {
 lean_dec_ref(x_281);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_279);
lean_ctor_set(x_285, 1, x_283);
x_286 = lean_st_ref_set(x_55, x_285, x_282);
x_287 = lean_unbox(x_278);
lean_dec(x_278);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; 
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec_ref(x_286);
x_289 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_288);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
lean_dec_ref(x_289);
x_292 = lean_ctor_get(x_290, 0);
lean_inc(x_292);
lean_dec(x_290);
lean_inc(x_55);
x_293 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_292, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_291);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec_ref(x_293);
x_296 = lean_ctor_get(x_294, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_294, 1);
lean_inc(x_297);
lean_dec(x_294);
x_298 = lean_st_ref_take(x_55, x_295);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
lean_dec_ref(x_298);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_302 = x_299;
} else {
 lean_dec_ref(x_299);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_297);
lean_ctor_set(x_303, 1, x_301);
x_304 = lean_st_ref_set(x_55, x_303, x_300);
x_305 = lean_ctor_get(x_304, 1);
lean_inc(x_305);
lean_dec_ref(x_304);
x_306 = lean_unbox(x_296);
lean_dec(x_296);
x_12 = x_55;
x_13 = x_306;
x_14 = x_305;
goto block_32;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_55);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_307 = lean_ctor_get(x_293, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_293, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_309 = x_293;
} else {
 lean_dec_ref(x_293);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(1, 2, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_307);
lean_ctor_set(x_310, 1, x_308);
return x_310;
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_311 = lean_ctor_get(x_289, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_289, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_313 = x_289;
} else {
 lean_dec_ref(x_289);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(1, 2, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_312);
return x_314;
}
}
else
{
lean_object* x_315; lean_object* x_316; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
x_315 = lean_ctor_get(x_286, 1);
lean_inc(x_315);
lean_dec_ref(x_286);
x_316 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_315);
return x_316;
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_317 = lean_ctor_get(x_275, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_275, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_319 = x_275;
} else {
 lean_dec_ref(x_275);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(1, 2, 0);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_317);
lean_ctor_set(x_320, 1, x_318);
return x_320;
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_321 = lean_ctor_get(x_271, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_271, 1);
lean_inc(x_322);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_323 = x_271;
} else {
 lean_dec_ref(x_271);
 x_323 = lean_box(0);
}
if (lean_is_scalar(x_323)) {
 x_324 = lean_alloc_ctor(1, 2, 0);
} else {
 x_324 = x_323;
}
lean_ctor_set(x_324, 0, x_321);
lean_ctor_set(x_324, 1, x_322);
return x_324;
}
}
else
{
lean_object* x_325; lean_object* x_326; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
x_325 = lean_ctor_get(x_268, 1);
lean_inc(x_325);
lean_dec_ref(x_268);
x_326 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_325);
return x_326;
}
}
}
else
{
uint8_t x_327; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_327 = !lean_is_exclusive(x_161);
if (x_327 == 0)
{
return x_161;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_161, 0);
x_329 = lean_ctor_get(x_161, 1);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_161);
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_328);
lean_ctor_set(x_330, 1, x_329);
return x_330;
}
}
}
else
{
uint8_t x_331; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_331 = !lean_is_exclusive(x_157);
if (x_331 == 0)
{
return x_157;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_157, 0);
x_333 = lean_ctor_get(x_157, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_157);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
return x_334;
}
}
}
else
{
lean_object* x_335; lean_object* x_336; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
x_335 = lean_ctor_get(x_154, 1);
lean_inc(x_335);
lean_dec_ref(x_154);
x_336 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_335);
return x_336;
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_337 = lean_ctor_get(x_150, 1);
lean_inc(x_337);
lean_dec(x_150);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_148);
lean_ctor_set(x_338, 1, x_337);
x_339 = lean_st_ref_set(x_55, x_338, x_151);
x_340 = lean_unbox(x_147);
lean_dec(x_147);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; 
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
lean_dec_ref(x_339);
x_342 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_341);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec_ref(x_342);
x_345 = lean_ctor_get(x_343, 0);
lean_inc(x_345);
lean_dec(x_343);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_346 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_345, x_52, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_344);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
lean_dec_ref(x_346);
x_349 = lean_ctor_get(x_347, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_347, 1);
lean_inc(x_350);
lean_dec(x_347);
x_351 = lean_st_ref_take(x_55, x_348);
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec_ref(x_351);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_355 = x_352;
} else {
 lean_dec_ref(x_352);
 x_355 = lean_box(0);
}
if (lean_is_scalar(x_355)) {
 x_356 = lean_alloc_ctor(0, 2, 0);
} else {
 x_356 = x_355;
}
lean_ctor_set(x_356, 0, x_350);
lean_ctor_set(x_356, 1, x_354);
x_357 = lean_st_ref_set(x_55, x_356, x_353);
x_358 = lean_unbox(x_349);
lean_dec(x_349);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; 
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
lean_dec_ref(x_357);
x_360 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_359);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec_ref(x_360);
x_363 = lean_ctor_get(x_361, 0);
lean_inc(x_363);
lean_dec(x_361);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_364 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_363, x_53, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_362);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; uint8_t x_376; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
lean_dec_ref(x_364);
x_367 = lean_ctor_get(x_365, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_365, 1);
lean_inc(x_368);
lean_dec(x_365);
x_369 = lean_st_ref_take(x_55, x_366);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec_ref(x_369);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_373 = x_370;
} else {
 lean_dec_ref(x_370);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_374 = lean_alloc_ctor(0, 2, 0);
} else {
 x_374 = x_373;
}
lean_ctor_set(x_374, 0, x_368);
lean_ctor_set(x_374, 1, x_372);
x_375 = lean_st_ref_set(x_55, x_374, x_371);
x_376 = lean_unbox(x_367);
lean_dec(x_367);
if (x_376 == 0)
{
lean_object* x_377; lean_object* x_378; 
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
lean_dec_ref(x_375);
x_378 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_377);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec_ref(x_378);
x_381 = lean_ctor_get(x_379, 0);
lean_inc(x_381);
lean_dec(x_379);
lean_inc(x_55);
x_382 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_381, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_380);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; uint8_t x_395; 
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_382, 1);
lean_inc(x_384);
lean_dec_ref(x_382);
x_385 = lean_ctor_get(x_383, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_383, 1);
lean_inc(x_386);
lean_dec(x_383);
x_387 = lean_st_ref_take(x_55, x_384);
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
lean_dec_ref(x_387);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 x_391 = x_388;
} else {
 lean_dec_ref(x_388);
 x_391 = lean_box(0);
}
if (lean_is_scalar(x_391)) {
 x_392 = lean_alloc_ctor(0, 2, 0);
} else {
 x_392 = x_391;
}
lean_ctor_set(x_392, 0, x_386);
lean_ctor_set(x_392, 1, x_390);
x_393 = lean_st_ref_set(x_55, x_392, x_389);
x_394 = lean_ctor_get(x_393, 1);
lean_inc(x_394);
lean_dec_ref(x_393);
x_395 = lean_unbox(x_385);
lean_dec(x_385);
x_12 = x_55;
x_13 = x_395;
x_14 = x_394;
goto block_32;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_55);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_396 = lean_ctor_get(x_382, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_382, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 x_398 = x_382;
} else {
 lean_dec_ref(x_382);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 2, 0);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_396);
lean_ctor_set(x_399, 1, x_397);
return x_399;
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_400 = lean_ctor_get(x_378, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_378, 1);
lean_inc(x_401);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_402 = x_378;
} else {
 lean_dec_ref(x_378);
 x_402 = lean_box(0);
}
if (lean_is_scalar(x_402)) {
 x_403 = lean_alloc_ctor(1, 2, 0);
} else {
 x_403 = x_402;
}
lean_ctor_set(x_403, 0, x_400);
lean_ctor_set(x_403, 1, x_401);
return x_403;
}
}
else
{
lean_object* x_404; lean_object* x_405; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
x_404 = lean_ctor_get(x_375, 1);
lean_inc(x_404);
lean_dec_ref(x_375);
x_405 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_404);
return x_405;
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_406 = lean_ctor_get(x_364, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_364, 1);
lean_inc(x_407);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_408 = x_364;
} else {
 lean_dec_ref(x_364);
 x_408 = lean_box(0);
}
if (lean_is_scalar(x_408)) {
 x_409 = lean_alloc_ctor(1, 2, 0);
} else {
 x_409 = x_408;
}
lean_ctor_set(x_409, 0, x_406);
lean_ctor_set(x_409, 1, x_407);
return x_409;
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_410 = lean_ctor_get(x_360, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_360, 1);
lean_inc(x_411);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_412 = x_360;
} else {
 lean_dec_ref(x_360);
 x_412 = lean_box(0);
}
if (lean_is_scalar(x_412)) {
 x_413 = lean_alloc_ctor(1, 2, 0);
} else {
 x_413 = x_412;
}
lean_ctor_set(x_413, 0, x_410);
lean_ctor_set(x_413, 1, x_411);
return x_413;
}
}
else
{
lean_object* x_414; lean_object* x_415; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
x_414 = lean_ctor_get(x_357, 1);
lean_inc(x_414);
lean_dec_ref(x_357);
x_415 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_414);
return x_415;
}
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_416 = lean_ctor_get(x_346, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_346, 1);
lean_inc(x_417);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_418 = x_346;
} else {
 lean_dec_ref(x_346);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_418)) {
 x_419 = lean_alloc_ctor(1, 2, 0);
} else {
 x_419 = x_418;
}
lean_ctor_set(x_419, 0, x_416);
lean_ctor_set(x_419, 1, x_417);
return x_419;
}
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_420 = lean_ctor_get(x_342, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_342, 1);
lean_inc(x_421);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_422 = x_342;
} else {
 lean_dec_ref(x_342);
 x_422 = lean_box(0);
}
if (lean_is_scalar(x_422)) {
 x_423 = lean_alloc_ctor(1, 2, 0);
} else {
 x_423 = x_422;
}
lean_ctor_set(x_423, 0, x_420);
lean_ctor_set(x_423, 1, x_421);
return x_423;
}
}
else
{
lean_object* x_424; lean_object* x_425; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
x_424 = lean_ctor_get(x_339, 1);
lean_inc(x_424);
lean_dec_ref(x_339);
x_425 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_424);
return x_425;
}
}
}
else
{
uint8_t x_426; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_426 = !lean_is_exclusive(x_144);
if (x_426 == 0)
{
return x_144;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_144, 0);
x_428 = lean_ctor_get(x_144, 1);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_144);
x_429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
return x_429;
}
}
}
else
{
uint8_t x_430; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_430 = !lean_is_exclusive(x_140);
if (x_430 == 0)
{
return x_140;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_431 = lean_ctor_get(x_140, 0);
x_432 = lean_ctor_get(x_140, 1);
lean_inc(x_432);
lean_inc(x_431);
lean_dec(x_140);
x_433 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set(x_433, 1, x_432);
return x_433;
}
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_33 = x_55;
x_34 = x_136;
goto block_42;
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_33 = x_55;
x_34 = x_136;
goto block_42;
}
}
else
{
lean_object* x_434; lean_object* x_435; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_434 = lean_ctor_get(x_133, 1);
lean_inc(x_434);
lean_dec_ref(x_133);
x_435 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_434);
return x_435;
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; 
x_436 = lean_ctor_get(x_129, 1);
lean_inc(x_436);
lean_dec(x_129);
x_437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_437, 0, x_127);
lean_ctor_set(x_437, 1, x_436);
x_438 = lean_st_ref_set(x_55, x_437, x_130);
x_439 = lean_unbox(x_126);
lean_dec(x_126);
if (x_439 == 0)
{
lean_object* x_440; lean_object* x_441; 
x_440 = lean_ctor_get(x_438, 1);
lean_inc(x_440);
lean_dec_ref(x_438);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_441 = l_Lean_Meta_Grind_splitNext(x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_440);
if (lean_obj_tag(x_441) == 0)
{
lean_object* x_442; uint8_t x_443; 
x_442 = lean_ctor_get(x_441, 0);
lean_inc(x_442);
x_443 = lean_unbox(x_442);
lean_dec(x_442);
if (x_443 == 0)
{
lean_object* x_444; lean_object* x_445; 
x_444 = lean_ctor_get(x_441, 1);
lean_inc(x_444);
lean_dec_ref(x_441);
x_445 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_444);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_445, 1);
lean_inc(x_447);
lean_dec_ref(x_445);
x_448 = lean_ctor_get(x_446, 0);
lean_inc(x_448);
lean_dec(x_446);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_449 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_448, x_51, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_447);
if (lean_obj_tag(x_449) == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; 
x_450 = lean_ctor_get(x_449, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_449, 1);
lean_inc(x_451);
lean_dec_ref(x_449);
x_452 = lean_ctor_get(x_450, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_450, 1);
lean_inc(x_453);
lean_dec(x_450);
x_454 = lean_st_ref_take(x_55, x_451);
x_455 = lean_ctor_get(x_454, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_454, 1);
lean_inc(x_456);
lean_dec_ref(x_454);
x_457 = lean_ctor_get(x_455, 1);
lean_inc(x_457);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 lean_ctor_release(x_455, 1);
 x_458 = x_455;
} else {
 lean_dec_ref(x_455);
 x_458 = lean_box(0);
}
if (lean_is_scalar(x_458)) {
 x_459 = lean_alloc_ctor(0, 2, 0);
} else {
 x_459 = x_458;
}
lean_ctor_set(x_459, 0, x_453);
lean_ctor_set(x_459, 1, x_457);
x_460 = lean_st_ref_set(x_55, x_459, x_456);
x_461 = lean_unbox(x_452);
lean_dec(x_452);
if (x_461 == 0)
{
lean_object* x_462; lean_object* x_463; 
x_462 = lean_ctor_get(x_460, 1);
lean_inc(x_462);
lean_dec_ref(x_460);
x_463 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_462);
if (lean_obj_tag(x_463) == 0)
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_463, 1);
lean_inc(x_465);
lean_dec_ref(x_463);
x_466 = lean_ctor_get(x_464, 0);
lean_inc(x_466);
lean_dec(x_464);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_467 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_466, x_52, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_465);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; 
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
lean_dec_ref(x_467);
x_470 = lean_ctor_get(x_468, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_468, 1);
lean_inc(x_471);
lean_dec(x_468);
x_472 = lean_st_ref_take(x_55, x_469);
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_472, 1);
lean_inc(x_474);
lean_dec_ref(x_472);
x_475 = lean_ctor_get(x_473, 1);
lean_inc(x_475);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 lean_ctor_release(x_473, 1);
 x_476 = x_473;
} else {
 lean_dec_ref(x_473);
 x_476 = lean_box(0);
}
if (lean_is_scalar(x_476)) {
 x_477 = lean_alloc_ctor(0, 2, 0);
} else {
 x_477 = x_476;
}
lean_ctor_set(x_477, 0, x_471);
lean_ctor_set(x_477, 1, x_475);
x_478 = lean_st_ref_set(x_55, x_477, x_474);
x_479 = lean_unbox(x_470);
lean_dec(x_470);
if (x_479 == 0)
{
lean_object* x_480; lean_object* x_481; 
x_480 = lean_ctor_get(x_478, 1);
lean_inc(x_480);
lean_dec_ref(x_478);
x_481 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_480);
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_481, 1);
lean_inc(x_483);
lean_dec_ref(x_481);
x_484 = lean_ctor_get(x_482, 0);
lean_inc(x_484);
lean_dec(x_482);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_485 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_484, x_53, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_483);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; uint8_t x_497; 
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_485, 1);
lean_inc(x_487);
lean_dec_ref(x_485);
x_488 = lean_ctor_get(x_486, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_486, 1);
lean_inc(x_489);
lean_dec(x_486);
x_490 = lean_st_ref_take(x_55, x_487);
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_490, 1);
lean_inc(x_492);
lean_dec_ref(x_490);
x_493 = lean_ctor_get(x_491, 1);
lean_inc(x_493);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 x_494 = x_491;
} else {
 lean_dec_ref(x_491);
 x_494 = lean_box(0);
}
if (lean_is_scalar(x_494)) {
 x_495 = lean_alloc_ctor(0, 2, 0);
} else {
 x_495 = x_494;
}
lean_ctor_set(x_495, 0, x_489);
lean_ctor_set(x_495, 1, x_493);
x_496 = lean_st_ref_set(x_55, x_495, x_492);
x_497 = lean_unbox(x_488);
lean_dec(x_488);
if (x_497 == 0)
{
lean_object* x_498; lean_object* x_499; 
x_498 = lean_ctor_get(x_496, 1);
lean_inc(x_498);
lean_dec_ref(x_496);
x_499 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_498);
if (lean_obj_tag(x_499) == 0)
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_500 = lean_ctor_get(x_499, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_499, 1);
lean_inc(x_501);
lean_dec_ref(x_499);
x_502 = lean_ctor_get(x_500, 0);
lean_inc(x_502);
lean_dec(x_500);
lean_inc(x_55);
x_503 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_502, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_501);
if (lean_obj_tag(x_503) == 0)
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; uint8_t x_516; 
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_503, 1);
lean_inc(x_505);
lean_dec_ref(x_503);
x_506 = lean_ctor_get(x_504, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_504, 1);
lean_inc(x_507);
lean_dec(x_504);
x_508 = lean_st_ref_take(x_55, x_505);
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
lean_dec_ref(x_508);
x_511 = lean_ctor_get(x_509, 1);
lean_inc(x_511);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 x_512 = x_509;
} else {
 lean_dec_ref(x_509);
 x_512 = lean_box(0);
}
if (lean_is_scalar(x_512)) {
 x_513 = lean_alloc_ctor(0, 2, 0);
} else {
 x_513 = x_512;
}
lean_ctor_set(x_513, 0, x_507);
lean_ctor_set(x_513, 1, x_511);
x_514 = lean_st_ref_set(x_55, x_513, x_510);
x_515 = lean_ctor_get(x_514, 1);
lean_inc(x_515);
lean_dec_ref(x_514);
x_516 = lean_unbox(x_506);
lean_dec(x_506);
x_12 = x_55;
x_13 = x_516;
x_14 = x_515;
goto block_32;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
lean_dec(x_55);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_517 = lean_ctor_get(x_503, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_503, 1);
lean_inc(x_518);
if (lean_is_exclusive(x_503)) {
 lean_ctor_release(x_503, 0);
 lean_ctor_release(x_503, 1);
 x_519 = x_503;
} else {
 lean_dec_ref(x_503);
 x_519 = lean_box(0);
}
if (lean_is_scalar(x_519)) {
 x_520 = lean_alloc_ctor(1, 2, 0);
} else {
 x_520 = x_519;
}
lean_ctor_set(x_520, 0, x_517);
lean_ctor_set(x_520, 1, x_518);
return x_520;
}
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_521 = lean_ctor_get(x_499, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_499, 1);
lean_inc(x_522);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 lean_ctor_release(x_499, 1);
 x_523 = x_499;
} else {
 lean_dec_ref(x_499);
 x_523 = lean_box(0);
}
if (lean_is_scalar(x_523)) {
 x_524 = lean_alloc_ctor(1, 2, 0);
} else {
 x_524 = x_523;
}
lean_ctor_set(x_524, 0, x_521);
lean_ctor_set(x_524, 1, x_522);
return x_524;
}
}
else
{
lean_object* x_525; lean_object* x_526; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
x_525 = lean_ctor_get(x_496, 1);
lean_inc(x_525);
lean_dec_ref(x_496);
x_526 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_525);
return x_526;
}
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_527 = lean_ctor_get(x_485, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_485, 1);
lean_inc(x_528);
if (lean_is_exclusive(x_485)) {
 lean_ctor_release(x_485, 0);
 lean_ctor_release(x_485, 1);
 x_529 = x_485;
} else {
 lean_dec_ref(x_485);
 x_529 = lean_box(0);
}
if (lean_is_scalar(x_529)) {
 x_530 = lean_alloc_ctor(1, 2, 0);
} else {
 x_530 = x_529;
}
lean_ctor_set(x_530, 0, x_527);
lean_ctor_set(x_530, 1, x_528);
return x_530;
}
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_531 = lean_ctor_get(x_481, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_481, 1);
lean_inc(x_532);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 x_533 = x_481;
} else {
 lean_dec_ref(x_481);
 x_533 = lean_box(0);
}
if (lean_is_scalar(x_533)) {
 x_534 = lean_alloc_ctor(1, 2, 0);
} else {
 x_534 = x_533;
}
lean_ctor_set(x_534, 0, x_531);
lean_ctor_set(x_534, 1, x_532);
return x_534;
}
}
else
{
lean_object* x_535; lean_object* x_536; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
x_535 = lean_ctor_get(x_478, 1);
lean_inc(x_535);
lean_dec_ref(x_478);
x_536 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_535);
return x_536;
}
}
else
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_537 = lean_ctor_get(x_467, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_467, 1);
lean_inc(x_538);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 x_539 = x_467;
} else {
 lean_dec_ref(x_467);
 x_539 = lean_box(0);
}
if (lean_is_scalar(x_539)) {
 x_540 = lean_alloc_ctor(1, 2, 0);
} else {
 x_540 = x_539;
}
lean_ctor_set(x_540, 0, x_537);
lean_ctor_set(x_540, 1, x_538);
return x_540;
}
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_541 = lean_ctor_get(x_463, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_463, 1);
lean_inc(x_542);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 x_543 = x_463;
} else {
 lean_dec_ref(x_463);
 x_543 = lean_box(0);
}
if (lean_is_scalar(x_543)) {
 x_544 = lean_alloc_ctor(1, 2, 0);
} else {
 x_544 = x_543;
}
lean_ctor_set(x_544, 0, x_541);
lean_ctor_set(x_544, 1, x_542);
return x_544;
}
}
else
{
lean_object* x_545; lean_object* x_546; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
x_545 = lean_ctor_get(x_460, 1);
lean_inc(x_545);
lean_dec_ref(x_460);
x_546 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_545);
return x_546;
}
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_547 = lean_ctor_get(x_449, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_449, 1);
lean_inc(x_548);
if (lean_is_exclusive(x_449)) {
 lean_ctor_release(x_449, 0);
 lean_ctor_release(x_449, 1);
 x_549 = x_449;
} else {
 lean_dec_ref(x_449);
 x_549 = lean_box(0);
}
if (lean_is_scalar(x_549)) {
 x_550 = lean_alloc_ctor(1, 2, 0);
} else {
 x_550 = x_549;
}
lean_ctor_set(x_550, 0, x_547);
lean_ctor_set(x_550, 1, x_548);
return x_550;
}
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_551 = lean_ctor_get(x_445, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_445, 1);
lean_inc(x_552);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 x_553 = x_445;
} else {
 lean_dec_ref(x_445);
 x_553 = lean_box(0);
}
if (lean_is_scalar(x_553)) {
 x_554 = lean_alloc_ctor(1, 2, 0);
} else {
 x_554 = x_553;
}
lean_ctor_set(x_554, 0, x_551);
lean_ctor_set(x_554, 1, x_552);
return x_554;
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_33 = x_55;
x_34 = x_441;
goto block_42;
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_33 = x_55;
x_34 = x_441;
goto block_42;
}
}
else
{
lean_object* x_555; lean_object* x_556; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_555 = lean_ctor_get(x_438, 1);
lean_inc(x_555);
lean_dec_ref(x_438);
x_556 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_555);
return x_556;
}
}
}
else
{
uint8_t x_557; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_557 = !lean_is_exclusive(x_123);
if (x_557 == 0)
{
return x_123;
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_558 = lean_ctor_get(x_123, 0);
x_559 = lean_ctor_get(x_123, 1);
lean_inc(x_559);
lean_inc(x_558);
lean_dec(x_123);
x_560 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_560, 0, x_558);
lean_ctor_set(x_560, 1, x_559);
return x_560;
}
}
}
else
{
uint8_t x_561; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_561 = !lean_is_exclusive(x_119);
if (x_561 == 0)
{
return x_119;
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_562 = lean_ctor_get(x_119, 0);
x_563 = lean_ctor_get(x_119, 1);
lean_inc(x_563);
lean_inc(x_562);
lean_dec(x_119);
x_564 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_564, 0, x_562);
lean_ctor_set(x_564, 1, x_563);
return x_564;
}
}
}
else
{
lean_object* x_565; lean_object* x_566; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
x_565 = lean_ctor_get(x_116, 1);
lean_inc(x_565);
lean_dec_ref(x_116);
x_566 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_565);
return x_566;
}
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; uint8_t x_570; 
x_567 = lean_ctor_get(x_112, 1);
lean_inc(x_567);
lean_dec(x_112);
x_568 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_568, 0, x_110);
lean_ctor_set(x_568, 1, x_567);
x_569 = lean_st_ref_set(x_55, x_568, x_113);
x_570 = lean_unbox(x_109);
lean_dec(x_109);
if (x_570 == 0)
{
lean_object* x_571; lean_object* x_572; 
x_571 = lean_ctor_get(x_569, 1);
lean_inc(x_571);
lean_dec_ref(x_569);
x_572 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_571);
if (lean_obj_tag(x_572) == 0)
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_572, 1);
lean_inc(x_574);
lean_dec_ref(x_572);
x_575 = lean_ctor_get(x_573, 0);
lean_inc(x_575);
lean_dec(x_573);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_576 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_575, x_50, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_574);
if (lean_obj_tag(x_576) == 0)
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; uint8_t x_588; 
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_576, 1);
lean_inc(x_578);
lean_dec_ref(x_576);
x_579 = lean_ctor_get(x_577, 0);
lean_inc(x_579);
x_580 = lean_ctor_get(x_577, 1);
lean_inc(x_580);
lean_dec(x_577);
x_581 = lean_st_ref_take(x_55, x_578);
x_582 = lean_ctor_get(x_581, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_581, 1);
lean_inc(x_583);
lean_dec_ref(x_581);
x_584 = lean_ctor_get(x_582, 1);
lean_inc(x_584);
if (lean_is_exclusive(x_582)) {
 lean_ctor_release(x_582, 0);
 lean_ctor_release(x_582, 1);
 x_585 = x_582;
} else {
 lean_dec_ref(x_582);
 x_585 = lean_box(0);
}
if (lean_is_scalar(x_585)) {
 x_586 = lean_alloc_ctor(0, 2, 0);
} else {
 x_586 = x_585;
}
lean_ctor_set(x_586, 0, x_580);
lean_ctor_set(x_586, 1, x_584);
x_587 = lean_st_ref_set(x_55, x_586, x_583);
x_588 = lean_unbox(x_579);
lean_dec(x_579);
if (x_588 == 0)
{
lean_object* x_589; lean_object* x_590; 
x_589 = lean_ctor_get(x_587, 1);
lean_inc(x_589);
lean_dec_ref(x_587);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_590 = l_Lean_Meta_Grind_splitNext(x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_589);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; uint8_t x_592; 
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
x_592 = lean_unbox(x_591);
lean_dec(x_591);
if (x_592 == 0)
{
lean_object* x_593; lean_object* x_594; 
x_593 = lean_ctor_get(x_590, 1);
lean_inc(x_593);
lean_dec_ref(x_590);
x_594 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_593);
if (lean_obj_tag(x_594) == 0)
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_595 = lean_ctor_get(x_594, 0);
lean_inc(x_595);
x_596 = lean_ctor_get(x_594, 1);
lean_inc(x_596);
lean_dec_ref(x_594);
x_597 = lean_ctor_get(x_595, 0);
lean_inc(x_597);
lean_dec(x_595);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_598 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_597, x_51, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_596);
if (lean_obj_tag(x_598) == 0)
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; uint8_t x_610; 
x_599 = lean_ctor_get(x_598, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_598, 1);
lean_inc(x_600);
lean_dec_ref(x_598);
x_601 = lean_ctor_get(x_599, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_599, 1);
lean_inc(x_602);
lean_dec(x_599);
x_603 = lean_st_ref_take(x_55, x_600);
x_604 = lean_ctor_get(x_603, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_603, 1);
lean_inc(x_605);
lean_dec_ref(x_603);
x_606 = lean_ctor_get(x_604, 1);
lean_inc(x_606);
if (lean_is_exclusive(x_604)) {
 lean_ctor_release(x_604, 0);
 lean_ctor_release(x_604, 1);
 x_607 = x_604;
} else {
 lean_dec_ref(x_604);
 x_607 = lean_box(0);
}
if (lean_is_scalar(x_607)) {
 x_608 = lean_alloc_ctor(0, 2, 0);
} else {
 x_608 = x_607;
}
lean_ctor_set(x_608, 0, x_602);
lean_ctor_set(x_608, 1, x_606);
x_609 = lean_st_ref_set(x_55, x_608, x_605);
x_610 = lean_unbox(x_601);
lean_dec(x_601);
if (x_610 == 0)
{
lean_object* x_611; lean_object* x_612; 
x_611 = lean_ctor_get(x_609, 1);
lean_inc(x_611);
lean_dec_ref(x_609);
x_612 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_611);
if (lean_obj_tag(x_612) == 0)
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_612, 1);
lean_inc(x_614);
lean_dec_ref(x_612);
x_615 = lean_ctor_get(x_613, 0);
lean_inc(x_615);
lean_dec(x_613);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_616 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_615, x_52, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_614);
if (lean_obj_tag(x_616) == 0)
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; uint8_t x_628; 
x_617 = lean_ctor_get(x_616, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_616, 1);
lean_inc(x_618);
lean_dec_ref(x_616);
x_619 = lean_ctor_get(x_617, 0);
lean_inc(x_619);
x_620 = lean_ctor_get(x_617, 1);
lean_inc(x_620);
lean_dec(x_617);
x_621 = lean_st_ref_take(x_55, x_618);
x_622 = lean_ctor_get(x_621, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_621, 1);
lean_inc(x_623);
lean_dec_ref(x_621);
x_624 = lean_ctor_get(x_622, 1);
lean_inc(x_624);
if (lean_is_exclusive(x_622)) {
 lean_ctor_release(x_622, 0);
 lean_ctor_release(x_622, 1);
 x_625 = x_622;
} else {
 lean_dec_ref(x_622);
 x_625 = lean_box(0);
}
if (lean_is_scalar(x_625)) {
 x_626 = lean_alloc_ctor(0, 2, 0);
} else {
 x_626 = x_625;
}
lean_ctor_set(x_626, 0, x_620);
lean_ctor_set(x_626, 1, x_624);
x_627 = lean_st_ref_set(x_55, x_626, x_623);
x_628 = lean_unbox(x_619);
lean_dec(x_619);
if (x_628 == 0)
{
lean_object* x_629; lean_object* x_630; 
x_629 = lean_ctor_get(x_627, 1);
lean_inc(x_629);
lean_dec_ref(x_627);
x_630 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_629);
if (lean_obj_tag(x_630) == 0)
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
x_631 = lean_ctor_get(x_630, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_630, 1);
lean_inc(x_632);
lean_dec_ref(x_630);
x_633 = lean_ctor_get(x_631, 0);
lean_inc(x_633);
lean_dec(x_631);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_634 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_633, x_53, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_632);
if (lean_obj_tag(x_634) == 0)
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; uint8_t x_646; 
x_635 = lean_ctor_get(x_634, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_634, 1);
lean_inc(x_636);
lean_dec_ref(x_634);
x_637 = lean_ctor_get(x_635, 0);
lean_inc(x_637);
x_638 = lean_ctor_get(x_635, 1);
lean_inc(x_638);
lean_dec(x_635);
x_639 = lean_st_ref_take(x_55, x_636);
x_640 = lean_ctor_get(x_639, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_639, 1);
lean_inc(x_641);
lean_dec_ref(x_639);
x_642 = lean_ctor_get(x_640, 1);
lean_inc(x_642);
if (lean_is_exclusive(x_640)) {
 lean_ctor_release(x_640, 0);
 lean_ctor_release(x_640, 1);
 x_643 = x_640;
} else {
 lean_dec_ref(x_640);
 x_643 = lean_box(0);
}
if (lean_is_scalar(x_643)) {
 x_644 = lean_alloc_ctor(0, 2, 0);
} else {
 x_644 = x_643;
}
lean_ctor_set(x_644, 0, x_638);
lean_ctor_set(x_644, 1, x_642);
x_645 = lean_st_ref_set(x_55, x_644, x_641);
x_646 = lean_unbox(x_637);
lean_dec(x_637);
if (x_646 == 0)
{
lean_object* x_647; lean_object* x_648; 
x_647 = lean_ctor_get(x_645, 1);
lean_inc(x_647);
lean_dec_ref(x_645);
x_648 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_647);
if (lean_obj_tag(x_648) == 0)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
x_649 = lean_ctor_get(x_648, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_648, 1);
lean_inc(x_650);
lean_dec_ref(x_648);
x_651 = lean_ctor_get(x_649, 0);
lean_inc(x_651);
lean_dec(x_649);
lean_inc(x_55);
x_652 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_651, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_650);
if (lean_obj_tag(x_652) == 0)
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; uint8_t x_665; 
x_653 = lean_ctor_get(x_652, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_652, 1);
lean_inc(x_654);
lean_dec_ref(x_652);
x_655 = lean_ctor_get(x_653, 0);
lean_inc(x_655);
x_656 = lean_ctor_get(x_653, 1);
lean_inc(x_656);
lean_dec(x_653);
x_657 = lean_st_ref_take(x_55, x_654);
x_658 = lean_ctor_get(x_657, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_657, 1);
lean_inc(x_659);
lean_dec_ref(x_657);
x_660 = lean_ctor_get(x_658, 1);
lean_inc(x_660);
if (lean_is_exclusive(x_658)) {
 lean_ctor_release(x_658, 0);
 lean_ctor_release(x_658, 1);
 x_661 = x_658;
} else {
 lean_dec_ref(x_658);
 x_661 = lean_box(0);
}
if (lean_is_scalar(x_661)) {
 x_662 = lean_alloc_ctor(0, 2, 0);
} else {
 x_662 = x_661;
}
lean_ctor_set(x_662, 0, x_656);
lean_ctor_set(x_662, 1, x_660);
x_663 = lean_st_ref_set(x_55, x_662, x_659);
x_664 = lean_ctor_get(x_663, 1);
lean_inc(x_664);
lean_dec_ref(x_663);
x_665 = lean_unbox(x_655);
lean_dec(x_655);
x_12 = x_55;
x_13 = x_665;
x_14 = x_664;
goto block_32;
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
lean_dec(x_55);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_666 = lean_ctor_get(x_652, 0);
lean_inc(x_666);
x_667 = lean_ctor_get(x_652, 1);
lean_inc(x_667);
if (lean_is_exclusive(x_652)) {
 lean_ctor_release(x_652, 0);
 lean_ctor_release(x_652, 1);
 x_668 = x_652;
} else {
 lean_dec_ref(x_652);
 x_668 = lean_box(0);
}
if (lean_is_scalar(x_668)) {
 x_669 = lean_alloc_ctor(1, 2, 0);
} else {
 x_669 = x_668;
}
lean_ctor_set(x_669, 0, x_666);
lean_ctor_set(x_669, 1, x_667);
return x_669;
}
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_670 = lean_ctor_get(x_648, 0);
lean_inc(x_670);
x_671 = lean_ctor_get(x_648, 1);
lean_inc(x_671);
if (lean_is_exclusive(x_648)) {
 lean_ctor_release(x_648, 0);
 lean_ctor_release(x_648, 1);
 x_672 = x_648;
} else {
 lean_dec_ref(x_648);
 x_672 = lean_box(0);
}
if (lean_is_scalar(x_672)) {
 x_673 = lean_alloc_ctor(1, 2, 0);
} else {
 x_673 = x_672;
}
lean_ctor_set(x_673, 0, x_670);
lean_ctor_set(x_673, 1, x_671);
return x_673;
}
}
else
{
lean_object* x_674; lean_object* x_675; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
x_674 = lean_ctor_get(x_645, 1);
lean_inc(x_674);
lean_dec_ref(x_645);
x_675 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_674);
return x_675;
}
}
else
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_676 = lean_ctor_get(x_634, 0);
lean_inc(x_676);
x_677 = lean_ctor_get(x_634, 1);
lean_inc(x_677);
if (lean_is_exclusive(x_634)) {
 lean_ctor_release(x_634, 0);
 lean_ctor_release(x_634, 1);
 x_678 = x_634;
} else {
 lean_dec_ref(x_634);
 x_678 = lean_box(0);
}
if (lean_is_scalar(x_678)) {
 x_679 = lean_alloc_ctor(1, 2, 0);
} else {
 x_679 = x_678;
}
lean_ctor_set(x_679, 0, x_676);
lean_ctor_set(x_679, 1, x_677);
return x_679;
}
}
else
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_680 = lean_ctor_get(x_630, 0);
lean_inc(x_680);
x_681 = lean_ctor_get(x_630, 1);
lean_inc(x_681);
if (lean_is_exclusive(x_630)) {
 lean_ctor_release(x_630, 0);
 lean_ctor_release(x_630, 1);
 x_682 = x_630;
} else {
 lean_dec_ref(x_630);
 x_682 = lean_box(0);
}
if (lean_is_scalar(x_682)) {
 x_683 = lean_alloc_ctor(1, 2, 0);
} else {
 x_683 = x_682;
}
lean_ctor_set(x_683, 0, x_680);
lean_ctor_set(x_683, 1, x_681);
return x_683;
}
}
else
{
lean_object* x_684; lean_object* x_685; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
x_684 = lean_ctor_get(x_627, 1);
lean_inc(x_684);
lean_dec_ref(x_627);
x_685 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_684);
return x_685;
}
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_686 = lean_ctor_get(x_616, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_616, 1);
lean_inc(x_687);
if (lean_is_exclusive(x_616)) {
 lean_ctor_release(x_616, 0);
 lean_ctor_release(x_616, 1);
 x_688 = x_616;
} else {
 lean_dec_ref(x_616);
 x_688 = lean_box(0);
}
if (lean_is_scalar(x_688)) {
 x_689 = lean_alloc_ctor(1, 2, 0);
} else {
 x_689 = x_688;
}
lean_ctor_set(x_689, 0, x_686);
lean_ctor_set(x_689, 1, x_687);
return x_689;
}
}
else
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_690 = lean_ctor_get(x_612, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_612, 1);
lean_inc(x_691);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 x_692 = x_612;
} else {
 lean_dec_ref(x_612);
 x_692 = lean_box(0);
}
if (lean_is_scalar(x_692)) {
 x_693 = lean_alloc_ctor(1, 2, 0);
} else {
 x_693 = x_692;
}
lean_ctor_set(x_693, 0, x_690);
lean_ctor_set(x_693, 1, x_691);
return x_693;
}
}
else
{
lean_object* x_694; lean_object* x_695; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
x_694 = lean_ctor_get(x_609, 1);
lean_inc(x_694);
lean_dec_ref(x_609);
x_695 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_694);
return x_695;
}
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_696 = lean_ctor_get(x_598, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_598, 1);
lean_inc(x_697);
if (lean_is_exclusive(x_598)) {
 lean_ctor_release(x_598, 0);
 lean_ctor_release(x_598, 1);
 x_698 = x_598;
} else {
 lean_dec_ref(x_598);
 x_698 = lean_box(0);
}
if (lean_is_scalar(x_698)) {
 x_699 = lean_alloc_ctor(1, 2, 0);
} else {
 x_699 = x_698;
}
lean_ctor_set(x_699, 0, x_696);
lean_ctor_set(x_699, 1, x_697);
return x_699;
}
}
else
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_700 = lean_ctor_get(x_594, 0);
lean_inc(x_700);
x_701 = lean_ctor_get(x_594, 1);
lean_inc(x_701);
if (lean_is_exclusive(x_594)) {
 lean_ctor_release(x_594, 0);
 lean_ctor_release(x_594, 1);
 x_702 = x_594;
} else {
 lean_dec_ref(x_594);
 x_702 = lean_box(0);
}
if (lean_is_scalar(x_702)) {
 x_703 = lean_alloc_ctor(1, 2, 0);
} else {
 x_703 = x_702;
}
lean_ctor_set(x_703, 0, x_700);
lean_ctor_set(x_703, 1, x_701);
return x_703;
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_33 = x_55;
x_34 = x_590;
goto block_42;
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_33 = x_55;
x_34 = x_590;
goto block_42;
}
}
else
{
lean_object* x_704; lean_object* x_705; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_704 = lean_ctor_get(x_587, 1);
lean_inc(x_704);
lean_dec_ref(x_587);
x_705 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_704);
return x_705;
}
}
else
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_706 = lean_ctor_get(x_576, 0);
lean_inc(x_706);
x_707 = lean_ctor_get(x_576, 1);
lean_inc(x_707);
if (lean_is_exclusive(x_576)) {
 lean_ctor_release(x_576, 0);
 lean_ctor_release(x_576, 1);
 x_708 = x_576;
} else {
 lean_dec_ref(x_576);
 x_708 = lean_box(0);
}
if (lean_is_scalar(x_708)) {
 x_709 = lean_alloc_ctor(1, 2, 0);
} else {
 x_709 = x_708;
}
lean_ctor_set(x_709, 0, x_706);
lean_ctor_set(x_709, 1, x_707);
return x_709;
}
}
else
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_710 = lean_ctor_get(x_572, 0);
lean_inc(x_710);
x_711 = lean_ctor_get(x_572, 1);
lean_inc(x_711);
if (lean_is_exclusive(x_572)) {
 lean_ctor_release(x_572, 0);
 lean_ctor_release(x_572, 1);
 x_712 = x_572;
} else {
 lean_dec_ref(x_572);
 x_712 = lean_box(0);
}
if (lean_is_scalar(x_712)) {
 x_713 = lean_alloc_ctor(1, 2, 0);
} else {
 x_713 = x_712;
}
lean_ctor_set(x_713, 0, x_710);
lean_ctor_set(x_713, 1, x_711);
return x_713;
}
}
else
{
lean_object* x_714; lean_object* x_715; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
x_714 = lean_ctor_get(x_569, 1);
lean_inc(x_714);
lean_dec_ref(x_569);
x_715 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_714);
return x_715;
}
}
}
else
{
uint8_t x_716; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_716 = !lean_is_exclusive(x_106);
if (x_716 == 0)
{
return x_106;
}
else
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_717 = lean_ctor_get(x_106, 0);
x_718 = lean_ctor_get(x_106, 1);
lean_inc(x_718);
lean_inc(x_717);
lean_dec(x_106);
x_719 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_719, 0, x_717);
lean_ctor_set(x_719, 1, x_718);
return x_719;
}
}
}
else
{
uint8_t x_720; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_720 = !lean_is_exclusive(x_102);
if (x_720 == 0)
{
return x_102;
}
else
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; 
x_721 = lean_ctor_get(x_102, 0);
x_722 = lean_ctor_get(x_102, 1);
lean_inc(x_722);
lean_inc(x_721);
lean_dec(x_102);
x_723 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_723, 0, x_721);
lean_ctor_set(x_723, 1, x_722);
return x_723;
}
}
}
else
{
lean_object* x_724; lean_object* x_725; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
x_724 = lean_ctor_get(x_99, 1);
lean_inc(x_724);
lean_dec_ref(x_99);
x_725 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_724);
return x_725;
}
}
else
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; uint8_t x_729; 
x_726 = lean_ctor_get(x_95, 1);
lean_inc(x_726);
lean_dec(x_95);
x_727 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_727, 0, x_93);
lean_ctor_set(x_727, 1, x_726);
x_728 = lean_st_ref_set(x_55, x_727, x_96);
x_729 = lean_unbox(x_92);
lean_dec(x_92);
if (x_729 == 0)
{
lean_object* x_730; lean_object* x_731; 
x_730 = lean_ctor_get(x_728, 1);
lean_inc(x_730);
lean_dec_ref(x_728);
x_731 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_730);
if (lean_obj_tag(x_731) == 0)
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; 
x_732 = lean_ctor_get(x_731, 0);
lean_inc(x_732);
x_733 = lean_ctor_get(x_731, 1);
lean_inc(x_733);
lean_dec_ref(x_731);
x_734 = lean_ctor_get(x_732, 0);
lean_inc(x_734);
lean_dec(x_732);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_735 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_734, x_49, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_733);
if (lean_obj_tag(x_735) == 0)
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; uint8_t x_747; 
x_736 = lean_ctor_get(x_735, 0);
lean_inc(x_736);
x_737 = lean_ctor_get(x_735, 1);
lean_inc(x_737);
lean_dec_ref(x_735);
x_738 = lean_ctor_get(x_736, 0);
lean_inc(x_738);
x_739 = lean_ctor_get(x_736, 1);
lean_inc(x_739);
lean_dec(x_736);
x_740 = lean_st_ref_take(x_55, x_737);
x_741 = lean_ctor_get(x_740, 0);
lean_inc(x_741);
x_742 = lean_ctor_get(x_740, 1);
lean_inc(x_742);
lean_dec_ref(x_740);
x_743 = lean_ctor_get(x_741, 1);
lean_inc(x_743);
if (lean_is_exclusive(x_741)) {
 lean_ctor_release(x_741, 0);
 lean_ctor_release(x_741, 1);
 x_744 = x_741;
} else {
 lean_dec_ref(x_741);
 x_744 = lean_box(0);
}
if (lean_is_scalar(x_744)) {
 x_745 = lean_alloc_ctor(0, 2, 0);
} else {
 x_745 = x_744;
}
lean_ctor_set(x_745, 0, x_739);
lean_ctor_set(x_745, 1, x_743);
x_746 = lean_st_ref_set(x_55, x_745, x_742);
x_747 = lean_unbox(x_738);
lean_dec(x_738);
if (x_747 == 0)
{
lean_object* x_748; lean_object* x_749; 
x_748 = lean_ctor_get(x_746, 1);
lean_inc(x_748);
lean_dec_ref(x_746);
x_749 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_748);
if (lean_obj_tag(x_749) == 0)
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; 
x_750 = lean_ctor_get(x_749, 0);
lean_inc(x_750);
x_751 = lean_ctor_get(x_749, 1);
lean_inc(x_751);
lean_dec_ref(x_749);
x_752 = lean_ctor_get(x_750, 0);
lean_inc(x_752);
lean_dec(x_750);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_753 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_752, x_50, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_751);
if (lean_obj_tag(x_753) == 0)
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; uint8_t x_765; 
x_754 = lean_ctor_get(x_753, 0);
lean_inc(x_754);
x_755 = lean_ctor_get(x_753, 1);
lean_inc(x_755);
lean_dec_ref(x_753);
x_756 = lean_ctor_get(x_754, 0);
lean_inc(x_756);
x_757 = lean_ctor_get(x_754, 1);
lean_inc(x_757);
lean_dec(x_754);
x_758 = lean_st_ref_take(x_55, x_755);
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_758, 1);
lean_inc(x_760);
lean_dec_ref(x_758);
x_761 = lean_ctor_get(x_759, 1);
lean_inc(x_761);
if (lean_is_exclusive(x_759)) {
 lean_ctor_release(x_759, 0);
 lean_ctor_release(x_759, 1);
 x_762 = x_759;
} else {
 lean_dec_ref(x_759);
 x_762 = lean_box(0);
}
if (lean_is_scalar(x_762)) {
 x_763 = lean_alloc_ctor(0, 2, 0);
} else {
 x_763 = x_762;
}
lean_ctor_set(x_763, 0, x_757);
lean_ctor_set(x_763, 1, x_761);
x_764 = lean_st_ref_set(x_55, x_763, x_760);
x_765 = lean_unbox(x_756);
lean_dec(x_756);
if (x_765 == 0)
{
lean_object* x_766; lean_object* x_767; 
x_766 = lean_ctor_get(x_764, 1);
lean_inc(x_766);
lean_dec_ref(x_764);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_767 = l_Lean_Meta_Grind_splitNext(x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_766);
if (lean_obj_tag(x_767) == 0)
{
lean_object* x_768; uint8_t x_769; 
x_768 = lean_ctor_get(x_767, 0);
lean_inc(x_768);
x_769 = lean_unbox(x_768);
lean_dec(x_768);
if (x_769 == 0)
{
lean_object* x_770; lean_object* x_771; 
x_770 = lean_ctor_get(x_767, 1);
lean_inc(x_770);
lean_dec_ref(x_767);
x_771 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_770);
if (lean_obj_tag(x_771) == 0)
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; 
x_772 = lean_ctor_get(x_771, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_771, 1);
lean_inc(x_773);
lean_dec_ref(x_771);
x_774 = lean_ctor_get(x_772, 0);
lean_inc(x_774);
lean_dec(x_772);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_775 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_774, x_51, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_773);
if (lean_obj_tag(x_775) == 0)
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; uint8_t x_787; 
x_776 = lean_ctor_get(x_775, 0);
lean_inc(x_776);
x_777 = lean_ctor_get(x_775, 1);
lean_inc(x_777);
lean_dec_ref(x_775);
x_778 = lean_ctor_get(x_776, 0);
lean_inc(x_778);
x_779 = lean_ctor_get(x_776, 1);
lean_inc(x_779);
lean_dec(x_776);
x_780 = lean_st_ref_take(x_55, x_777);
x_781 = lean_ctor_get(x_780, 0);
lean_inc(x_781);
x_782 = lean_ctor_get(x_780, 1);
lean_inc(x_782);
lean_dec_ref(x_780);
x_783 = lean_ctor_get(x_781, 1);
lean_inc(x_783);
if (lean_is_exclusive(x_781)) {
 lean_ctor_release(x_781, 0);
 lean_ctor_release(x_781, 1);
 x_784 = x_781;
} else {
 lean_dec_ref(x_781);
 x_784 = lean_box(0);
}
if (lean_is_scalar(x_784)) {
 x_785 = lean_alloc_ctor(0, 2, 0);
} else {
 x_785 = x_784;
}
lean_ctor_set(x_785, 0, x_779);
lean_ctor_set(x_785, 1, x_783);
x_786 = lean_st_ref_set(x_55, x_785, x_782);
x_787 = lean_unbox(x_778);
lean_dec(x_778);
if (x_787 == 0)
{
lean_object* x_788; lean_object* x_789; 
x_788 = lean_ctor_get(x_786, 1);
lean_inc(x_788);
lean_dec_ref(x_786);
x_789 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_788);
if (lean_obj_tag(x_789) == 0)
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; 
x_790 = lean_ctor_get(x_789, 0);
lean_inc(x_790);
x_791 = lean_ctor_get(x_789, 1);
lean_inc(x_791);
lean_dec_ref(x_789);
x_792 = lean_ctor_get(x_790, 0);
lean_inc(x_792);
lean_dec(x_790);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_793 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_792, x_52, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_791);
if (lean_obj_tag(x_793) == 0)
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; uint8_t x_805; 
x_794 = lean_ctor_get(x_793, 0);
lean_inc(x_794);
x_795 = lean_ctor_get(x_793, 1);
lean_inc(x_795);
lean_dec_ref(x_793);
x_796 = lean_ctor_get(x_794, 0);
lean_inc(x_796);
x_797 = lean_ctor_get(x_794, 1);
lean_inc(x_797);
lean_dec(x_794);
x_798 = lean_st_ref_take(x_55, x_795);
x_799 = lean_ctor_get(x_798, 0);
lean_inc(x_799);
x_800 = lean_ctor_get(x_798, 1);
lean_inc(x_800);
lean_dec_ref(x_798);
x_801 = lean_ctor_get(x_799, 1);
lean_inc(x_801);
if (lean_is_exclusive(x_799)) {
 lean_ctor_release(x_799, 0);
 lean_ctor_release(x_799, 1);
 x_802 = x_799;
} else {
 lean_dec_ref(x_799);
 x_802 = lean_box(0);
}
if (lean_is_scalar(x_802)) {
 x_803 = lean_alloc_ctor(0, 2, 0);
} else {
 x_803 = x_802;
}
lean_ctor_set(x_803, 0, x_797);
lean_ctor_set(x_803, 1, x_801);
x_804 = lean_st_ref_set(x_55, x_803, x_800);
x_805 = lean_unbox(x_796);
lean_dec(x_796);
if (x_805 == 0)
{
lean_object* x_806; lean_object* x_807; 
x_806 = lean_ctor_get(x_804, 1);
lean_inc(x_806);
lean_dec_ref(x_804);
x_807 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_806);
if (lean_obj_tag(x_807) == 0)
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_808 = lean_ctor_get(x_807, 0);
lean_inc(x_808);
x_809 = lean_ctor_get(x_807, 1);
lean_inc(x_809);
lean_dec_ref(x_807);
x_810 = lean_ctor_get(x_808, 0);
lean_inc(x_810);
lean_dec(x_808);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_811 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_810, x_53, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_809);
if (lean_obj_tag(x_811) == 0)
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; uint8_t x_823; 
x_812 = lean_ctor_get(x_811, 0);
lean_inc(x_812);
x_813 = lean_ctor_get(x_811, 1);
lean_inc(x_813);
lean_dec_ref(x_811);
x_814 = lean_ctor_get(x_812, 0);
lean_inc(x_814);
x_815 = lean_ctor_get(x_812, 1);
lean_inc(x_815);
lean_dec(x_812);
x_816 = lean_st_ref_take(x_55, x_813);
x_817 = lean_ctor_get(x_816, 0);
lean_inc(x_817);
x_818 = lean_ctor_get(x_816, 1);
lean_inc(x_818);
lean_dec_ref(x_816);
x_819 = lean_ctor_get(x_817, 1);
lean_inc(x_819);
if (lean_is_exclusive(x_817)) {
 lean_ctor_release(x_817, 0);
 lean_ctor_release(x_817, 1);
 x_820 = x_817;
} else {
 lean_dec_ref(x_817);
 x_820 = lean_box(0);
}
if (lean_is_scalar(x_820)) {
 x_821 = lean_alloc_ctor(0, 2, 0);
} else {
 x_821 = x_820;
}
lean_ctor_set(x_821, 0, x_815);
lean_ctor_set(x_821, 1, x_819);
x_822 = lean_st_ref_set(x_55, x_821, x_818);
x_823 = lean_unbox(x_814);
lean_dec(x_814);
if (x_823 == 0)
{
lean_object* x_824; lean_object* x_825; 
x_824 = lean_ctor_get(x_822, 1);
lean_inc(x_824);
lean_dec_ref(x_822);
x_825 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_824);
if (lean_obj_tag(x_825) == 0)
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; 
x_826 = lean_ctor_get(x_825, 0);
lean_inc(x_826);
x_827 = lean_ctor_get(x_825, 1);
lean_inc(x_827);
lean_dec_ref(x_825);
x_828 = lean_ctor_get(x_826, 0);
lean_inc(x_828);
lean_dec(x_826);
lean_inc(x_55);
x_829 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_828, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_827);
if (lean_obj_tag(x_829) == 0)
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; uint8_t x_842; 
x_830 = lean_ctor_get(x_829, 0);
lean_inc(x_830);
x_831 = lean_ctor_get(x_829, 1);
lean_inc(x_831);
lean_dec_ref(x_829);
x_832 = lean_ctor_get(x_830, 0);
lean_inc(x_832);
x_833 = lean_ctor_get(x_830, 1);
lean_inc(x_833);
lean_dec(x_830);
x_834 = lean_st_ref_take(x_55, x_831);
x_835 = lean_ctor_get(x_834, 0);
lean_inc(x_835);
x_836 = lean_ctor_get(x_834, 1);
lean_inc(x_836);
lean_dec_ref(x_834);
x_837 = lean_ctor_get(x_835, 1);
lean_inc(x_837);
if (lean_is_exclusive(x_835)) {
 lean_ctor_release(x_835, 0);
 lean_ctor_release(x_835, 1);
 x_838 = x_835;
} else {
 lean_dec_ref(x_835);
 x_838 = lean_box(0);
}
if (lean_is_scalar(x_838)) {
 x_839 = lean_alloc_ctor(0, 2, 0);
} else {
 x_839 = x_838;
}
lean_ctor_set(x_839, 0, x_833);
lean_ctor_set(x_839, 1, x_837);
x_840 = lean_st_ref_set(x_55, x_839, x_836);
x_841 = lean_ctor_get(x_840, 1);
lean_inc(x_841);
lean_dec_ref(x_840);
x_842 = lean_unbox(x_832);
lean_dec(x_832);
x_12 = x_55;
x_13 = x_842;
x_14 = x_841;
goto block_32;
}
else
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; 
lean_dec(x_55);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_843 = lean_ctor_get(x_829, 0);
lean_inc(x_843);
x_844 = lean_ctor_get(x_829, 1);
lean_inc(x_844);
if (lean_is_exclusive(x_829)) {
 lean_ctor_release(x_829, 0);
 lean_ctor_release(x_829, 1);
 x_845 = x_829;
} else {
 lean_dec_ref(x_829);
 x_845 = lean_box(0);
}
if (lean_is_scalar(x_845)) {
 x_846 = lean_alloc_ctor(1, 2, 0);
} else {
 x_846 = x_845;
}
lean_ctor_set(x_846, 0, x_843);
lean_ctor_set(x_846, 1, x_844);
return x_846;
}
}
else
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_847 = lean_ctor_get(x_825, 0);
lean_inc(x_847);
x_848 = lean_ctor_get(x_825, 1);
lean_inc(x_848);
if (lean_is_exclusive(x_825)) {
 lean_ctor_release(x_825, 0);
 lean_ctor_release(x_825, 1);
 x_849 = x_825;
} else {
 lean_dec_ref(x_825);
 x_849 = lean_box(0);
}
if (lean_is_scalar(x_849)) {
 x_850 = lean_alloc_ctor(1, 2, 0);
} else {
 x_850 = x_849;
}
lean_ctor_set(x_850, 0, x_847);
lean_ctor_set(x_850, 1, x_848);
return x_850;
}
}
else
{
lean_object* x_851; lean_object* x_852; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
x_851 = lean_ctor_get(x_822, 1);
lean_inc(x_851);
lean_dec_ref(x_822);
x_852 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_851);
return x_852;
}
}
else
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_853 = lean_ctor_get(x_811, 0);
lean_inc(x_853);
x_854 = lean_ctor_get(x_811, 1);
lean_inc(x_854);
if (lean_is_exclusive(x_811)) {
 lean_ctor_release(x_811, 0);
 lean_ctor_release(x_811, 1);
 x_855 = x_811;
} else {
 lean_dec_ref(x_811);
 x_855 = lean_box(0);
}
if (lean_is_scalar(x_855)) {
 x_856 = lean_alloc_ctor(1, 2, 0);
} else {
 x_856 = x_855;
}
lean_ctor_set(x_856, 0, x_853);
lean_ctor_set(x_856, 1, x_854);
return x_856;
}
}
else
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_857 = lean_ctor_get(x_807, 0);
lean_inc(x_857);
x_858 = lean_ctor_get(x_807, 1);
lean_inc(x_858);
if (lean_is_exclusive(x_807)) {
 lean_ctor_release(x_807, 0);
 lean_ctor_release(x_807, 1);
 x_859 = x_807;
} else {
 lean_dec_ref(x_807);
 x_859 = lean_box(0);
}
if (lean_is_scalar(x_859)) {
 x_860 = lean_alloc_ctor(1, 2, 0);
} else {
 x_860 = x_859;
}
lean_ctor_set(x_860, 0, x_857);
lean_ctor_set(x_860, 1, x_858);
return x_860;
}
}
else
{
lean_object* x_861; lean_object* x_862; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
x_861 = lean_ctor_get(x_804, 1);
lean_inc(x_861);
lean_dec_ref(x_804);
x_862 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_861);
return x_862;
}
}
else
{
lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_863 = lean_ctor_get(x_793, 0);
lean_inc(x_863);
x_864 = lean_ctor_get(x_793, 1);
lean_inc(x_864);
if (lean_is_exclusive(x_793)) {
 lean_ctor_release(x_793, 0);
 lean_ctor_release(x_793, 1);
 x_865 = x_793;
} else {
 lean_dec_ref(x_793);
 x_865 = lean_box(0);
}
if (lean_is_scalar(x_865)) {
 x_866 = lean_alloc_ctor(1, 2, 0);
} else {
 x_866 = x_865;
}
lean_ctor_set(x_866, 0, x_863);
lean_ctor_set(x_866, 1, x_864);
return x_866;
}
}
else
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_867 = lean_ctor_get(x_789, 0);
lean_inc(x_867);
x_868 = lean_ctor_get(x_789, 1);
lean_inc(x_868);
if (lean_is_exclusive(x_789)) {
 lean_ctor_release(x_789, 0);
 lean_ctor_release(x_789, 1);
 x_869 = x_789;
} else {
 lean_dec_ref(x_789);
 x_869 = lean_box(0);
}
if (lean_is_scalar(x_869)) {
 x_870 = lean_alloc_ctor(1, 2, 0);
} else {
 x_870 = x_869;
}
lean_ctor_set(x_870, 0, x_867);
lean_ctor_set(x_870, 1, x_868);
return x_870;
}
}
else
{
lean_object* x_871; lean_object* x_872; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
x_871 = lean_ctor_get(x_786, 1);
lean_inc(x_871);
lean_dec_ref(x_786);
x_872 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_871);
return x_872;
}
}
else
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_873 = lean_ctor_get(x_775, 0);
lean_inc(x_873);
x_874 = lean_ctor_get(x_775, 1);
lean_inc(x_874);
if (lean_is_exclusive(x_775)) {
 lean_ctor_release(x_775, 0);
 lean_ctor_release(x_775, 1);
 x_875 = x_775;
} else {
 lean_dec_ref(x_775);
 x_875 = lean_box(0);
}
if (lean_is_scalar(x_875)) {
 x_876 = lean_alloc_ctor(1, 2, 0);
} else {
 x_876 = x_875;
}
lean_ctor_set(x_876, 0, x_873);
lean_ctor_set(x_876, 1, x_874);
return x_876;
}
}
else
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_877 = lean_ctor_get(x_771, 0);
lean_inc(x_877);
x_878 = lean_ctor_get(x_771, 1);
lean_inc(x_878);
if (lean_is_exclusive(x_771)) {
 lean_ctor_release(x_771, 0);
 lean_ctor_release(x_771, 1);
 x_879 = x_771;
} else {
 lean_dec_ref(x_771);
 x_879 = lean_box(0);
}
if (lean_is_scalar(x_879)) {
 x_880 = lean_alloc_ctor(1, 2, 0);
} else {
 x_880 = x_879;
}
lean_ctor_set(x_880, 0, x_877);
lean_ctor_set(x_880, 1, x_878);
return x_880;
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_33 = x_55;
x_34 = x_767;
goto block_42;
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_33 = x_55;
x_34 = x_767;
goto block_42;
}
}
else
{
lean_object* x_881; lean_object* x_882; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_881 = lean_ctor_get(x_764, 1);
lean_inc(x_881);
lean_dec_ref(x_764);
x_882 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_881);
return x_882;
}
}
else
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_883 = lean_ctor_get(x_753, 0);
lean_inc(x_883);
x_884 = lean_ctor_get(x_753, 1);
lean_inc(x_884);
if (lean_is_exclusive(x_753)) {
 lean_ctor_release(x_753, 0);
 lean_ctor_release(x_753, 1);
 x_885 = x_753;
} else {
 lean_dec_ref(x_753);
 x_885 = lean_box(0);
}
if (lean_is_scalar(x_885)) {
 x_886 = lean_alloc_ctor(1, 2, 0);
} else {
 x_886 = x_885;
}
lean_ctor_set(x_886, 0, x_883);
lean_ctor_set(x_886, 1, x_884);
return x_886;
}
}
else
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_887 = lean_ctor_get(x_749, 0);
lean_inc(x_887);
x_888 = lean_ctor_get(x_749, 1);
lean_inc(x_888);
if (lean_is_exclusive(x_749)) {
 lean_ctor_release(x_749, 0);
 lean_ctor_release(x_749, 1);
 x_889 = x_749;
} else {
 lean_dec_ref(x_749);
 x_889 = lean_box(0);
}
if (lean_is_scalar(x_889)) {
 x_890 = lean_alloc_ctor(1, 2, 0);
} else {
 x_890 = x_889;
}
lean_ctor_set(x_890, 0, x_887);
lean_ctor_set(x_890, 1, x_888);
return x_890;
}
}
else
{
lean_object* x_891; lean_object* x_892; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
x_891 = lean_ctor_get(x_746, 1);
lean_inc(x_891);
lean_dec_ref(x_746);
x_892 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_891);
return x_892;
}
}
else
{
lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_893 = lean_ctor_get(x_735, 0);
lean_inc(x_893);
x_894 = lean_ctor_get(x_735, 1);
lean_inc(x_894);
if (lean_is_exclusive(x_735)) {
 lean_ctor_release(x_735, 0);
 lean_ctor_release(x_735, 1);
 x_895 = x_735;
} else {
 lean_dec_ref(x_735);
 x_895 = lean_box(0);
}
if (lean_is_scalar(x_895)) {
 x_896 = lean_alloc_ctor(1, 2, 0);
} else {
 x_896 = x_895;
}
lean_ctor_set(x_896, 0, x_893);
lean_ctor_set(x_896, 1, x_894);
return x_896;
}
}
else
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_897 = lean_ctor_get(x_731, 0);
lean_inc(x_897);
x_898 = lean_ctor_get(x_731, 1);
lean_inc(x_898);
if (lean_is_exclusive(x_731)) {
 lean_ctor_release(x_731, 0);
 lean_ctor_release(x_731, 1);
 x_899 = x_731;
} else {
 lean_dec_ref(x_731);
 x_899 = lean_box(0);
}
if (lean_is_scalar(x_899)) {
 x_900 = lean_alloc_ctor(1, 2, 0);
} else {
 x_900 = x_899;
}
lean_ctor_set(x_900, 0, x_897);
lean_ctor_set(x_900, 1, x_898);
return x_900;
}
}
else
{
lean_object* x_901; lean_object* x_902; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
x_901 = lean_ctor_get(x_728, 1);
lean_inc(x_901);
lean_dec_ref(x_728);
x_902 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_901);
return x_902;
}
}
}
else
{
uint8_t x_903; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_903 = !lean_is_exclusive(x_89);
if (x_903 == 0)
{
return x_89;
}
else
{
lean_object* x_904; lean_object* x_905; lean_object* x_906; 
x_904 = lean_ctor_get(x_89, 0);
x_905 = lean_ctor_get(x_89, 1);
lean_inc(x_905);
lean_inc(x_904);
lean_dec(x_89);
x_906 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_906, 0, x_904);
lean_ctor_set(x_906, 1, x_905);
return x_906;
}
}
}
else
{
uint8_t x_907; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_907 = !lean_is_exclusive(x_85);
if (x_907 == 0)
{
return x_85;
}
else
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; 
x_908 = lean_ctor_get(x_85, 0);
x_909 = lean_ctor_get(x_85, 1);
lean_inc(x_909);
lean_inc(x_908);
lean_dec(x_85);
x_910 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_910, 0, x_908);
lean_ctor_set(x_910, 1, x_909);
return x_910;
}
}
}
else
{
lean_object* x_911; lean_object* x_912; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
x_911 = lean_ctor_get(x_82, 1);
lean_inc(x_911);
lean_dec_ref(x_82);
x_912 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_911);
return x_912;
}
}
else
{
lean_object* x_913; lean_object* x_914; lean_object* x_915; uint8_t x_916; 
x_913 = lean_ctor_get(x_78, 1);
lean_inc(x_913);
lean_dec(x_78);
x_914 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_914, 0, x_76);
lean_ctor_set(x_914, 1, x_913);
x_915 = lean_st_ref_set(x_55, x_914, x_79);
x_916 = lean_unbox(x_75);
lean_dec(x_75);
if (x_916 == 0)
{
lean_object* x_917; lean_object* x_918; 
x_917 = lean_ctor_get(x_915, 1);
lean_inc(x_917);
lean_dec_ref(x_915);
x_918 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_917);
if (lean_obj_tag(x_918) == 0)
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; 
x_919 = lean_ctor_get(x_918, 0);
lean_inc(x_919);
x_920 = lean_ctor_get(x_918, 1);
lean_inc(x_920);
lean_dec_ref(x_918);
x_921 = lean_ctor_get(x_919, 0);
lean_inc(x_921);
lean_dec(x_919);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_922 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_921, x_48, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_920);
if (lean_obj_tag(x_922) == 0)
{
lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; uint8_t x_934; 
x_923 = lean_ctor_get(x_922, 0);
lean_inc(x_923);
x_924 = lean_ctor_get(x_922, 1);
lean_inc(x_924);
lean_dec_ref(x_922);
x_925 = lean_ctor_get(x_923, 0);
lean_inc(x_925);
x_926 = lean_ctor_get(x_923, 1);
lean_inc(x_926);
lean_dec(x_923);
x_927 = lean_st_ref_take(x_55, x_924);
x_928 = lean_ctor_get(x_927, 0);
lean_inc(x_928);
x_929 = lean_ctor_get(x_927, 1);
lean_inc(x_929);
lean_dec_ref(x_927);
x_930 = lean_ctor_get(x_928, 1);
lean_inc(x_930);
if (lean_is_exclusive(x_928)) {
 lean_ctor_release(x_928, 0);
 lean_ctor_release(x_928, 1);
 x_931 = x_928;
} else {
 lean_dec_ref(x_928);
 x_931 = lean_box(0);
}
if (lean_is_scalar(x_931)) {
 x_932 = lean_alloc_ctor(0, 2, 0);
} else {
 x_932 = x_931;
}
lean_ctor_set(x_932, 0, x_926);
lean_ctor_set(x_932, 1, x_930);
x_933 = lean_st_ref_set(x_55, x_932, x_929);
x_934 = lean_unbox(x_925);
lean_dec(x_925);
if (x_934 == 0)
{
lean_object* x_935; lean_object* x_936; 
x_935 = lean_ctor_get(x_933, 1);
lean_inc(x_935);
lean_dec_ref(x_933);
x_936 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_935);
if (lean_obj_tag(x_936) == 0)
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; 
x_937 = lean_ctor_get(x_936, 0);
lean_inc(x_937);
x_938 = lean_ctor_get(x_936, 1);
lean_inc(x_938);
lean_dec_ref(x_936);
x_939 = lean_ctor_get(x_937, 0);
lean_inc(x_939);
lean_dec(x_937);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_940 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_939, x_49, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_938);
if (lean_obj_tag(x_940) == 0)
{
lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; uint8_t x_952; 
x_941 = lean_ctor_get(x_940, 0);
lean_inc(x_941);
x_942 = lean_ctor_get(x_940, 1);
lean_inc(x_942);
lean_dec_ref(x_940);
x_943 = lean_ctor_get(x_941, 0);
lean_inc(x_943);
x_944 = lean_ctor_get(x_941, 1);
lean_inc(x_944);
lean_dec(x_941);
x_945 = lean_st_ref_take(x_55, x_942);
x_946 = lean_ctor_get(x_945, 0);
lean_inc(x_946);
x_947 = lean_ctor_get(x_945, 1);
lean_inc(x_947);
lean_dec_ref(x_945);
x_948 = lean_ctor_get(x_946, 1);
lean_inc(x_948);
if (lean_is_exclusive(x_946)) {
 lean_ctor_release(x_946, 0);
 lean_ctor_release(x_946, 1);
 x_949 = x_946;
} else {
 lean_dec_ref(x_946);
 x_949 = lean_box(0);
}
if (lean_is_scalar(x_949)) {
 x_950 = lean_alloc_ctor(0, 2, 0);
} else {
 x_950 = x_949;
}
lean_ctor_set(x_950, 0, x_944);
lean_ctor_set(x_950, 1, x_948);
x_951 = lean_st_ref_set(x_55, x_950, x_947);
x_952 = lean_unbox(x_943);
lean_dec(x_943);
if (x_952 == 0)
{
lean_object* x_953; lean_object* x_954; 
x_953 = lean_ctor_get(x_951, 1);
lean_inc(x_953);
lean_dec_ref(x_951);
x_954 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_953);
if (lean_obj_tag(x_954) == 0)
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; 
x_955 = lean_ctor_get(x_954, 0);
lean_inc(x_955);
x_956 = lean_ctor_get(x_954, 1);
lean_inc(x_956);
lean_dec_ref(x_954);
x_957 = lean_ctor_get(x_955, 0);
lean_inc(x_957);
lean_dec(x_955);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_958 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_957, x_50, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_956);
if (lean_obj_tag(x_958) == 0)
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; uint8_t x_970; 
x_959 = lean_ctor_get(x_958, 0);
lean_inc(x_959);
x_960 = lean_ctor_get(x_958, 1);
lean_inc(x_960);
lean_dec_ref(x_958);
x_961 = lean_ctor_get(x_959, 0);
lean_inc(x_961);
x_962 = lean_ctor_get(x_959, 1);
lean_inc(x_962);
lean_dec(x_959);
x_963 = lean_st_ref_take(x_55, x_960);
x_964 = lean_ctor_get(x_963, 0);
lean_inc(x_964);
x_965 = lean_ctor_get(x_963, 1);
lean_inc(x_965);
lean_dec_ref(x_963);
x_966 = lean_ctor_get(x_964, 1);
lean_inc(x_966);
if (lean_is_exclusive(x_964)) {
 lean_ctor_release(x_964, 0);
 lean_ctor_release(x_964, 1);
 x_967 = x_964;
} else {
 lean_dec_ref(x_964);
 x_967 = lean_box(0);
}
if (lean_is_scalar(x_967)) {
 x_968 = lean_alloc_ctor(0, 2, 0);
} else {
 x_968 = x_967;
}
lean_ctor_set(x_968, 0, x_962);
lean_ctor_set(x_968, 1, x_966);
x_969 = lean_st_ref_set(x_55, x_968, x_965);
x_970 = lean_unbox(x_961);
lean_dec(x_961);
if (x_970 == 0)
{
lean_object* x_971; lean_object* x_972; 
x_971 = lean_ctor_get(x_969, 1);
lean_inc(x_971);
lean_dec_ref(x_969);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_972 = l_Lean_Meta_Grind_splitNext(x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_971);
if (lean_obj_tag(x_972) == 0)
{
lean_object* x_973; uint8_t x_974; 
x_973 = lean_ctor_get(x_972, 0);
lean_inc(x_973);
x_974 = lean_unbox(x_973);
lean_dec(x_973);
if (x_974 == 0)
{
lean_object* x_975; lean_object* x_976; 
x_975 = lean_ctor_get(x_972, 1);
lean_inc(x_975);
lean_dec_ref(x_972);
x_976 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_975);
if (lean_obj_tag(x_976) == 0)
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; 
x_977 = lean_ctor_get(x_976, 0);
lean_inc(x_977);
x_978 = lean_ctor_get(x_976, 1);
lean_inc(x_978);
lean_dec_ref(x_976);
x_979 = lean_ctor_get(x_977, 0);
lean_inc(x_979);
lean_dec(x_977);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_980 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_979, x_51, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_978);
if (lean_obj_tag(x_980) == 0)
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; uint8_t x_992; 
x_981 = lean_ctor_get(x_980, 0);
lean_inc(x_981);
x_982 = lean_ctor_get(x_980, 1);
lean_inc(x_982);
lean_dec_ref(x_980);
x_983 = lean_ctor_get(x_981, 0);
lean_inc(x_983);
x_984 = lean_ctor_get(x_981, 1);
lean_inc(x_984);
lean_dec(x_981);
x_985 = lean_st_ref_take(x_55, x_982);
x_986 = lean_ctor_get(x_985, 0);
lean_inc(x_986);
x_987 = lean_ctor_get(x_985, 1);
lean_inc(x_987);
lean_dec_ref(x_985);
x_988 = lean_ctor_get(x_986, 1);
lean_inc(x_988);
if (lean_is_exclusive(x_986)) {
 lean_ctor_release(x_986, 0);
 lean_ctor_release(x_986, 1);
 x_989 = x_986;
} else {
 lean_dec_ref(x_986);
 x_989 = lean_box(0);
}
if (lean_is_scalar(x_989)) {
 x_990 = lean_alloc_ctor(0, 2, 0);
} else {
 x_990 = x_989;
}
lean_ctor_set(x_990, 0, x_984);
lean_ctor_set(x_990, 1, x_988);
x_991 = lean_st_ref_set(x_55, x_990, x_987);
x_992 = lean_unbox(x_983);
lean_dec(x_983);
if (x_992 == 0)
{
lean_object* x_993; lean_object* x_994; 
x_993 = lean_ctor_get(x_991, 1);
lean_inc(x_993);
lean_dec_ref(x_991);
x_994 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_993);
if (lean_obj_tag(x_994) == 0)
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; 
x_995 = lean_ctor_get(x_994, 0);
lean_inc(x_995);
x_996 = lean_ctor_get(x_994, 1);
lean_inc(x_996);
lean_dec_ref(x_994);
x_997 = lean_ctor_get(x_995, 0);
lean_inc(x_997);
lean_dec(x_995);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_998 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_997, x_52, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_996);
if (lean_obj_tag(x_998) == 0)
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; uint8_t x_1010; 
x_999 = lean_ctor_get(x_998, 0);
lean_inc(x_999);
x_1000 = lean_ctor_get(x_998, 1);
lean_inc(x_1000);
lean_dec_ref(x_998);
x_1001 = lean_ctor_get(x_999, 0);
lean_inc(x_1001);
x_1002 = lean_ctor_get(x_999, 1);
lean_inc(x_1002);
lean_dec(x_999);
x_1003 = lean_st_ref_take(x_55, x_1000);
x_1004 = lean_ctor_get(x_1003, 0);
lean_inc(x_1004);
x_1005 = lean_ctor_get(x_1003, 1);
lean_inc(x_1005);
lean_dec_ref(x_1003);
x_1006 = lean_ctor_get(x_1004, 1);
lean_inc(x_1006);
if (lean_is_exclusive(x_1004)) {
 lean_ctor_release(x_1004, 0);
 lean_ctor_release(x_1004, 1);
 x_1007 = x_1004;
} else {
 lean_dec_ref(x_1004);
 x_1007 = lean_box(0);
}
if (lean_is_scalar(x_1007)) {
 x_1008 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1008 = x_1007;
}
lean_ctor_set(x_1008, 0, x_1002);
lean_ctor_set(x_1008, 1, x_1006);
x_1009 = lean_st_ref_set(x_55, x_1008, x_1005);
x_1010 = lean_unbox(x_1001);
lean_dec(x_1001);
if (x_1010 == 0)
{
lean_object* x_1011; lean_object* x_1012; 
x_1011 = lean_ctor_get(x_1009, 1);
lean_inc(x_1011);
lean_dec_ref(x_1009);
x_1012 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_1011);
if (lean_obj_tag(x_1012) == 0)
{
lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; 
x_1013 = lean_ctor_get(x_1012, 0);
lean_inc(x_1013);
x_1014 = lean_ctor_get(x_1012, 1);
lean_inc(x_1014);
lean_dec_ref(x_1012);
x_1015 = lean_ctor_get(x_1013, 0);
lean_inc(x_1015);
lean_dec(x_1013);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_1016 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_1015, x_53, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_1014);
if (lean_obj_tag(x_1016) == 0)
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; uint8_t x_1028; 
x_1017 = lean_ctor_get(x_1016, 0);
lean_inc(x_1017);
x_1018 = lean_ctor_get(x_1016, 1);
lean_inc(x_1018);
lean_dec_ref(x_1016);
x_1019 = lean_ctor_get(x_1017, 0);
lean_inc(x_1019);
x_1020 = lean_ctor_get(x_1017, 1);
lean_inc(x_1020);
lean_dec(x_1017);
x_1021 = lean_st_ref_take(x_55, x_1018);
x_1022 = lean_ctor_get(x_1021, 0);
lean_inc(x_1022);
x_1023 = lean_ctor_get(x_1021, 1);
lean_inc(x_1023);
lean_dec_ref(x_1021);
x_1024 = lean_ctor_get(x_1022, 1);
lean_inc(x_1024);
if (lean_is_exclusive(x_1022)) {
 lean_ctor_release(x_1022, 0);
 lean_ctor_release(x_1022, 1);
 x_1025 = x_1022;
} else {
 lean_dec_ref(x_1022);
 x_1025 = lean_box(0);
}
if (lean_is_scalar(x_1025)) {
 x_1026 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1026 = x_1025;
}
lean_ctor_set(x_1026, 0, x_1020);
lean_ctor_set(x_1026, 1, x_1024);
x_1027 = lean_st_ref_set(x_55, x_1026, x_1023);
x_1028 = lean_unbox(x_1019);
lean_dec(x_1019);
if (x_1028 == 0)
{
lean_object* x_1029; lean_object* x_1030; 
x_1029 = lean_ctor_get(x_1027, 1);
lean_inc(x_1029);
lean_dec_ref(x_1027);
x_1030 = l_Lean_Meta_Grind_getGoal___redArg(x_55, x_1029);
if (lean_obj_tag(x_1030) == 0)
{
lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; 
x_1031 = lean_ctor_get(x_1030, 0);
lean_inc(x_1031);
x_1032 = lean_ctor_get(x_1030, 1);
lean_inc(x_1032);
lean_dec_ref(x_1030);
x_1033 = lean_ctor_get(x_1031, 0);
lean_inc(x_1033);
lean_dec(x_1031);
lean_inc(x_55);
x_1034 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__0___redArg(x_1033, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_1032);
if (lean_obj_tag(x_1034) == 0)
{
lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; uint8_t x_1047; 
x_1035 = lean_ctor_get(x_1034, 0);
lean_inc(x_1035);
x_1036 = lean_ctor_get(x_1034, 1);
lean_inc(x_1036);
lean_dec_ref(x_1034);
x_1037 = lean_ctor_get(x_1035, 0);
lean_inc(x_1037);
x_1038 = lean_ctor_get(x_1035, 1);
lean_inc(x_1038);
lean_dec(x_1035);
x_1039 = lean_st_ref_take(x_55, x_1036);
x_1040 = lean_ctor_get(x_1039, 0);
lean_inc(x_1040);
x_1041 = lean_ctor_get(x_1039, 1);
lean_inc(x_1041);
lean_dec_ref(x_1039);
x_1042 = lean_ctor_get(x_1040, 1);
lean_inc(x_1042);
if (lean_is_exclusive(x_1040)) {
 lean_ctor_release(x_1040, 0);
 lean_ctor_release(x_1040, 1);
 x_1043 = x_1040;
} else {
 lean_dec_ref(x_1040);
 x_1043 = lean_box(0);
}
if (lean_is_scalar(x_1043)) {
 x_1044 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1044 = x_1043;
}
lean_ctor_set(x_1044, 0, x_1038);
lean_ctor_set(x_1044, 1, x_1042);
x_1045 = lean_st_ref_set(x_55, x_1044, x_1041);
x_1046 = lean_ctor_get(x_1045, 1);
lean_inc(x_1046);
lean_dec_ref(x_1045);
x_1047 = lean_unbox(x_1037);
lean_dec(x_1037);
x_12 = x_55;
x_13 = x_1047;
x_14 = x_1046;
goto block_32;
}
else
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
lean_dec(x_55);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1048 = lean_ctor_get(x_1034, 0);
lean_inc(x_1048);
x_1049 = lean_ctor_get(x_1034, 1);
lean_inc(x_1049);
if (lean_is_exclusive(x_1034)) {
 lean_ctor_release(x_1034, 0);
 lean_ctor_release(x_1034, 1);
 x_1050 = x_1034;
} else {
 lean_dec_ref(x_1034);
 x_1050 = lean_box(0);
}
if (lean_is_scalar(x_1050)) {
 x_1051 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1051 = x_1050;
}
lean_ctor_set(x_1051, 0, x_1048);
lean_ctor_set(x_1051, 1, x_1049);
return x_1051;
}
}
else
{
lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1052 = lean_ctor_get(x_1030, 0);
lean_inc(x_1052);
x_1053 = lean_ctor_get(x_1030, 1);
lean_inc(x_1053);
if (lean_is_exclusive(x_1030)) {
 lean_ctor_release(x_1030, 0);
 lean_ctor_release(x_1030, 1);
 x_1054 = x_1030;
} else {
 lean_dec_ref(x_1030);
 x_1054 = lean_box(0);
}
if (lean_is_scalar(x_1054)) {
 x_1055 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1055 = x_1054;
}
lean_ctor_set(x_1055, 0, x_1052);
lean_ctor_set(x_1055, 1, x_1053);
return x_1055;
}
}
else
{
lean_object* x_1056; lean_object* x_1057; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
x_1056 = lean_ctor_get(x_1027, 1);
lean_inc(x_1056);
lean_dec_ref(x_1027);
x_1057 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1056);
return x_1057;
}
}
else
{
lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1058 = lean_ctor_get(x_1016, 0);
lean_inc(x_1058);
x_1059 = lean_ctor_get(x_1016, 1);
lean_inc(x_1059);
if (lean_is_exclusive(x_1016)) {
 lean_ctor_release(x_1016, 0);
 lean_ctor_release(x_1016, 1);
 x_1060 = x_1016;
} else {
 lean_dec_ref(x_1016);
 x_1060 = lean_box(0);
}
if (lean_is_scalar(x_1060)) {
 x_1061 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1061 = x_1060;
}
lean_ctor_set(x_1061, 0, x_1058);
lean_ctor_set(x_1061, 1, x_1059);
return x_1061;
}
}
else
{
lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1062 = lean_ctor_get(x_1012, 0);
lean_inc(x_1062);
x_1063 = lean_ctor_get(x_1012, 1);
lean_inc(x_1063);
if (lean_is_exclusive(x_1012)) {
 lean_ctor_release(x_1012, 0);
 lean_ctor_release(x_1012, 1);
 x_1064 = x_1012;
} else {
 lean_dec_ref(x_1012);
 x_1064 = lean_box(0);
}
if (lean_is_scalar(x_1064)) {
 x_1065 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1065 = x_1064;
}
lean_ctor_set(x_1065, 0, x_1062);
lean_ctor_set(x_1065, 1, x_1063);
return x_1065;
}
}
else
{
lean_object* x_1066; lean_object* x_1067; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
x_1066 = lean_ctor_get(x_1009, 1);
lean_inc(x_1066);
lean_dec_ref(x_1009);
x_1067 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1066);
return x_1067;
}
}
else
{
lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1068 = lean_ctor_get(x_998, 0);
lean_inc(x_1068);
x_1069 = lean_ctor_get(x_998, 1);
lean_inc(x_1069);
if (lean_is_exclusive(x_998)) {
 lean_ctor_release(x_998, 0);
 lean_ctor_release(x_998, 1);
 x_1070 = x_998;
} else {
 lean_dec_ref(x_998);
 x_1070 = lean_box(0);
}
if (lean_is_scalar(x_1070)) {
 x_1071 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1071 = x_1070;
}
lean_ctor_set(x_1071, 0, x_1068);
lean_ctor_set(x_1071, 1, x_1069);
return x_1071;
}
}
else
{
lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1072 = lean_ctor_get(x_994, 0);
lean_inc(x_1072);
x_1073 = lean_ctor_get(x_994, 1);
lean_inc(x_1073);
if (lean_is_exclusive(x_994)) {
 lean_ctor_release(x_994, 0);
 lean_ctor_release(x_994, 1);
 x_1074 = x_994;
} else {
 lean_dec_ref(x_994);
 x_1074 = lean_box(0);
}
if (lean_is_scalar(x_1074)) {
 x_1075 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1075 = x_1074;
}
lean_ctor_set(x_1075, 0, x_1072);
lean_ctor_set(x_1075, 1, x_1073);
return x_1075;
}
}
else
{
lean_object* x_1076; lean_object* x_1077; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
x_1076 = lean_ctor_get(x_991, 1);
lean_inc(x_1076);
lean_dec_ref(x_991);
x_1077 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1076);
return x_1077;
}
}
else
{
lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1078 = lean_ctor_get(x_980, 0);
lean_inc(x_1078);
x_1079 = lean_ctor_get(x_980, 1);
lean_inc(x_1079);
if (lean_is_exclusive(x_980)) {
 lean_ctor_release(x_980, 0);
 lean_ctor_release(x_980, 1);
 x_1080 = x_980;
} else {
 lean_dec_ref(x_980);
 x_1080 = lean_box(0);
}
if (lean_is_scalar(x_1080)) {
 x_1081 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1081 = x_1080;
}
lean_ctor_set(x_1081, 0, x_1078);
lean_ctor_set(x_1081, 1, x_1079);
return x_1081;
}
}
else
{
lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1082 = lean_ctor_get(x_976, 0);
lean_inc(x_1082);
x_1083 = lean_ctor_get(x_976, 1);
lean_inc(x_1083);
if (lean_is_exclusive(x_976)) {
 lean_ctor_release(x_976, 0);
 lean_ctor_release(x_976, 1);
 x_1084 = x_976;
} else {
 lean_dec_ref(x_976);
 x_1084 = lean_box(0);
}
if (lean_is_scalar(x_1084)) {
 x_1085 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1085 = x_1084;
}
lean_ctor_set(x_1085, 0, x_1082);
lean_ctor_set(x_1085, 1, x_1083);
return x_1085;
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_33 = x_55;
x_34 = x_972;
goto block_42;
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_33 = x_55;
x_34 = x_972;
goto block_42;
}
}
else
{
lean_object* x_1086; lean_object* x_1087; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
x_1086 = lean_ctor_get(x_969, 1);
lean_inc(x_1086);
lean_dec_ref(x_969);
x_1087 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1086);
return x_1087;
}
}
else
{
lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1088 = lean_ctor_get(x_958, 0);
lean_inc(x_1088);
x_1089 = lean_ctor_get(x_958, 1);
lean_inc(x_1089);
if (lean_is_exclusive(x_958)) {
 lean_ctor_release(x_958, 0);
 lean_ctor_release(x_958, 1);
 x_1090 = x_958;
} else {
 lean_dec_ref(x_958);
 x_1090 = lean_box(0);
}
if (lean_is_scalar(x_1090)) {
 x_1091 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1091 = x_1090;
}
lean_ctor_set(x_1091, 0, x_1088);
lean_ctor_set(x_1091, 1, x_1089);
return x_1091;
}
}
else
{
lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_1092 = lean_ctor_get(x_954, 0);
lean_inc(x_1092);
x_1093 = lean_ctor_get(x_954, 1);
lean_inc(x_1093);
if (lean_is_exclusive(x_954)) {
 lean_ctor_release(x_954, 0);
 lean_ctor_release(x_954, 1);
 x_1094 = x_954;
} else {
 lean_dec_ref(x_954);
 x_1094 = lean_box(0);
}
if (lean_is_scalar(x_1094)) {
 x_1095 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1095 = x_1094;
}
lean_ctor_set(x_1095, 0, x_1092);
lean_ctor_set(x_1095, 1, x_1093);
return x_1095;
}
}
else
{
lean_object* x_1096; lean_object* x_1097; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
x_1096 = lean_ctor_get(x_951, 1);
lean_inc(x_1096);
lean_dec_ref(x_951);
x_1097 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1096);
return x_1097;
}
}
else
{
lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_1098 = lean_ctor_get(x_940, 0);
lean_inc(x_1098);
x_1099 = lean_ctor_get(x_940, 1);
lean_inc(x_1099);
if (lean_is_exclusive(x_940)) {
 lean_ctor_release(x_940, 0);
 lean_ctor_release(x_940, 1);
 x_1100 = x_940;
} else {
 lean_dec_ref(x_940);
 x_1100 = lean_box(0);
}
if (lean_is_scalar(x_1100)) {
 x_1101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1101 = x_1100;
}
lean_ctor_set(x_1101, 0, x_1098);
lean_ctor_set(x_1101, 1, x_1099);
return x_1101;
}
}
else
{
lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_1102 = lean_ctor_get(x_936, 0);
lean_inc(x_1102);
x_1103 = lean_ctor_get(x_936, 1);
lean_inc(x_1103);
if (lean_is_exclusive(x_936)) {
 lean_ctor_release(x_936, 0);
 lean_ctor_release(x_936, 1);
 x_1104 = x_936;
} else {
 lean_dec_ref(x_936);
 x_1104 = lean_box(0);
}
if (lean_is_scalar(x_1104)) {
 x_1105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1105 = x_1104;
}
lean_ctor_set(x_1105, 0, x_1102);
lean_ctor_set(x_1105, 1, x_1103);
return x_1105;
}
}
else
{
lean_object* x_1106; lean_object* x_1107; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
x_1106 = lean_ctor_get(x_933, 1);
lean_inc(x_1106);
lean_dec_ref(x_933);
x_1107 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1106);
return x_1107;
}
}
else
{
lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_1108 = lean_ctor_get(x_922, 0);
lean_inc(x_1108);
x_1109 = lean_ctor_get(x_922, 1);
lean_inc(x_1109);
if (lean_is_exclusive(x_922)) {
 lean_ctor_release(x_922, 0);
 lean_ctor_release(x_922, 1);
 x_1110 = x_922;
} else {
 lean_dec_ref(x_922);
 x_1110 = lean_box(0);
}
if (lean_is_scalar(x_1110)) {
 x_1111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1111 = x_1110;
}
lean_ctor_set(x_1111, 0, x_1108);
lean_ctor_set(x_1111, 1, x_1109);
return x_1111;
}
}
else
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_1112 = lean_ctor_get(x_918, 0);
lean_inc(x_1112);
x_1113 = lean_ctor_get(x_918, 1);
lean_inc(x_1113);
if (lean_is_exclusive(x_918)) {
 lean_ctor_release(x_918, 0);
 lean_ctor_release(x_918, 1);
 x_1114 = x_918;
} else {
 lean_dec_ref(x_918);
 x_1114 = lean_box(0);
}
if (lean_is_scalar(x_1114)) {
 x_1115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1115 = x_1114;
}
lean_ctor_set(x_1115, 0, x_1112);
lean_ctor_set(x_1115, 1, x_1113);
return x_1115;
}
}
else
{
lean_object* x_1116; lean_object* x_1117; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
x_1116 = lean_ctor_get(x_915, 1);
lean_inc(x_1116);
lean_dec_ref(x_915);
x_1117 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1116);
return x_1117;
}
}
}
else
{
uint8_t x_1118; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_1118 = !lean_is_exclusive(x_72);
if (x_1118 == 0)
{
return x_72;
}
else
{
lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; 
x_1119 = lean_ctor_get(x_72, 0);
x_1120 = lean_ctor_get(x_72, 1);
lean_inc(x_1120);
lean_inc(x_1119);
lean_dec(x_72);
x_1121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1121, 0, x_1119);
lean_ctor_set(x_1121, 1, x_1120);
return x_1121;
}
}
}
else
{
uint8_t x_1122; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
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
x_1122 = !lean_is_exclusive(x_68);
if (x_1122 == 0)
{
return x_68;
}
else
{
lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; 
x_1123 = lean_ctor_get(x_68, 0);
x_1124 = lean_ctor_get(x_68, 1);
lean_inc(x_1124);
lean_inc(x_1123);
lean_dec(x_68);
x_1125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1125, 0, x_1123);
lean_ctor_set(x_1125, 1, x_1124);
return x_1125;
}
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
x_33 = x_55;
x_34 = x_64;
goto block_42;
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
x_33 = x_55;
x_34 = x_64;
goto block_42;
}
}
}
else
{
uint8_t x_1145; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_1145 = !lean_is_exclusive(x_43);
if (x_1145 == 0)
{
return x_43;
}
else
{
lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; 
x_1146 = lean_ctor_get(x_43, 0);
x_1147 = lean_ctor_get(x_43, 1);
lean_inc(x_1147);
lean_inc(x_1146);
lean_dec(x_43);
x_1148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1148, 0, x_1146);
lean_ctor_set(x_1148, 1, x_1147);
return x_1148;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop_spec__1_spec__1___redArg___lam__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
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
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Lean_Meta_Grind_getConfig___redArg(x_3, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_st_ref_get(x_16, x_20);
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_14, 1, x_23);
lean_ctor_set(x_14, 0, x_19);
lean_ctor_set(x_21, 0, x_14);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_14, 1, x_24);
lean_ctor_set(x_14, 0, x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_14);
lean_dec(x_16);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
x_33 = l_Lean_Meta_Grind_getConfig___redArg(x_3, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = lean_st_ref_get(x_31, x_35);
lean_dec(x_31);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_37);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_31);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_44 = x_33;
} else {
 lean_dec_ref(x_33);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
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
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lean_Meta_Grind_reportIssue(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_st_ref_get(x_17, x_21);
lean_dec(x_17);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_20);
lean_ctor_set(x_22, 0, x_15);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_22);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_20);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_free_object(x_15);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = l_Lean_Meta_Grind_reportIssue(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = lean_st_ref_get(x_32, x_36);
lean_dec(x_32);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_38);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_32);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_45 = x_34;
} else {
 lean_dec_ref(x_34);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
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
lean_dec(x_27);
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
lean_dec(x_27);
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
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_mk_ref(x_1, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_14 = l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_st_ref_get(x_12, x_16);
lean_dec(x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_10, 1, x_19);
lean_ctor_set(x_10, 0, x_15);
lean_ctor_set(x_17, 0, x_10);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_10, 1, x_20);
lean_ctor_set(x_10, 0, x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_free_object(x_10);
lean_dec(x_12);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
lean_inc(x_27);
x_29 = l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_main(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = lean_st_ref_get(x_27, x_31);
lean_dec(x_27);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_33);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_27);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_40 = x_29;
} else {
 lean_dec_ref(x_29);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
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
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Lookahead(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Intro(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Check(uint8_t builtin, lean_object*);
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
res = initialize_Lean_Meta_Tactic_Grind_Arith(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Lookahead(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0___redArg___closed__0();
l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_MVarId_isAssigned___at___Lean_Meta_Grind_tryFallback_spec__0_spec__0_spec__0___redArg___closed__1();
l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Solve_0__Lean_Meta_Grind_solve_loop___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
