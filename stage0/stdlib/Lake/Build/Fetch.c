// Lean compiler output
// Module: Lake.Build.Fetch
// Imports: Lake.Util.Lift Lake.Util.Error Lake.Util.Cycle Lake.Util.EquipT Lake.Build.Info Lake.Build.Store Lake.Build.Context
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
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildCycleError___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ModuleFacet_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildCycleError___redArg___closed__1;
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadErrorOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ModuleFacet_fetch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildKey_instToString___lam__0(lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildCycleError___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__0___boxed(lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildCycleError(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildInfo_fetch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__0(lean_object*);
extern lean_object* l_Lake_Module_keyword;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lake_formatCycle___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_RecBuildT_run_x27___redArg___closed__0;
lean_object* l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg(lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildInfo_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake_buildCycleError___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_BuildKey_instToString___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_buildCycleError___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("build cycle detected:\n", 22, 22);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildCycleError___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lake_buildCycleError___redArg___closed__0;
x_4 = l_Lake_buildCycleError___redArg___closed__1;
x_5 = l_Lake_formatCycle___redArg(x_3, x_2);
x_6 = lean_string_append(x_4, x_5);
lean_dec(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_buildCycleError(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_buildCycleError___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lake_buildCycleError___redArg(x_1, x_3);
x_8 = lean_apply_3(x_7, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 3);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
lean_closure_set(x_1, 2, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = l_ReaderT_instMonad___redArg(x_1);
x_4 = l_ReaderT_instMonad___redArg(x_3);
x_5 = l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg(x_4);
x_6 = l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__0;
x_7 = l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__1;
x_8 = lean_alloc_closure((void*)(l_Lake_instMonadErrorOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_6);
x_9 = lean_alloc_closure((void*)(l_Lake_instMonadErrorOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_7);
x_10 = lean_alloc_closure((void*)(l_Lake_instMonadErrorOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_6);
x_11 = lean_alloc_closure((void*)(l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___lam__0), 6, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_Lake_RecBuildT_run___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_2);
x_8 = lean_apply_2(x_3, lean_box(0), x_7);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_3);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_Lake_RecBuildT_run___redArg___lam__1), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_3);
x_9 = lean_apply_3(x_4, x_5, x_7, x_6);
x_10 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_9, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Lake_RecBuildT_run___redArg___lam__2), 7, 6);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_8);
lean_closure_set(x_9, 3, x_5);
lean_closure_set(x_9, 4, x_3);
lean_closure_set(x_9, 5, x_6);
x_10 = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(x_10, 0, lean_box(0));
lean_closure_set(x_10, 1, lean_box(0));
lean_closure_set(x_10, 2, x_4);
x_11 = lean_apply_2(x_2, lean_box(0), x_10);
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_10);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Lake_RecBuildT_run___redArg___lam__2), 7, 6);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_10);
lean_closure_set(x_11, 3, x_7);
lean_closure_set(x_11, 4, x_5);
lean_closure_set(x_11, 5, x_8);
x_12 = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(x_12, 0, lean_box(0));
lean_closure_set(x_12, 1, lean_box(0));
lean_closure_set(x_12, 2, x_6);
x_13 = lean_apply_2(x_4, lean_box(0), x_12);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_13, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_Lake_RecBuildT_run_x27___redArg___lam__1), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_2);
x_8 = lean_apply_2(x_3, lean_box(0), x_7);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_3);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_Lake_RecBuildT_run_x27___redArg___lam__2), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_3);
x_9 = lean_apply_3(x_4, x_5, x_7, x_6);
x_10 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_9, x_8);
return x_10;
}
}
static lean_object* _init_l_Lake_RecBuildT_run_x27___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_closure((void*)(l_Lake_RecBuildT_run_x27___redArg___lam__0___boxed), 1, 0);
x_11 = lean_box(0);
lean_inc(x_7);
lean_inc(x_2);
x_12 = lean_alloc_closure((void*)(l_Lake_RecBuildT_run_x27___redArg___lam__3), 7, 6);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_7);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_11);
lean_closure_set(x_12, 5, x_4);
x_13 = l_Lake_RecBuildT_run_x27___redArg___closed__0;
x_14 = lean_apply_2(x_2, lean_box(0), x_13);
x_15 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_14, x_12);
x_16 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_10, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_closure((void*)(l_Lake_RecBuildT_run_x27___redArg___lam__0___boxed), 1, 0);
x_13 = lean_box(0);
lean_inc(x_9);
lean_inc(x_4);
x_14 = lean_alloc_closure((void*)(l_Lake_RecBuildT_run_x27___redArg___lam__3), 7, 6);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_4);
lean_closure_set(x_14, 2, x_9);
lean_closure_set(x_14, 3, x_5);
lean_closure_set(x_14, 4, x_13);
lean_closure_set(x_14, 5, x_6);
x_15 = l_Lake_RecBuildT_run_x27___redArg___closed__0;
x_16 = lean_apply_2(x_4, lean_box(0), x_15);
x_17 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_16, x_14);
x_18 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_12, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildT_run_x27___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_RecBuildT_run_x27___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_fetch___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_fetch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_6(x_4, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleFacet_fetch___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lake_Module_keyword;
x_12 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_2);
lean_ctor_set(x_12, 3, x_1);
x_13 = lean_apply_6(x_3, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_ModuleFacet_fetch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_ModuleFacet_fetch___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* initialize_Lake_Util_Lift(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Error(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Cycle(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_EquipT(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Info(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Store(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Context(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Fetch(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Lift(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Error(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Cycle(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_EquipT(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Info(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Store(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Context(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_buildCycleError___redArg___closed__0 = _init_l_Lake_buildCycleError___redArg___closed__0();
lean_mark_persistent(l_Lake_buildCycleError___redArg___closed__0);
l_Lake_buildCycleError___redArg___closed__1 = _init_l_Lake_buildCycleError___redArg___closed__1();
lean_mark_persistent(l_Lake_buildCycleError___redArg___closed__1);
l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__0 = _init_l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__0();
lean_mark_persistent(l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__0);
l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__1 = _init_l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__1();
lean_mark_persistent(l_Lake_instMonadCycleOfBuildKeyRecBuildTOfMonadOfMonadError___redArg___closed__1);
l_Lake_RecBuildT_run_x27___redArg___closed__0 = _init_l_Lake_RecBuildT_run_x27___redArg___closed__0();
lean_mark_persistent(l_Lake_RecBuildT_run_x27___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
