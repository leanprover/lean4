// Lean compiler output
// Module: Lean.Server.RequestCancellation
// Imports: Init.System.Promise Lean.Server.ServerTask
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
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadCancellableCancellableTOfMonadOfMonadLiftTBaseIO___redArg(lean_object*, lean_object*);
lean_object* lean_io_promise_new(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_check___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadCancellableOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___Lean_Server_CancellableM_checkCancelled_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancelByEdit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_check___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_editCancellationTask(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_wasCancelledByEdit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_run___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_checkCancelled___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancelByCancelRequest___boxed(lean_object*, lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancelByEdit(lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_requestCancelled;
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_noConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_check(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_toCtorIdx(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_check___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_noConfusion___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_wasCancelledByEdit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancelByCancelRequest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancellationTasks___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancellationTasks(lean_object*);
static lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(lean_object*, lean_object*);
lean_object* l_ExceptT_bindCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_wasCancelled(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_new(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_editCancellationTask___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_noConfusion___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___Lean_Server_CancellableM_checkCancelled_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_checkCancelled(lean_object*, lean_object*);
static lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_wasCancelled___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadCancellableCancellableTOfMonadOfMonadLiftTBaseIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadCancellableOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_new(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_st_mk_ref(x_3, x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_box(x_2);
x_8 = lean_st_mk_ref(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_io_promise_new(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_io_promise_new(x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_9);
lean_ctor_set(x_17, 2, x_12);
lean_ctor_set(x_17, 3, x_16);
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
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_9);
lean_ctor_set(x_20, 2, x_12);
lean_ctor_set(x_20, 3, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancelByCancelRequest(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 2);
x_5 = 1;
x_6 = lean_box(x_5);
x_7 = lean_st_ref_set(x_3, x_6, x_2);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_box(0);
x_10 = lean_io_promise_resolve(x_9, x_4, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancelByCancelRequest___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestCancellationToken_cancelByCancelRequest(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancelByEdit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 3);
x_5 = 1;
x_6 = lean_box(x_5);
x_7 = lean_st_ref_set(x_3, x_6, x_2);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_box(0);
x_10 = lean_io_promise_resolve(x_9, x_4, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancelByEdit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestCancellationToken_cancelByEdit(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l_IO_Promise_result_x21___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_RequestCancellationToken_requestCancellationTask(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_editCancellationTask(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = l_IO_Promise_result_x21___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_editCancellationTask___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_RequestCancellationToken_editCancellationTask(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancellationTasks(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Server_RequestCancellationToken_requestCancellationTask(x_1);
x_3 = l_Lean_Server_RequestCancellationToken_editCancellationTask(x_1);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancellationTasks___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_RequestCancellationToken_cancellationTasks(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_st_ref_get(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_wasCancelledByEdit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_st_ref_get(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_wasCancelledByEdit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestCancellationToken_wasCancelledByEdit(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_wasCancelled(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_Lean_Server_RequestCancellationToken_wasCancelledByEdit(x_1, x_5);
x_7 = lean_unbox(x_4);
if (x_7 == 0)
{
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_wasCancelled___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestCancellationToken_wasCancelled(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_toCtorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_RequestCancellation_toCtorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_noConfusion___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_noConfusion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_noConfusion___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_RequestCancellation_noConfusion___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_RequestCancellation_noConfusion(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Server_RequestCancellation_requestCancelled() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_run___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_3, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1(lean_object* x_1, uint8_t x_2) {
_start:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0;
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1;
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest___boxed), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_apply_2(x_2, lean_box(0), x_9);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_3, x_10);
x_12 = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(x_12, 0, lean_box(0));
lean_closure_set(x_12, 1, lean_box(0));
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, lean_box(0));
lean_closure_set(x_12, 4, lean_box(0));
lean_closure_set(x_12, 5, x_5);
x_13 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0___boxed), 1, 0);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_7);
lean_inc(x_5);
lean_inc_ref(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Server_CancellableT_checkCancelled___redArg___lam__2), 7, 6);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_8);
lean_closure_set(x_10, 3, x_1);
lean_closure_set(x_10, 4, x_9);
lean_closure_set(x_10, 5, x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_3);
x_12 = lean_apply_2(x_7, lean_box(0), x_11);
x_13 = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(x_13, 0, lean_box(0));
lean_closure_set(x_13, 1, lean_box(0));
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, lean_box(0));
lean_closure_set(x_13, 4, lean_box(0));
lean_closure_set(x_13, 5, x_10);
x_14 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_CancellableT_checkCancelled___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___Lean_Server_CancellableM_checkCancelled_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0;
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_dec(x_13);
x_14 = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1;
lean_ctor_set(x_3, 0, x_14);
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_dec(x_3);
x_16 = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_checkCancelled(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_CancellableT_checkCancelled___at___Lean_Server_CancellableM_checkCancelled_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___Lean_Server_CancellableM_checkCancelled_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_CancellableT_checkCancelled___at___Lean_Server_CancellableM_checkCancelled_spec__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_checkCancelled___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_CancellableM_checkCancelled(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadCancellableOfMonadLift___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadCancellableOfMonadLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadCancellableCancellableTOfMonadOfMonadLiftTBaseIO___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_CancellableT_checkCancelled), 4, 3);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_1);
lean_closure_set(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadCancellableCancellableTOfMonadOfMonadLiftTBaseIO(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Server_CancellableT_checkCancelled), 4, 3);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_check___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_check(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_check___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_RequestCancellation_check___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_check___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestCancellation_check(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init_System_Promise(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_ServerTask(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_RequestCancellation(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_Promise(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_ServerTask(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_RequestCancellation_requestCancelled = _init_l_Lean_Server_RequestCancellation_requestCancelled();
lean_mark_persistent(l_Lean_Server_RequestCancellation_requestCancelled);
l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0 = _init_l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0();
lean_mark_persistent(l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0);
l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1 = _init_l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1();
lean_mark_persistent(l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
