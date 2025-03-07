// Lean compiler output
// Module: Lake.Util.Task
// Imports: Init.Control.Option
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
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__7(lean_object*, lean_object*);
static lean_object* l_Lake_instMonadTask__lake___closed__1;
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedBaseIOTask___rarg(lean_object*);
static lean_object* l_Lake_instMonadTask__lake___closed__2;
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake;
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instInhabitedOptionIOTask___closed__1;
static lean_object* l_Lake_instMonadTask__lake___closed__9;
lean_object* lean_task_pure(lean_object*);
static lean_object* l_Lake_instMonadTask__lake___closed__4;
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__3(lean_object*, lean_object*);
lean_object* l_Function_const___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__9(lean_object*, lean_object*);
static lean_object* l_Lake_instMonadTask__lake___closed__3;
LEAN_EXPORT lean_object* l_Lake_instInhabitedBaseIOTask(lean_object*);
extern lean_object* l_Task_Priority_default;
static lean_object* l_Lake_instMonadTask__lake___closed__7;
static lean_object* l_Lake_instMonadTask__lake___closed__5;
static lean_object* l_Lake_instMonadTask__lake___closed__6;
static lean_object* l_Lake_instMonadTask__lake___closed__10;
static lean_object* l_Lake_instMonadTask__lake___closed__8;
LEAN_EXPORT lean_object* l_Lake_instMonadBaseIOTask;
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instInhabitedOptionIOTask(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = l_Task_Priority_default;
x_6 = 0;
x_7 = lean_task_map(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l_Function_const___rarg___boxed), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = l_Task_Priority_default;
x_7 = 0;
x_8 = lean_task_map(x_5, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_task_pure(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_1, x_3);
x_5 = l_Task_Priority_default;
x_6 = 0;
x_7 = lean_task_map(x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l_Lake_instMonadTask__lake___lambda__4), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = l_Task_Priority_default;
x_7 = 0;
x_8 = lean_task_bind(x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_task_pure(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_alloc_closure((void*)(l_Lake_instMonadTask__lake___lambda__6___boxed), 2, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = l_Task_Priority_default;
x_7 = 0;
x_8 = lean_task_bind(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l_Lake_instMonadTask__lake___lambda__7), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = l_Task_Priority_default;
x_7 = 0;
x_8 = lean_task_bind(x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l_Lake_instMonadTask__lake___lambda__9___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = l_Task_Priority_default;
x_7 = 0;
x_8 = lean_task_bind(x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = l_Task_Priority_default;
x_6 = 0;
x_7 = lean_task_bind(x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lake_instMonadTask__lake___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMonadTask__lake___lambda__1), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadTask__lake___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMonadTask__lake___lambda__2), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadTask__lake___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instMonadTask__lake___closed__1;
x_2 = l_Lake_instMonadTask__lake___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instMonadTask__lake___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMonadTask__lake___lambda__3), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadTask__lake___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMonadTask__lake___lambda__5), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadTask__lake___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMonadTask__lake___lambda__8), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadTask__lake___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMonadTask__lake___lambda__10), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadTask__lake___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lake_instMonadTask__lake___closed__3;
x_2 = l_Lake_instMonadTask__lake___closed__4;
x_3 = l_Lake_instMonadTask__lake___closed__5;
x_4 = l_Lake_instMonadTask__lake___closed__6;
x_5 = l_Lake_instMonadTask__lake___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_instMonadTask__lake___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMonadTask__lake___lambda__11), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadTask__lake___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instMonadTask__lake___closed__8;
x_2 = l_Lake_instMonadTask__lake___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instMonadTask__lake() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instMonadTask__lake___closed__10;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instMonadTask__lake___lambda__6(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lambda__9___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instMonadTask__lake___lambda__9(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instMonadBaseIOTask() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instMonadTask__lake;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedBaseIOTask___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_instMonadBaseIOTask;
x_3 = l_instInhabitedOfMonad___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedBaseIOTask(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instInhabitedBaseIOTask___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedOptionIOTask___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_task_pure(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedOptionIOTask(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instInhabitedOptionIOTask___closed__1;
return x_2;
}
}
lean_object* initialize_Init_Control_Option(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Task(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Option(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instMonadTask__lake___closed__1 = _init_l_Lake_instMonadTask__lake___closed__1();
lean_mark_persistent(l_Lake_instMonadTask__lake___closed__1);
l_Lake_instMonadTask__lake___closed__2 = _init_l_Lake_instMonadTask__lake___closed__2();
lean_mark_persistent(l_Lake_instMonadTask__lake___closed__2);
l_Lake_instMonadTask__lake___closed__3 = _init_l_Lake_instMonadTask__lake___closed__3();
lean_mark_persistent(l_Lake_instMonadTask__lake___closed__3);
l_Lake_instMonadTask__lake___closed__4 = _init_l_Lake_instMonadTask__lake___closed__4();
lean_mark_persistent(l_Lake_instMonadTask__lake___closed__4);
l_Lake_instMonadTask__lake___closed__5 = _init_l_Lake_instMonadTask__lake___closed__5();
lean_mark_persistent(l_Lake_instMonadTask__lake___closed__5);
l_Lake_instMonadTask__lake___closed__6 = _init_l_Lake_instMonadTask__lake___closed__6();
lean_mark_persistent(l_Lake_instMonadTask__lake___closed__6);
l_Lake_instMonadTask__lake___closed__7 = _init_l_Lake_instMonadTask__lake___closed__7();
lean_mark_persistent(l_Lake_instMonadTask__lake___closed__7);
l_Lake_instMonadTask__lake___closed__8 = _init_l_Lake_instMonadTask__lake___closed__8();
lean_mark_persistent(l_Lake_instMonadTask__lake___closed__8);
l_Lake_instMonadTask__lake___closed__9 = _init_l_Lake_instMonadTask__lake___closed__9();
lean_mark_persistent(l_Lake_instMonadTask__lake___closed__9);
l_Lake_instMonadTask__lake___closed__10 = _init_l_Lake_instMonadTask__lake___closed__10();
lean_mark_persistent(l_Lake_instMonadTask__lake___closed__10);
l_Lake_instMonadTask__lake = _init_l_Lake_instMonadTask__lake();
lean_mark_persistent(l_Lake_instMonadTask__lake);
l_Lake_instMonadBaseIOTask = _init_l_Lake_instMonadBaseIOTask();
lean_mark_persistent(l_Lake_instMonadBaseIOTask);
l_Lake_instInhabitedOptionIOTask___closed__1 = _init_l_Lake_instInhabitedOptionIOTask___closed__1();
lean_mark_persistent(l_Lake_instInhabitedOptionIOTask___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
