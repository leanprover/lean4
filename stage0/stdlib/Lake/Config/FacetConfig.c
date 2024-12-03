// Lean compiler output
// Module: Lake.Config.FacetConfig
// Imports: Lake.Build.Fetch
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
LEAN_EXPORT lean_object* l_Lake_FacetConfig_name___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkFacetJobConfig(lean_object*, lean_object*, lean_object*);
static lean_object* l_Functor_discard___at_Lake_mkFacetJobConfig___spec__1___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkFacetConfig___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig___rarg(lean_object*);
extern lean_object* l_Task_Priority_default;
LEAN_EXPORT lean_object* l_Lake_mkFacetJobConfig___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkFacetConfig___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkFacetConfig(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EResult_map___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_mkFacetJobConfig___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_FacetConfig_name(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_mkFacetJobConfig___spec__1___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_mkFacetJobConfig___spec__1(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig___rarg___boxed(lean_object*);
static lean_object* l_Lake_instInhabitedFacetConfig___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_mkFacetJobConfig___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig(lean_object*, lean_object*);
static lean_object* l_Functor_discard___at_Lake_mkFacetJobConfig___spec__1___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_FacetConfig_name___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
static lean_object* _init_l_Lake_instInhabitedFacetConfig___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instInhabitedFacetConfig___rarg___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_Lake_instInhabitedFacetConfig___rarg___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_instInhabitedFacetConfig___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_instInhabitedFacetConfig___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instInhabitedFacetConfig___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_name___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_name(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_FacetConfig_name___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_name___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_FacetConfig_name___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_mkFacetConfig___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_mkFacetConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lake_mkFacetConfig___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_mkFacetConfig___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_mkFacetConfig___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_mkFacetJobConfig___spec__1___rarg___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = lean_box(0);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
static lean_object* _init_l_Functor_discard___at_Lake_mkFacetJobConfig___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Functor_discard___at_Lake_mkFacetJobConfig___spec__1___rarg___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Functor_discard___at_Lake_mkFacetJobConfig___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Functor_discard___at_Lake_mkFacetJobConfig___spec__1___rarg___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lake_EResult_map___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_mkFacetJobConfig___spec__1___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Functor_discard___at_Lake_mkFacetJobConfig___spec__1___rarg___closed__2;
x_5 = l_Task_Priority_default;
x_6 = 0;
x_7 = lean_task_map(x_4, x_3, x_5, x_6);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_11 = l_Functor_discard___at_Lake_mkFacetJobConfig___spec__1___rarg___closed__2;
x_12 = l_Task_Priority_default;
x_13 = 0;
x_14 = lean_task_map(x_11, x_8, x_12, x_13);
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_10);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Functor_discard___at_Lake_mkFacetJobConfig___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Functor_discard___at_Lake_mkFacetJobConfig___spec__1___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_mkFacetJobConfig___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Functor_discard___at_Lake_mkFacetJobConfig___spec__1___rarg), 1, 0);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_mkFacetJobConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lake_mkFacetJobConfig___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_mkFacetJobConfig___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_mkFacetJobConfig___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Lake_Build_Fetch(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_FacetConfig(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Fetch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedFacetConfig___rarg___closed__1 = _init_l_Lake_instInhabitedFacetConfig___rarg___closed__1();
lean_mark_persistent(l_Lake_instInhabitedFacetConfig___rarg___closed__1);
l_Functor_discard___at_Lake_mkFacetJobConfig___spec__1___rarg___closed__1 = _init_l_Functor_discard___at_Lake_mkFacetJobConfig___spec__1___rarg___closed__1();
lean_mark_persistent(l_Functor_discard___at_Lake_mkFacetJobConfig___spec__1___rarg___closed__1);
l_Functor_discard___at_Lake_mkFacetJobConfig___spec__1___rarg___closed__2 = _init_l_Functor_discard___at_Lake_mkFacetJobConfig___spec__1___rarg___closed__2();
lean_mark_persistent(l_Functor_discard___at_Lake_mkFacetJobConfig___spec__1___rarg___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
