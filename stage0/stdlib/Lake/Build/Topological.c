// Lean compiler output
// Module: Lake.Build.Topological
// Imports: Lake.Util.Cycle Lake.Util.Store Lake.Util.EquipT
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
LEAN_EXPORT lean_object* l_Lake_recFetch___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_recFetchAcyclic___rarg___lambda__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_partition_loop___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_recFetchAcyclic___rarg___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lake_recFetch___rarg), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lake_recFetch___rarg), 2, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_4);
x_7 = lean_apply_3(x_5, lean_box(0), x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___rarg___lambda__1), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_5);
x_7 = lean_apply_2(x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lake_recFetchAcyclic___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_1, x_3, x_2);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
static lean_object* _init_l_Lake_recFetchAcyclic___rarg___lambda__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_List_elem___rarg(x_1, x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_1);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_6);
x_10 = lean_apply_3(x_8, lean_box(0), x_9, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
lean_inc(x_2);
x_12 = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___rarg___lambda__3___boxed), 3, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
x_13 = lean_box(0);
x_14 = l_Lake_recFetchAcyclic___rarg___lambda__4___closed__1;
x_15 = l_List_partition_loop___rarg(x_12, x_6, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_2);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_13);
x_19 = l_List_appendTR___rarg(x_17, x_18);
x_20 = lean_apply_2(x_11, lean_box(0), x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_6);
x_8 = lean_apply_1(x_1, x_6);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___rarg___lambda__2), 5, 4);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_7);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_6);
lean_inc(x_9);
lean_inc(x_11);
x_13 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_11, x_12);
x_14 = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___rarg___lambda__4), 6, 5);
lean_closure_set(x_14, 0, x_5);
lean_closure_set(x_14, 1, x_8);
lean_closure_set(x_14, 2, x_10);
lean_closure_set(x_14, 3, x_13);
lean_closure_set(x_14, 4, x_3);
x_15 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_11, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___rarg___lambda__5), 7, 5);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_5);
lean_closure_set(x_7, 4, x_1);
x_8 = l_Lake_recFetch___rarg(x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___rarg), 6, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lake_recFetchAcyclic___rarg___lambda__3(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
lean_inc(x_5);
x_7 = lean_apply_2(x_6, x_2, x_5);
x_8 = lean_alloc_closure((void*)(l_Lake_recFetchMemoize___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_5);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_4);
x_7 = lean_alloc_closure((void*)(l_Lake_recFetchMemoize___rarg___lambda__2), 5, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_4);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_2(x_11, lean_box(0), x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___rarg___lambda__1), 4, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_9);
x_11 = lean_apply_2(x_3, x_4, x_10);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_inc(x_6);
x_13 = lean_apply_1(x_12, x_6);
lean_inc(x_8);
x_14 = lean_alloc_closure((void*)(l_Lake_recFetchMemoize___rarg___lambda__3), 6, 5);
lean_closure_set(x_14, 0, x_5);
lean_closure_set(x_14, 1, x_6);
lean_closure_set(x_14, 2, x_7);
lean_closure_set(x_14, 3, x_8);
lean_closure_set(x_14, 4, x_11);
x_15 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_7);
x_9 = lean_apply_1(x_1, x_7);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l_Lake_recFetchMemoize___rarg___lambda__4), 9, 8);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_8);
lean_closure_set(x_13, 2, x_4);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_5);
lean_closure_set(x_13, 5, x_9);
lean_closure_set(x_13, 6, x_2);
lean_closure_set(x_13, 7, x_10);
lean_inc(x_10);
lean_inc(x_12);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
x_15 = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___rarg___lambda__4), 6, 5);
lean_closure_set(x_15, 0, x_6);
lean_closure_set(x_15, 1, x_9);
lean_closure_set(x_15, 2, x_11);
lean_closure_set(x_15, 3, x_14);
lean_closure_set(x_15, 4, x_3);
x_16 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lake_recFetchMemoize___rarg___lambda__5), 8, 6);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_6);
lean_closure_set(x_8, 4, x_4);
lean_closure_set(x_8, 5, x_1);
x_9 = l_Lake_recFetch___rarg(x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lake_recFetchMemoize___rarg), 7, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_recFetchMemoize___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* initialize_Lake_Util_Cycle(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Store(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_EquipT(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Topological(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Cycle(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Store(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_EquipT(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_recFetchAcyclic___rarg___lambda__4___closed__1 = _init_l_Lake_recFetchAcyclic___rarg___lambda__4___closed__1();
lean_mark_persistent(l_Lake_recFetchAcyclic___rarg___lambda__4___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
