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
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_recFetchAcyclic___redArg___lam__3___closed__0;
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_recFetchAcyclic___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_partition_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lake_recFetch___redArg), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_recFetch___redArg(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_apply_3(x_2, lean_box(0), x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___redArg___lam__0), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_5);
x_7 = lean_apply_2(x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lake_recFetchAcyclic___redArg___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_apply_2(x_1, x_4, x_2);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
return x_3;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
}
}
static lean_object* _init_l_Lake_recFetchAcyclic___redArg___lam__3___closed__0() {
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
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_List_elem___redArg(x_1, x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_apply_3(x_3, lean_box(0), x_8, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_box(x_7);
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___redArg___lam__2___boxed), 4, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_10);
x_12 = lean_box(0);
x_13 = l_Lake_recFetchAcyclic___redArg___lam__3___closed__0;
x_14 = l_List_partition_loop___redArg(x_11, x_6, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_dec(x_17);
lean_inc(x_2);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 1, x_16);
lean_ctor_set(x_14, 0, x_2);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_12);
x_19 = l_List_appendTR___redArg(x_14, x_18);
x_20 = lean_apply_2(x_5, lean_box(0), x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
lean_inc(x_2);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_12);
x_24 = l_List_appendTR___redArg(x_22, x_23);
x_25 = lean_apply_2(x_5, lean_box(0), x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___redArg___lam__1), 5, 4);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_7);
x_12 = lean_apply_1(x_3, x_7);
lean_inc(x_4);
lean_inc(x_9);
x_13 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_9, x_11);
x_14 = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___redArg___lam__3), 6, 5);
lean_closure_set(x_14, 0, x_5);
lean_closure_set(x_14, 1, x_12);
lean_closure_set(x_14, 2, x_10);
lean_closure_set(x_14, 3, x_13);
lean_closure_set(x_14, 4, x_6);
x_15 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_9, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___redArg___lam__4), 8, 6);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_7);
lean_closure_set(x_10, 4, x_1);
lean_closure_set(x_10, 5, x_9);
x_11 = l_Lake_recFetch___redArg(x_10, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_recFetchAcyclic___redArg(x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lake_recFetchAcyclic___redArg___lam__2(x_1, x_2, x_5, x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lake_recFetchMemoize___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_apply_2(x_2, x_3, x_5);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = lean_apply_4(x_1, lean_box(0), lean_box(0), x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_2(x_4, lean_box(0), x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
lean_inc(x_5);
x_12 = lean_apply_1(x_3, x_5);
x_13 = lean_apply_2(x_4, x_5, x_6);
lean_inc(x_12);
x_14 = lean_apply_1(x_9, x_12);
lean_inc(x_8);
lean_inc(x_11);
x_15 = lean_alloc_closure((void*)(l_Lake_recFetchMemoize___redArg___lam__1), 5, 4);
lean_closure_set(x_15, 0, x_11);
lean_closure_set(x_15, 1, x_10);
lean_closure_set(x_15, 2, x_12);
lean_closure_set(x_15, 3, x_8);
lean_inc(x_8);
x_16 = lean_alloc_closure((void*)(l_Lake_recFetchMemoize___redArg___lam__2), 5, 4);
lean_closure_set(x_16, 0, x_8);
lean_closure_set(x_16, 1, x_13);
lean_closure_set(x_16, 2, x_15);
lean_closure_set(x_16, 3, x_11);
x_17 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_14, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_5);
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(l_Lake_recFetchMemoize___redArg___lam__3), 6, 4);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_5);
lean_closure_set(x_8, 3, x_6);
x_9 = l_Lake_recFetchAcyclic___redArg(x_1, x_2, x_3, x_5, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_recFetchMemoize___redArg(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_recFetchMemoize___redArg___lam__0(x_1, x_2, x_3);
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
l_Lake_recFetchAcyclic___redArg___lam__3___closed__0 = _init_l_Lake_recFetchAcyclic___redArg___lam__3___closed__0();
lean_mark_persistent(l_Lake_recFetchAcyclic___redArg___lam__3___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
