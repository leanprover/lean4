// Lean compiler output
// Module: Std.Sat.AIG.Relabel
// Imports: Std.Sat.AIG.Basic Std.Sat.AIG.Lemmas
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabel___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Std_Sat_AIG_relabel___spec__1___rarg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabel___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_relabel(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_Cache_empty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabel(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Relabel_0__Std_Sat_AIG_Decl_relabel_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Relabel_0__Std_Sat_AIG_Decl_relabel_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabel___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Std_Sat_AIG_relabel___spec__1(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_relabel___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Std_Sat_AIG_relabel___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_relabel___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_ctor_get_uint8(x_2, 0);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_5, 0, x_4);
return x_5;
}
}
case 1:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_apply_1(x_1, x_7);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_apply_1(x_1, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
default: 
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_17 = lean_alloc_ctor(2, 2, 2);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 1, x_16);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_relabel(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Sat_AIG_Decl_relabel___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Relabel_0__Std_Sat_AIG_Decl_relabel_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get_uint8(x_1, 0);
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
lean_dec(x_1);
x_14 = lean_box(x_12);
x_15 = lean_box(x_13);
x_16 = lean_apply_4(x_4, x_10, x_11, x_14, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Relabel_0__Std_Sat_AIG_Decl_relabel_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_Relabel_0__Std_Sat_AIG_Decl_relabel_match__1_splitter___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Std_Sat_AIG_relabel___spec__1___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
lean_inc(x_1);
x_9 = l_Std_Sat_AIG_Decl_relabel___rarg(x_1, x_6);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Std_Sat_AIG_relabel___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Std_Sat_AIG_relabel___spec__1___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_array_size(x_5);
x_7 = 0;
x_8 = l_Array_mapMUnsafe_map___at_Std_Sat_AIG_relabel___spec__1___rarg(x_3, x_6, x_7, x_5);
x_9 = l_Std_Sat_AIG_Cache_empty(lean_box(0), x_1, x_2, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_Sat_AIG_relabel___rarg___boxed), 4, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Std_Sat_AIG_relabel___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Std_Sat_AIG_relabel___spec__1___rarg(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Sat_AIG_relabel___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Sat_AIG_relabel(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabel___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Std_Sat_AIG_relabel___rarg(x_1, x_2, x_3, x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = l_Std_Sat_AIG_relabel___rarg(x_1, x_2, x_3, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_Sat_AIG_Entrypoint_relabel___rarg___boxed), 4, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabel___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Sat_AIG_Entrypoint_relabel___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Sat_AIG_Entrypoint_relabel(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Std_Sat_AIG_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_Lemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_Relabel(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
