// Lean compiler output
// Module: Lean.Data.LOption
// Imports: Init
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
LEAN_EXPORT lean_object* l_toLOptionM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption(lean_object*);
static lean_object* l_Lean_instToStringLOption___rarg___closed__2;
static lean_object* l_Lean_instToStringLOption___rarg___closed__3;
static lean_object* l_Lean_instToStringLOption___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lean_instBEqLOption(lean_object*);
LEAN_EXPORT lean_object* l_toLOptionM___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_toLOptionM___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_LOption_0__Lean_beqLOption____x40_Lean_Data_LOption___hyg_39____rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToStringLOption(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqLOption___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_LOption_0__Lean_beqLOption____x40_Lean_Data_LOption___hyg_39_(lean_object*);
LEAN_EXPORT lean_object* l_toLOptionM___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToStringLOption___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_instToStringLOption___rarg___closed__1;
LEAN_EXPORT lean_object* l_Option_toLOption___rarg___boxed(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_toLOption(lean_object*);
LEAN_EXPORT lean_object* l_Option_toLOption___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_LOption_0__Lean_beqLOption____x40_Lean_Data_LOption___hyg_39____rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; lean_object* x_5; 
x_4 = 1;
x_5 = lean_box(x_4);
return x_5;
}
else
{
uint8_t x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = 0;
x_7 = lean_box(x_6);
return x_7;
}
}
case 1:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_apply_2(x_1, x_8, x_9);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = 0;
x_12 = lean_box(x_11);
return x_12;
}
}
default: 
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 2)
{
uint8_t x_13; lean_object* x_14; 
x_13 = 1;
x_14 = lean_box(x_13);
return x_14;
}
else
{
uint8_t x_15; lean_object* x_16; 
lean_dec(x_3);
x_15 = 0;
x_16 = lean_box(x_15);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_LOption_0__Lean_beqLOption____x40_Lean_Data_LOption___hyg_39_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_LOption_0__Lean_beqLOption____x40_Lean_Data_LOption___hyg_39____rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLOption___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_LOption_0__Lean_beqLOption____x40_Lean_Data_LOption___hyg_39____rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instBEqLOption___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_instToStringLOption___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("none", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_instToStringLOption___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(some ", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_instToStringLOption___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_instToStringLOption___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("undef", 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringLOption___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = l_Lean_instToStringLOption___rarg___closed__1;
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = l_Lean_instToStringLOption___rarg___closed__2;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_instToStringLOption___rarg___closed__3;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
default: 
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = l_Lean_instToStringLOption___rarg___closed__4;
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringLOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToStringLOption___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_toLOption___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Option_toLOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_toLOption___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_toLOption___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Option_toLOption___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_toLOptionM___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Option_toLOption___rarg(x_2);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_toLOptionM___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_alloc_closure((void*)(l_toLOptionM___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_toLOptionM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_toLOptionM___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_toLOptionM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_toLOptionM___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_LOption(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instToStringLOption___rarg___closed__1 = _init_l_Lean_instToStringLOption___rarg___closed__1();
lean_mark_persistent(l_Lean_instToStringLOption___rarg___closed__1);
l_Lean_instToStringLOption___rarg___closed__2 = _init_l_Lean_instToStringLOption___rarg___closed__2();
lean_mark_persistent(l_Lean_instToStringLOption___rarg___closed__2);
l_Lean_instToStringLOption___rarg___closed__3 = _init_l_Lean_instToStringLOption___rarg___closed__3();
lean_mark_persistent(l_Lean_instToStringLOption___rarg___closed__3);
l_Lean_instToStringLOption___rarg___closed__4 = _init_l_Lean_instToStringLOption___rarg___closed__4();
lean_mark_persistent(l_Lean_instToStringLOption___rarg___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
