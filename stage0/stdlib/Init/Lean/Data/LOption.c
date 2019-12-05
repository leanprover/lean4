// Lean compiler output
// Module: Init.Lean.Data.LOption
// Imports: Init.Data.ToString
#include "runtime/lean.h"
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
extern lean_object* l_Option_HasRepr___rarg___closed__2;
lean_object* l_toLOptionM___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Option_toLOption___rarg(lean_object*);
lean_object* l_toLOptionM(lean_object*, lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__1;
lean_object* l_Lean_LOption_HasBeq(lean_object*);
lean_object* l_Lean_LOption_beq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_LOption_HasToString___rarg___closed__1;
lean_object* l_Lean_LOption_beq(lean_object*);
lean_object* l_Lean_LOption_HasToString___rarg(lean_object*, lean_object*);
lean_object* l_Lean_LOption_HasToString(lean_object*);
lean_object* l_Lean_LOption_Inhabited(lean_object*);
lean_object* l_Lean_LOption_HasBeq___rarg(lean_object*);
lean_object* l_Option_toLOption___rarg___boxed(lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l_Option_toLOption(lean_object*);
lean_object* l_toLOptionM___boxed(lean_object*, lean_object*);
lean_object* l_toLOptionM___rarg(lean_object*, lean_object*);
lean_object* l_toLOptionM___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_LOption_Inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* _init_l_Lean_LOption_HasToString___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("undef");
return x_1;
}
}
lean_object* l_Lean_LOption_HasToString___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = l_Option_HasRepr___rarg___closed__1;
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = l_Option_HasRepr___rarg___closed__2;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Option_HasRepr___rarg___closed__3;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
default: 
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = l_Lean_LOption_HasToString___rarg___closed__1;
return x_10;
}
}
}
}
lean_object* l_Lean_LOption_HasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LOption_HasToString___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_LOption_beq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_LOption_beq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LOption_beq___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_LOption_HasBeq___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LOption_beq___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_LOption_HasBeq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LOption_HasBeq___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Option_toLOption___rarg(lean_object* x_1) {
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
lean_object* l_Option_toLOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_toLOption___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Option_toLOption___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Option_toLOption___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_toLOptionM___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_toLOptionM___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_toLOptionM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_toLOptionM___rarg), 2, 0);
return x_3;
}
}
lean_object* l_toLOptionM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_toLOptionM___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_toLOptionM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_toLOptionM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init_Data_ToString(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Data_LOption(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_LOption_HasToString___rarg___closed__1 = _init_l_Lean_LOption_HasToString___rarg___closed__1();
lean_mark_persistent(l_Lean_LOption_HasToString___rarg___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
