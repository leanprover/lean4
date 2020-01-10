// Lean compiler output
// Module: Init.Lean.Data.Occurrences
// Imports: Init.Data.Nat
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
lean_object* l_Lean_Occurrences_contains___boxed(lean_object*, lean_object*);
uint8_t l_List_elem___main___at_Lean_Occurrences_contains___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Occurrences_beq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Occurrences_HasBeq;
uint8_t l_Lean_Occurrences_contains(lean_object*, lean_object*);
uint8_t l_List_beq___main___at_Lean_Occurrences_beq___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Occurrences_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Occurrences_Inhabited;
lean_object* l_Lean_Occurrences_HasBeq___closed__1;
lean_object* l_List_elem___main___at_Lean_Occurrences_contains___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Occurrences_isAll___boxed(lean_object*);
uint8_t l_Lean_Occurrences_isAll(lean_object*);
lean_object* l_List_beq___main___at_Lean_Occurrences_beq___spec__1___boxed(lean_object*, lean_object*);
lean_object* _init_l_Lean_Occurrences_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
uint8_t l_List_elem___main___at_Lean_Occurrences_contains___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_nat_dec_eq(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
uint8_t l_Lean_Occurrences_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
case 1:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_List_elem___main___at_Lean_Occurrences_contains___spec__1(x_2, x_4);
return x_5;
}
default: 
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = l_List_elem___main___at_Lean_Occurrences_contains___spec__1(x_2, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
}
}
}
lean_object* l_List_elem___main___at_Lean_Occurrences_contains___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___main___at_Lean_Occurrences_contains___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Occurrences_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Occurrences_contains(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_Occurrences_isAll(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Occurrences_isAll___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Occurrences_isAll(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_List_beq___main___at_Lean_Occurrences_beq___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_nat_dec_eq(x_6, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
}
uint8_t l_Lean_Occurrences_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_2, 0);
x_7 = l_List_beq___main___at_Lean_Occurrences_beq___spec__1(x_5, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
default: 
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_2, 0);
x_11 = l_List_beq___main___at_Lean_Occurrences_beq___spec__1(x_9, x_10);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
}
}
lean_object* l_List_beq___main___at_Lean_Occurrences_beq___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___main___at_Lean_Occurrences_beq___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Occurrences_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Occurrences_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Occurrences_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Occurrences_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Occurrences_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Occurrences_HasBeq___closed__1;
return x_1;
}
}
lean_object* initialize_Init_Data_Nat(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Data_Occurrences(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Occurrences_Inhabited = _init_l_Lean_Occurrences_Inhabited();
lean_mark_persistent(l_Lean_Occurrences_Inhabited);
l_Lean_Occurrences_HasBeq___closed__1 = _init_l_Lean_Occurrences_HasBeq___closed__1();
lean_mark_persistent(l_Lean_Occurrences_HasBeq___closed__1);
l_Lean_Occurrences_HasBeq = _init_l_Lean_Occurrences_HasBeq();
lean_mark_persistent(l_Lean_Occurrences_HasBeq);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
