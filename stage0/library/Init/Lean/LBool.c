// Lean compiler output
// Module: Init.Lean.LBool
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
uint8_t l_Lean_LBool_Inhabited;
lean_object* l_Lean_LBool_HasToString;
lean_object* l_Lean_LBool_toString(uint8_t);
lean_object* l_Lean_LBool_HasBeq;
lean_object* l_Lean_LBool_HasBeq___closed__1;
lean_object* l_Lean_LBool_toString___boxed(lean_object*);
uint8_t l_Lean_LBool_and(uint8_t, uint8_t);
lean_object* l_Lean_LBool_neg___boxed(lean_object*);
lean_object* l_Bool_toLBool___boxed(lean_object*);
lean_object* l_Lean_LBool_and___boxed(lean_object*, lean_object*);
extern lean_object* l_Bool_HasRepr___closed__1;
extern lean_object* l_Bool_HasRepr___closed__2;
uint8_t l_Lean_LBool_neg(uint8_t);
uint8_t l_Bool_toLBool(uint8_t);
lean_object* l_Lean_LBool_toString___closed__1;
uint8_t l_Lean_LBool_beq(uint8_t, uint8_t);
lean_object* l_Lean_LBool_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LBool_HasToString___closed__1;
uint8_t _init_l_Lean_LBool_Inhabited() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
uint8_t l_Lean_LBool_neg(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 1:
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
default: 
{
return x_1;
}
}
}
}
lean_object* l_Lean_LBool_neg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_LBool_neg(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_LBool_and(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(x_1);
if (lean_obj_tag(x_3) == 1)
{
return x_2;
}
else
{
lean_dec(x_3);
return x_1;
}
}
}
lean_object* l_Lean_LBool_and___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_LBool_and(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_Lean_LBool_beq(uint8_t x_1, uint8_t x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; 
x_3 = lean_box(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
}
case 1:
{
lean_object* x_6; 
x_6 = lean_box(x_2);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 0;
return x_8;
}
}
default: 
{
lean_object* x_9; 
x_9 = lean_box(x_2);
if (lean_obj_tag(x_9) == 2)
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = 0;
return x_11;
}
}
}
}
}
lean_object* l_Lean_LBool_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_LBool_beq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* _init_l_Lean_LBool_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_LBool_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_LBool_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LBool_HasBeq___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_LBool_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("undef");
return x_1;
}
}
lean_object* l_Lean_LBool_toString(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_Bool_HasRepr___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Bool_HasRepr___closed__2;
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = l_Lean_LBool_toString___closed__1;
return x_4;
}
}
}
}
lean_object* l_Lean_LBool_toString___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_LBool_toString(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_LBool_HasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_LBool_toString___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_LBool_HasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LBool_HasToString___closed__1;
return x_1;
}
}
uint8_t l_Bool_toLBool(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
lean_object* l_Bool_toLBool___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Bool_toLBool(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init_Data_ToString(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_LBool(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_LBool_Inhabited = _init_l_Lean_LBool_Inhabited();
l_Lean_LBool_HasBeq___closed__1 = _init_l_Lean_LBool_HasBeq___closed__1();
lean_mark_persistent(l_Lean_LBool_HasBeq___closed__1);
l_Lean_LBool_HasBeq = _init_l_Lean_LBool_HasBeq();
lean_mark_persistent(l_Lean_LBool_HasBeq);
l_Lean_LBool_toString___closed__1 = _init_l_Lean_LBool_toString___closed__1();
lean_mark_persistent(l_Lean_LBool_toString___closed__1);
l_Lean_LBool_HasToString___closed__1 = _init_l_Lean_LBool_HasToString___closed__1();
lean_mark_persistent(l_Lean_LBool_HasToString___closed__1);
l_Lean_LBool_HasToString = _init_l_Lean_LBool_HasToString();
lean_mark_persistent(l_Lean_LBool_HasToString);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
