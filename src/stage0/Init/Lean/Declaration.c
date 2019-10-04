// Lean compiler output
// Module: Init.Lean.Declaration
// Imports: Init.Lean.Expr
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
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Task_get(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name___boxed(lean_object*);
lean_object* l_Lean_ConstantInfo_toConstantVal(lean_object*);
lean_object* l_Lean_ConstantInfo_value___boxed(lean_object*);
lean_object* l_Lean_ConstantInfo_value(lean_object*);
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l_Lean_ConstantInfo_instantiateTypeUnivParams___boxed(lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*);
lean_object* l_Lean_ConstantInfo_hints___boxed(lean_object*);
lean_object* lean_instantiate_type_lparams(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_instantiateValueUnivParams___boxed(lean_object*, lean_object*);
lean_object* lean_instantiate_value_lparams(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_hints(lean_object*);
lean_object* l_Lean_ConstantInfo_toConstantVal___boxed(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_ConstantInfo_type___boxed(lean_object*);
lean_object* l_Lean_ConstantInfo_lparams___boxed(lean_object*);
lean_object* l_Lean_ConstantInfo_hasValue___boxed(lean_object*);
lean_object* l_Lean_ConstantInfo_toConstantVal(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
lean_object* l_Lean_ConstantInfo_toConstantVal___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ConstantInfo_toConstantVal(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_ConstantInfo_name(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_ConstantInfo_toConstantVal(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_ConstantInfo_name___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ConstantInfo_name(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_ConstantInfo_lparams(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_ConstantInfo_toConstantVal(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_ConstantInfo_lparams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ConstantInfo_lparams(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_ConstantInfo_type(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_ConstantInfo_toConstantVal(x_1);
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_ConstantInfo_type___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ConstantInfo_type(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_ConstantInfo_value(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
case 2:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_5, 1);
x_7 = lean_task_get(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
default: 
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
}
}
}
lean_object* l_Lean_ConstantInfo_value___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ConstantInfo_value(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_ConstantInfo_hasValue(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 2:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
default: 
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
}
lean_object* l_Lean_ConstantInfo_hasValue___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_ConstantInfo_hasValue(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_ConstantInfo_hints(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
}
lean_object* l_Lean_ConstantInfo_hints___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ConstantInfo_hints(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_ConstantInfo_instantiateTypeUnivParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_instantiate_type_lparams(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_ConstantInfo_instantiateValueUnivParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_instantiate_value_lparams(x_1, x_2);
return x_3;
}
}
lean_object* initialize_Init_Lean_Expr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Declaration(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Expr(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif
