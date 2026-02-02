// Lean compiler output
// Module: Init.Data.Order.Opposite
// Imports: public import Init.Data.Order.ClassesExtra public import Init.Data.Order.LemmasExtra
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
LEAN_EXPORT lean_object* l_LE_opposite(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LT_opposite(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Min_oppositeMax___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Min_oppositeMax___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Min_oppositeMax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Max_oppositeMin___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Max_oppositeMin___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Max_oppositeMin(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_OppositeOrderInstances_instDecidableLEOpposite___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instDecidableLEOpposite___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_OppositeOrderInstances_instDecidableLEOpposite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instDecidableLEOpposite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_OppositeOrderInstances_instDecidableLTOpposite___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instDecidableLTOpposite___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_OppositeOrderInstances_instDecidableLTOpposite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instDecidableLTOpposite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instLETransOpposite(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LE_opposite(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LT_opposite(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Min_oppositeMax___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Min_oppositeMax___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Min_oppositeMax___redArg___lam__0), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Min_oppositeMax(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Min_oppositeMax___redArg___lam__0), 3, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Max_oppositeMin___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Max_oppositeMin___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Max_oppositeMin___redArg___lam__0), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Max_oppositeMin(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Max_oppositeMin___redArg___lam__0), 3, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_OppositeOrderInstances_instDecidableLEOpposite___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_1, x_3, x_2);
x_5 = lean_unbox(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instDecidableLEOpposite___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_OppositeOrderInstances_instDecidableLEOpposite___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_OppositeOrderInstances_instDecidableLEOpposite(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_apply_2(x_3, x_5, x_4);
x_7 = lean_unbox(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instDecidableLEOpposite___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_OppositeOrderInstances_instDecidableLEOpposite(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Std_OppositeOrderInstances_instDecidableLTOpposite___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_1, x_3, x_2);
x_5 = lean_unbox(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instDecidableLTOpposite___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_OppositeOrderInstances_instDecidableLTOpposite___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_OppositeOrderInstances_instDecidableLTOpposite(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_apply_2(x_3, x_5, x_4);
x_7 = lean_unbox(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instDecidableLTOpposite___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_OppositeOrderInstances_instDecidableLTOpposite(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_OppositeOrderInstances_instLETransOpposite(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
return lean_box(0);
}
}
lean_object* initialize_Init_Data_Order_ClassesExtra(uint8_t builtin);
lean_object* initialize_Init_Data_Order_LemmasExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Order_Opposite(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_ClassesExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_LemmasExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
