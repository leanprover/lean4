// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Char
// Imports: public import Init.Data.Char.Ordinal public import Init.Data.Range.Polymorphic.Fin import Init.Data.Range.Polymorphic.Lemmas import Init.Data.Range.Polymorphic.Map import Init.Data.Char.Order
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
LEAN_EXPORT lean_object* l_Char_instLeast_x3f___closed__0___boxed__const__1;
LEAN_EXPORT lean_object* l_Char_instHasSize___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Char_ordinal(uint32_t);
LEAN_EXPORT lean_object* l_Char_instHasSize;
LEAN_EXPORT lean_object* l_Char_instHasSize__1;
LEAN_EXPORT lean_object* l_Char_instHasSize__1___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Char_instUpwardEnumerable___closed__0;
static lean_object* l_Char_instHasSize__2___closed__0;
static lean_object* l___private_Init_Data_Range_Polymorphic_Char_0__Char_map___closed__0;
static lean_object* l_Char_instLeast_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Char_0__Char_map;
static lean_object* l_Char_instHasSize___closed__0;
static lean_object* l_Char_instUpwardEnumerable___closed__1;
LEAN_EXPORT lean_object* l_Char_instLeast_x3f;
lean_object* l_Char_succMany_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_instHasSize__2;
static lean_object* l_Char_instUpwardEnumerable___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Char_instHasSize__2___lam__0(uint32_t);
lean_object* l_Char_ordinal___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Char_instHasSize__1___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Char_instHasSize___lam__0(uint32_t, uint32_t);
static lean_object* l_Char_instHasSize__1___closed__0;
LEAN_EXPORT lean_object* l_Char_instHasSize__2___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Char_instUpwardEnumerable;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Char_succ_x3f___boxed(lean_object*);
static lean_object* _init_l_Char_instUpwardEnumerable___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Char_succ_x3f___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Char_instUpwardEnumerable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Char_succMany_x3f___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Char_instUpwardEnumerable___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_instUpwardEnumerable___closed__1;
x_2 = l_Char_instUpwardEnumerable___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Char_instUpwardEnumerable() {
_start:
{
lean_object* x_1; 
x_1 = l_Char_instUpwardEnumerable___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Char_instHasSize___lam__0(uint32_t x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Char_ordinal(x_1);
x_4 = l_Char_ordinal(x_2);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_4);
x_7 = lean_nat_sub(x_6, x_3);
lean_dec(x_3);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Char_instHasSize___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Char_instHasSize___lam__0(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Char_instHasSize___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Char_instHasSize___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Char_instHasSize() {
_start:
{
lean_object* x_1; 
x_1 = l_Char_instHasSize___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Char_instHasSize__1___lam__0(uint32_t x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_Char_ordinal(x_1);
x_4 = l_Char_ordinal(x_2);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_4);
x_7 = lean_nat_sub(x_6, x_3);
lean_dec(x_3);
lean_dec(x_6);
x_8 = lean_nat_sub(x_7, x_5);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Char_instHasSize__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Char_instHasSize__1___lam__0(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Char_instHasSize__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Char_instHasSize__1___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Char_instHasSize__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Char_instHasSize__1___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Char_instHasSize__2___lam__0(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1112064u);
x_3 = l_Char_ordinal(x_1);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Char_instHasSize__2___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Char_instHasSize__2___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_Char_instHasSize__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Char_instHasSize__2___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Char_instHasSize__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Char_instHasSize__2___closed__0;
return x_1;
}
}
static lean_object* _init_l_Char_instLeast_x3f___closed__0___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Char_instLeast_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Char_instLeast_x3f___closed__0___boxed__const__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Char_instLeast_x3f() {
_start:
{
lean_object* x_1; 
x_1 = l_Char_instLeast_x3f___closed__0;
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_Char_0__Char_map___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Char_ordinal___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_Char_0__Char_map() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Init_Data_Range_Polymorphic_Char_0__Char_map___closed__0;
return x_1;
}
}
lean_object* initialize_Init_Data_Char_Ordinal(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Fin(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Map(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Order(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_Char(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Char_Ordinal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Fin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Map(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Char_instUpwardEnumerable___closed__0 = _init_l_Char_instUpwardEnumerable___closed__0();
lean_mark_persistent(l_Char_instUpwardEnumerable___closed__0);
l_Char_instUpwardEnumerable___closed__1 = _init_l_Char_instUpwardEnumerable___closed__1();
lean_mark_persistent(l_Char_instUpwardEnumerable___closed__1);
l_Char_instUpwardEnumerable___closed__2 = _init_l_Char_instUpwardEnumerable___closed__2();
lean_mark_persistent(l_Char_instUpwardEnumerable___closed__2);
l_Char_instUpwardEnumerable = _init_l_Char_instUpwardEnumerable();
lean_mark_persistent(l_Char_instUpwardEnumerable);
l_Char_instHasSize___closed__0 = _init_l_Char_instHasSize___closed__0();
lean_mark_persistent(l_Char_instHasSize___closed__0);
l_Char_instHasSize = _init_l_Char_instHasSize();
lean_mark_persistent(l_Char_instHasSize);
l_Char_instHasSize__1___closed__0 = _init_l_Char_instHasSize__1___closed__0();
lean_mark_persistent(l_Char_instHasSize__1___closed__0);
l_Char_instHasSize__1 = _init_l_Char_instHasSize__1();
lean_mark_persistent(l_Char_instHasSize__1);
l_Char_instHasSize__2___closed__0 = _init_l_Char_instHasSize__2___closed__0();
lean_mark_persistent(l_Char_instHasSize__2___closed__0);
l_Char_instHasSize__2 = _init_l_Char_instHasSize__2();
lean_mark_persistent(l_Char_instHasSize__2);
l_Char_instLeast_x3f___closed__0___boxed__const__1 = _init_l_Char_instLeast_x3f___closed__0___boxed__const__1();
lean_mark_persistent(l_Char_instLeast_x3f___closed__0___boxed__const__1);
l_Char_instLeast_x3f___closed__0 = _init_l_Char_instLeast_x3f___closed__0();
lean_mark_persistent(l_Char_instLeast_x3f___closed__0);
l_Char_instLeast_x3f = _init_l_Char_instLeast_x3f();
lean_mark_persistent(l_Char_instLeast_x3f);
l___private_Init_Data_Range_Polymorphic_Char_0__Char_map___closed__0 = _init_l___private_Init_Data_Range_Polymorphic_Char_0__Char_map___closed__0();
lean_mark_persistent(l___private_Init_Data_Range_Polymorphic_Char_0__Char_map___closed__0);
l___private_Init_Data_Range_Polymorphic_Char_0__Char_map = _init_l___private_Init_Data_Range_Polymorphic_Char_0__Char_map();
lean_mark_persistent(l___private_Init_Data_Range_Polymorphic_Char_0__Char_map);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
