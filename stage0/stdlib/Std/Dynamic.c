// Lean compiler output
// Module: Std.Dynamic
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
LEAN_EXPORT lean_object* l___private_Std_Dynamic_0__Std_Dynamic_mkImpl(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Dynamic_0__Std_Dynamic_get_x3fImpl___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Dynamic_0__Std_TypeName_typeNameImpl(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Dynamic_0__Std_TypeNameData(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Dynamic_0__Std_Dynamic_typeNameImpl(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Dynamic_0__Std_Dynamic_get_x3fImpl(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Dynamic_0__Std_TypeName_typeNameImpl___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_TypeName_mk___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Dynamic_0__Std_Dynamic_typeNameImpl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_TypeName_mk(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Dynamic_0__Std_Dynamic_get_x3fImpl___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TypeName_mk___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Dynamic_0__Std_Dynamic_mkImpl___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Dynamic_0__Std_TypeName_typeNameImpl___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Dynamic_0__Std_DynamicPointed;
static lean_object* l___private_Std_Dynamic_0__Std_DynamicPointed___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Dynamic_0__Std_TypeNameData(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_Std_TypeName_mk___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_TypeName_mk(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_TypeName_mk___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_TypeName_mk___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_TypeName_mk___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Dynamic_0__Std_TypeName_typeNameImpl___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Std_Dynamic_0__Std_TypeName_typeNameImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Dynamic_0__Std_TypeName_typeNameImpl___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Dynamic_0__Std_TypeName_typeNameImpl___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Std_Dynamic_0__Std_TypeName_typeNameImpl___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Std_Dynamic_0__Std_DynamicPointed___closed__1() {
_start:
{
return lean_box(0);
}
}
static lean_object* _init_l___private_Std_Dynamic_0__Std_DynamicPointed() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Std_Dynamic_0__Std_DynamicPointed___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Std_Dynamic_0__Std_Dynamic_typeNameImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Dynamic_0__Std_Dynamic_typeNameImpl___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Std_Dynamic_0__Std_Dynamic_typeNameImpl(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Dynamic_0__Std_Dynamic_get_x3fImpl___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_name_eq(x_3, x_2);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Dynamic_0__Std_Dynamic_get_x3fImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Dynamic_0__Std_Dynamic_get_x3fImpl___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Dynamic_0__Std_Dynamic_get_x3fImpl___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Dynamic_0__Std_Dynamic_get_x3fImpl___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Dynamic_0__Std_Dynamic_mkImpl___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Dynamic_0__Std_Dynamic_mkImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Dynamic_0__Std_Dynamic_mkImpl___rarg), 2, 0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Dynamic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Std_Dynamic_0__Std_DynamicPointed___closed__1 = _init_l___private_Std_Dynamic_0__Std_DynamicPointed___closed__1();
lean_mark_persistent(l___private_Std_Dynamic_0__Std_DynamicPointed___closed__1);
l___private_Std_Dynamic_0__Std_DynamicPointed = _init_l___private_Std_Dynamic_0__Std_DynamicPointed();
lean_mark_persistent(l___private_Std_Dynamic_0__Std_DynamicPointed);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
