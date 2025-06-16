// Lean compiler output
// Module: Init.Data.Zero
// Imports: Init.Core
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
LEAN_EXPORT lean_object* l_Zero_ofOfNat0___rarg(lean_object*);
LEAN_EXPORT lean_object* l_One_toOfNat1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Zero_ofOfNat0(lean_object*);
LEAN_EXPORT lean_object* l_One_ofOfNat1___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Zero_toOfNat0___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Zero_toOfNat0___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_One_ofOfNat1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_One_toOfNat1(lean_object*);
LEAN_EXPORT lean_object* l_Zero_toOfNat0(lean_object*);
LEAN_EXPORT lean_object* l_One_toOfNat1___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_One_ofOfNat1(lean_object*);
LEAN_EXPORT lean_object* l_Zero_ofOfNat0___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Zero_toOfNat0___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Zero_toOfNat0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Zero_toOfNat0___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Zero_toOfNat0___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Zero_toOfNat0___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Zero_ofOfNat0___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Zero_ofOfNat0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Zero_ofOfNat0___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Zero_ofOfNat0___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Zero_ofOfNat0___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_One_toOfNat1___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_One_toOfNat1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_One_toOfNat1___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_One_toOfNat1___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_One_toOfNat1___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_One_ofOfNat1___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_One_ofOfNat1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_One_ofOfNat1___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_One_ofOfNat1___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_One_ofOfNat1___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Core(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Zero(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
