// Lean compiler output
// Module: Lake.Util.Opaque
// Imports: Init.Prelude
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
LEAN_EXPORT lean_object* l_POpaque_cast___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_POpaque_castTo(lean_object*);
LEAN_EXPORT lean_object* l_POpaque_mk_unsafe__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_POpaque_mk___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Opaque_0__POpaque_nonemptyType;
LEAN_EXPORT lean_object* l_POpaque_mk(lean_object*);
LEAN_EXPORT lean_object* l_Opaque_mk___rarg(lean_object*);
LEAN_EXPORT lean_object* l_POpaque_mk_unsafe__1___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_POpaque_cast(lean_object*);
LEAN_EXPORT lean_object* l_POpaque_mk_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l_POpaque_cast___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Opaque_mk(lean_object*);
LEAN_EXPORT lean_object* l_POpaque_castTo___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_POpaque_castTo___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Opaque_mk___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_POpaque_mk___rarg___boxed(lean_object*);
static lean_object* _init_l___private_Lake_Util_Opaque_0__POpaque_nonemptyType() {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_POpaque_mk_unsafe__1___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_POpaque_mk_unsafe__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_POpaque_mk_unsafe__1___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_POpaque_mk_unsafe__1___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_POpaque_mk_unsafe__1___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_POpaque_mk___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_POpaque_mk(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_POpaque_mk___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_POpaque_mk___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_POpaque_mk___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Opaque_mk___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Opaque_mk(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Opaque_mk___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Opaque_mk___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Opaque_mk___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_POpaque_cast___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_POpaque_cast(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_POpaque_cast___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_POpaque_cast___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_POpaque_cast___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_POpaque_castTo___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_POpaque_castTo(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_POpaque_castTo___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_POpaque_castTo___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_POpaque_castTo___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Prelude(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Opaque(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lake_Util_Opaque_0__POpaque_nonemptyType = _init_l___private_Lake_Util_Opaque_0__POpaque_nonemptyType();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
