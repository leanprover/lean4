// Lean compiler output
// Module: Std.Data.Iterators.Combinators.DropWhile
// Imports: Std.Data.Iterators.Combinators.Monadic.DropWhile
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
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_Intermediate_dropWhile___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_dropWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_Intermediate_dropWhile(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_dropWhile___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_Intermediate_dropWhile___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_dropWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_Intermediate_dropWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_Intermediate_dropWhile___redArg(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_Intermediate_dropWhile(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_Intermediate_dropWhile___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Std_Iterators_Iter_Intermediate_dropWhile___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_Intermediate_dropWhile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Std_Iterators_Iter_Intermediate_dropWhile(x_1, x_2, x_3, x_6, x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_dropWhile___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_dropWhile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_box(1);
x_6 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_6, 0, x_4);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_7);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_dropWhile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Iterators_Iter_dropWhile(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Combinators_DropWhile(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
