// Lean compiler output
// Module: Std.Data.Iterators.Combinators.TakeWhile
// Imports: Std.Data.Iterators.Combinators.Monadic.TakeWhile
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
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_takeWhile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift___at_Std_Iterators_Iter_takeWhile___spec__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Iterators_PostconditionT_lift___at_Std_Iterators_Iter_takeWhile___spec__1(uint8_t);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_takeWhile___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_takeWhile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_takeWhile___rarg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Iterators_PostconditionT_lift___at_Std_Iterators_Iter_takeWhile___spec__1(uint8_t x_1) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_takeWhile___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_takeWhile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_Iterators_Iter_takeWhile___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_PostconditionT_lift___at_Std_Iterators_Iter_takeWhile___spec__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Std_Iterators_PostconditionT_lift___at_Std_Iterators_Iter_takeWhile___spec__1(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_takeWhile___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Iterators_Iter_takeWhile___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Iter_takeWhile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Iterators_Iter_takeWhile(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Combinators_TakeWhile(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
