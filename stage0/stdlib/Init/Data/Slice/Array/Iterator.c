// Lean compiler output
// Module: Init.Data.Slice.Array.Iterator
// Imports: Init.Core Init.Data.Slice.Array.Basic Init.Data.Iterators.Combinators.Attach Init.Data.Iterators.Combinators.FilterMap Init.Data.Range.Polymorphic.Basic Init.Data.Range.Polymorphic.Nat Init.Data.Range.Polymorphic.Iterators Init.Data.Slice.Operations
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
LEAN_EXPORT lean_object* l_instToIteratorSubarrayId___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToIteratorSubarrayId___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToIteratorSubarrayId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToIteratorSubarrayId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToIteratorSubarrayId___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
lean_inc(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instToIteratorSubarrayId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instToIteratorSubarrayId___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instToIteratorSubarrayId___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToIteratorSubarrayId___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToIteratorSubarrayId___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instToIteratorSubarrayId(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init_Core(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Slice_Array_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Iterators_Combinators_Attach(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Iterators_Combinators_FilterMap(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Slice_Operations(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Slice_Array_Iterator(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Array_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_Attach(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Nat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Operations(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
