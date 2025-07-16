// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Stream
// Imports: Init.Data.Range.Polymorphic.Iterators Init.Data.Stream
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
LEAN_EXPORT lean_object* l_Std_PRange_instToStreamMkIterRangeIteratorOfUpwardEnumerableOfBoundedUpwardEnumerable(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instToStreamMkIterRangeIteratorOfUpwardEnumerableOfBoundedUpwardEnumerable___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instToStreamMkIterRangeIteratorOfUpwardEnumerableOfBoundedUpwardEnumerable___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instToStreamMkIterRangeIteratorOfUpwardEnumerableOfBoundedUpwardEnumerable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instToStreamMkIterRangeIteratorOfUpwardEnumerableOfBoundedUpwardEnumerable___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_apply_1(x_1, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instToStreamMkIterRangeIteratorOfUpwardEnumerableOfBoundedUpwardEnumerable___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PRange_instToStreamMkIterRangeIteratorOfUpwardEnumerableOfBoundedUpwardEnumerable___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instToStreamMkIterRangeIteratorOfUpwardEnumerableOfBoundedUpwardEnumerable(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PRange_instToStreamMkIterRangeIteratorOfUpwardEnumerableOfBoundedUpwardEnumerable___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instToStreamMkIterRangeIteratorOfUpwardEnumerableOfBoundedUpwardEnumerable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox(x_2);
x_8 = l_Std_PRange_instToStreamMkIterRangeIteratorOfUpwardEnumerableOfBoundedUpwardEnumerable(x_6, x_7, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_8;
}
}
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Stream(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_Stream(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Stream(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
