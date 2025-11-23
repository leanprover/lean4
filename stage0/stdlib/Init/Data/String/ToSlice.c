// Lean compiler output
// Module: Init.Data.String.ToSlice
// Imports: public import Init.Data.String.Defs
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
lean_object* l_String_toSlice(lean_object*);
static lean_object* l_String_instToSlice___closed__0;
LEAN_EXPORT lean_object* l_String_ToSlice_ctorIdx___boxed(lean_object*, lean_object*);
static lean_object* l_String_instToSliceSlice___closed__0;
lean_object* l_id___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instToSlice;
LEAN_EXPORT lean_object* l_String_instToSliceSlice;
LEAN_EXPORT lean_object* l_String_ToSlice_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_ToSlice_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_ToSlice_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_ToSlice_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_String_instToSliceSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_String_instToSliceSlice() {
_start:
{
lean_object* x_1; 
x_1 = l_String_instToSliceSlice___closed__0;
return x_1;
}
}
static lean_object* _init_l_String_instToSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_toSlice), 1, 0);
return x_1;
}
}
static lean_object* _init_l_String_instToSlice() {
_start:
{
lean_object* x_1; 
x_1 = l_String_instToSlice___closed__0;
return x_1;
}
}
lean_object* initialize_Init_Data_String_Defs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_ToSlice(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_instToSliceSlice___closed__0 = _init_l_String_instToSliceSlice___closed__0();
lean_mark_persistent(l_String_instToSliceSlice___closed__0);
l_String_instToSliceSlice = _init_l_String_instToSliceSlice();
lean_mark_persistent(l_String_instToSliceSlice);
l_String_instToSlice___closed__0 = _init_l_String_instToSlice___closed__0();
lean_mark_persistent(l_String_instToSlice___closed__0);
l_String_instToSlice = _init_l_String_instToSlice();
lean_mark_persistent(l_String_instToSlice);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
