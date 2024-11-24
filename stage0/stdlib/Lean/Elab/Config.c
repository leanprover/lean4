// Lean compiler output
// Module: Lean.Elab.Config
// Imports: Lean.Meta.Basic
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_setElabConfig(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_setElabConfig(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
uint8_t x_3; uint8_t x_4; 
x_3 = 1;
x_4 = 0;
lean_ctor_set_uint8(x_1, 0, x_3);
lean_ctor_set_uint8(x_1, 1, x_3);
lean_ctor_set_uint8(x_1, 2, x_4);
lean_ctor_set_uint8(x_1, 3, x_4);
return x_1;
}
else
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_5 = lean_ctor_get_uint8(x_1, 4);
x_6 = lean_ctor_get_uint8(x_1, 5);
x_7 = lean_ctor_get_uint8(x_1, 6);
x_8 = lean_ctor_get_uint8(x_1, 7);
x_9 = lean_ctor_get_uint8(x_1, 8);
x_10 = lean_ctor_get_uint8(x_1, 9);
x_11 = lean_ctor_get_uint8(x_1, 10);
x_12 = lean_ctor_get_uint8(x_1, 11);
x_13 = lean_ctor_get_uint8(x_1, 12);
x_14 = lean_ctor_get_uint8(x_1, 13);
x_15 = lean_ctor_get_uint8(x_1, 14);
x_16 = lean_ctor_get_uint8(x_1, 15);
x_17 = lean_ctor_get_uint8(x_1, 16);
x_18 = lean_ctor_get_uint8(x_1, 17);
lean_dec(x_1);
x_19 = 1;
x_20 = 0;
x_21 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, 1, x_19);
lean_ctor_set_uint8(x_21, 2, x_20);
lean_ctor_set_uint8(x_21, 3, x_20);
lean_ctor_set_uint8(x_21, 4, x_5);
lean_ctor_set_uint8(x_21, 5, x_6);
lean_ctor_set_uint8(x_21, 6, x_7);
lean_ctor_set_uint8(x_21, 7, x_8);
lean_ctor_set_uint8(x_21, 8, x_9);
lean_ctor_set_uint8(x_21, 9, x_10);
lean_ctor_set_uint8(x_21, 10, x_11);
lean_ctor_set_uint8(x_21, 11, x_12);
lean_ctor_set_uint8(x_21, 12, x_13);
lean_ctor_set_uint8(x_21, 13, x_14);
lean_ctor_set_uint8(x_21, 14, x_15);
lean_ctor_set_uint8(x_21, 15, x_16);
lean_ctor_set_uint8(x_21, 16, x_17);
lean_ctor_set_uint8(x_21, 17, x_18);
return x_21;
}
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Config(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
