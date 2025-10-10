// Lean compiler output
// Module: Init.Data.Order
// Imports: public import Init.Data.Order.Ord public import Init.Data.Order.Classes public import Init.Data.Order.ClassesExtra public import Init.Data.Order.Lemmas public import Init.Data.Order.LemmasExtra public import Init.Data.Order.Factories public import Init.Data.Order.FactoriesExtra public import Init.Data.Order.PackageFactories
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
lean_object* initialize_Init_Data_Order_Ord(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Order_Classes(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Order_ClassesExtra(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Order_LemmasExtra(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Order_Factories(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Order_FactoriesExtra(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Order_PackageFactories(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Order(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_Ord(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Classes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_ClassesExtra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_LemmasExtra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Factories(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_FactoriesExtra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_PackageFactories(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
