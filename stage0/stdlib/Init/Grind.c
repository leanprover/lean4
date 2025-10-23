// Lean compiler output
// Module: Init.Grind
// Imports: public import Init.Grind.Norm public import Init.Grind.Tactics public import Init.Grind.Lemmas public import Init.Grind.Cases public import Init.Grind.Propagator public import Init.Grind.Util public import Init.Grind.Offset public import Init.Grind.PP public import Init.Grind.Ring public import Init.Grind.Module public import Init.Grind.Ordered public import Init.Grind.Ext public import Init.Grind.ToInt public import Init.Grind.ToIntLemmas public import Init.Grind.Attr public import Init.Data.Int.OfNat public import Init.Grind.AC public import Init.Grind.Injective public import Init.Grind.Order public import Init.Grind.Interactive
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
lean_object* initialize_Init_Grind_Norm(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Cases(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Propagator(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Offset(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_PP(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Ring(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Module(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Ordered(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Ext(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_ToInt(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_ToIntLemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Attr(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_AC(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Injective(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Order(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Interactive(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Norm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Tactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Cases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Propagator(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Offset(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_PP(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Module(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ordered(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_ToInt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_ToIntLemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Attr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_OfNat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_AC(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Injective(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Order(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Interactive(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
