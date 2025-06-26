// Lean compiler output
// Module: Init.Data.BitVec
// Imports: Init.Data.BitVec.BasicAux Init.Data.BitVec.Basic Init.Data.BitVec.Bootstrap Init.Data.BitVec.Bitblast Init.Data.BitVec.Decidable Init.Data.BitVec.Lemmas Init.Data.BitVec.Folds
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
lean_object* initialize_Init_Data_BitVec_BasicAux(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_BitVec_Bitblast(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_BitVec_Decidable(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_BitVec_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_BitVec_Folds(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_BitVec(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_BitVec_BasicAux(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Bootstrap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Bitblast(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Decidable(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Folds(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
