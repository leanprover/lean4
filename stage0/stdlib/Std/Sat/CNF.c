// Lean compiler output
// Module: Std.Sat.CNF
// Imports: Std.Sat.CNF.Basic Std.Sat.CNF.Literal Std.Sat.CNF.Relabel Std.Sat.CNF.RelabelFin Std.Sat.CNF.Dimacs
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
lean_object* initialize_Std_Sat_CNF_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_CNF_Literal(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_CNF_Relabel(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_CNF_RelabelFin(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_CNF_Dimacs(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_CNF(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_CNF_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_Literal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_Relabel(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_RelabelFin(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_Dimacs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
