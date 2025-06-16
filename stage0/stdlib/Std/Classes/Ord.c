// Lean compiler output
// Module: Std.Classes.Ord
// Imports: Std.Classes.Ord.Basic Std.Classes.Ord.SInt Std.Classes.Ord.UInt Std.Classes.Ord.String Std.Classes.Ord.BitVec Std.Classes.Ord.Vector
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
lean_object* initialize_Std_Classes_Ord_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Classes_Ord_SInt(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Classes_Ord_UInt(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Classes_Ord_String(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Classes_Ord_BitVec(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Classes_Ord_Vector(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Classes_Ord(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Classes_Ord_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Classes_Ord_SInt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Classes_Ord_UInt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Classes_Ord_String(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Classes_Ord_BitVec(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Classes_Ord_Vector(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
