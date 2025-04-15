// Lean compiler output
// Module: Init.Data
// Imports: Init.Data.Basic Init.Data.Nat Init.Data.Bool Init.Data.BitVec Init.Data.Cast Init.Data.Char Init.Data.String Init.Data.List Init.Data.Int Init.Data.Array Init.Data.Array.Subarray.Split Init.Data.ByteArray Init.Data.FloatArray Init.Data.Fin Init.Data.UInt Init.Data.SInt Init.Data.Float Init.Data.Float32 Init.Data.Option Init.Data.Ord Init.Data.Random Init.Data.ToString Init.Data.Range Init.Data.Hashable Init.Data.OfScientific Init.Data.Format Init.Data.Stream Init.Data.Prod Init.Data.AC Init.Data.Queue Init.Data.Sum Init.Data.BEq Init.Data.Subtype Init.Data.ULift Init.Data.PLift Init.Data.Zero Init.Data.NeZero Init.Data.Function Init.Data.RArray Init.Data.Vector
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
lean_object* initialize_Init_Data_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Bool(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_BitVec(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Cast(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Char(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_String(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Subarray_Split(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ByteArray(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_FloatArray(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Fin(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_UInt(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_SInt(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Float(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Float32(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Option(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Ord(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Random(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ToString(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Range(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Hashable(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_OfScientific(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Format(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Stream(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Prod(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_AC(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Queue(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Sum(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_BEq(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Subtype(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ULift(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_PLift(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Zero(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_NeZero(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Function(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_RArray(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Vector(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Cast(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Subarray_Split(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_FloatArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Float(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Float32(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Random(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Hashable(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_OfScientific(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Stream(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Prod(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_AC(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Queue(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Sum(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BEq(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Subtype(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ULift(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_PLift(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Zero(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_NeZero(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Function(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_RArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
