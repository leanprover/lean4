// Lean compiler output
// Module: Lake.Util
// Imports: public import Lake.Util.Binder public import Lake.Util.Casing public import Lake.Util.Cli public import Lake.Util.Cycle public import Lake.Util.Date public import Lake.Util.EquipT public import Lake.Util.Error public import Lake.Util.EStateT public import Lake.Util.Exit public import Lake.Util.Family public import Lake.Util.FilePath public import Lake.Util.Git public import Lake.Util.IO public import Lake.Util.JsonObject public import Lake.Util.Lift public import Lake.Util.Lock public import Lake.Util.Log public import Lake.Util.MainM public import Lake.Util.Message public import Lake.Util.Name public import Lake.Util.NativeLib public import Lake.Util.Opaque public import Lake.Util.OrderedTagAttribute public import Lake.Util.OrdHashSet public import Lake.Util.Proc public import Lake.Util.RBArray public import Lake.Util.Reservoir public import Lake.Util.Store public import Lake.Util.StoreInsts public import Lake.Util.String public import Lake.Util.Task public import Lake.Util.Url public import Lake.Util.Version
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
lean_object* initialize_Lake_Util_Binder(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Casing(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Cli(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Cycle(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Date(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_EquipT(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Error(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_EStateT(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Exit(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Family(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_FilePath(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Git(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_JsonObject(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Lift(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Lock(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_MainM(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Message(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Name(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_NativeLib(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Opaque(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_OrderedTagAttribute(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_OrdHashSet(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_RBArray(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Reservoir(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Store(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_StoreInsts(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_String(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Task(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Url(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Version(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Binder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Casing(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Cli(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Cycle(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Date(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_EquipT(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Error(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_EStateT(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Exit(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Family(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_FilePath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Git(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_JsonObject(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Lift(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Lock(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_MainM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Message(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Name(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_NativeLib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Opaque(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_OrderedTagAttribute(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_OrdHashSet(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Proc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_RBArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Reservoir(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Store(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_StoreInsts(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_String(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Task(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Url(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Version(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
