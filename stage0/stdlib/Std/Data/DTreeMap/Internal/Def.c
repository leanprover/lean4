// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.Def
// Imports: Std.Classes.Ord
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_delta;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instInhabitedImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_ratio;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instInhabitedImpl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(1);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_delta() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(3u);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_ratio() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(2u);
return x_1;
}
}
lean_object* initialize_Std_Classes_Ord(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_Internal_Def(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Classes_Ord(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_DTreeMap_Internal_delta = _init_l_Std_DTreeMap_Internal_delta();
lean_mark_persistent(l_Std_DTreeMap_Internal_delta);
l_Std_DTreeMap_Internal_ratio = _init_l_Std_DTreeMap_Internal_ratio();
lean_mark_persistent(l_Std_DTreeMap_Internal_ratio);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
