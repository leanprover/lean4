// Lean compiler output
// Module: Lean.ToLevel
// Imports: Lean.Expr
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
LEAN_EXPORT lean_object* l_Lean_instToLevel;
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Level_max___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToLevel__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ToLevel_max(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ToLevel_imax(lean_object*, lean_object*);
lean_object* l_Lean_Level_imax___override(lean_object*, lean_object*);
static lean_object* _init_l_Lean_instToLevel() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instToLevel__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_succ___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ToLevel_max(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Level_max___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ToLevel_imax(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Level_imax___override(x_1, x_2);
return x_3;
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ToLevel(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instToLevel = _init_l_Lean_instToLevel();
lean_mark_persistent(l_Lean_instToLevel);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
