// Lean compiler output
// Module: Std.Do.SPred.Laws
// Imports: Std.Do.SPred.Notation
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
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransEntails___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransBientails___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransEntails(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransBientails(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransEntails(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransEntails___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Do_SPred_instTransEntails(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransBientails(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_instTransBientails___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Do_SPred_instTransBientails(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Std_Do_SPred_Notation(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Do_SPred_Laws(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Do_SPred_Notation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
