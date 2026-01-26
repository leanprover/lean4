// Lean compiler output
// Module: Lean.Server.Test.Refs
// Imports: import Init.Prelude
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
LEAN_EXPORT lean_object* l_Lean_Server_Test_Refs_test7;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Refs_test8;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Refs_test9;
LEAN_EXPORT lean_object* l_Lean_Server_Test_Refs_test10;
static lean_object* _init_l_Lean_Server_Test_Refs_test7() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Test_Refs_test8() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Test_Refs_test9() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Test_Refs_test10() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* initialize_Init_Prelude(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Test_Refs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_Test_Refs_test7 = _init_l_Lean_Server_Test_Refs_test7();
lean_mark_persistent(l_Lean_Server_Test_Refs_test7);
l_Lean_Server_Test_Refs_test8 = _init_l_Lean_Server_Test_Refs_test8();
lean_mark_persistent(l_Lean_Server_Test_Refs_test8);
l_Lean_Server_Test_Refs_test9 = _init_l_Lean_Server_Test_Refs_test9();
lean_mark_persistent(l_Lean_Server_Test_Refs_test9);
l_Lean_Server_Test_Refs_test10 = _init_l_Lean_Server_Test_Refs_test10();
lean_mark_persistent(l_Lean_Server_Test_Refs_test10);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
