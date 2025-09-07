// Lean compiler output
// Module: Lake.CLI
// Imports: Lake.CLI.Actions Lake.CLI.Build Lake.CLI.Error Lake.CLI.Help Lake.CLI.Init Lake.CLI.Main Lake.CLI.Serve Lake.CLI.Translate Lake.CLI.Translate.Lean Lake.CLI.Translate.Toml
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
lean_object* initialize_Lake_CLI_Actions(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_CLI_Build(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_CLI_Error(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_CLI_Help(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_CLI_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_CLI_Main(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_CLI_Serve(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_CLI_Translate(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_CLI_Translate_Lean(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_CLI_Translate_Toml(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_CLI_Actions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Build(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Error(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Help(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Serve(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Translate(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Translate_Lean(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Translate_Toml(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
