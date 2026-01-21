// Lean compiler output
// Module: Lake.CLI
// Imports: public import Lake.CLI.Actions public import Lake.CLI.Build public import Lake.CLI.Error public import Lake.CLI.Help public import Lake.CLI.Init public import Lake.CLI.Main public import Lake.CLI.Serve public import Lake.CLI.Shake public import Lake.CLI.Translate public import Lake.CLI.Translate.Lean public import Lake.CLI.Translate.Toml
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
lean_object* initialize_Lake_CLI_Actions(uint8_t builtin);
lean_object* initialize_Lake_CLI_Build(uint8_t builtin);
lean_object* initialize_Lake_CLI_Error(uint8_t builtin);
lean_object* initialize_Lake_CLI_Help(uint8_t builtin);
lean_object* initialize_Lake_CLI_Init(uint8_t builtin);
lean_object* initialize_Lake_CLI_Main(uint8_t builtin);
lean_object* initialize_Lake_CLI_Serve(uint8_t builtin);
lean_object* initialize_Lake_CLI_Shake(uint8_t builtin);
lean_object* initialize_Lake_CLI_Translate(uint8_t builtin);
lean_object* initialize_Lake_CLI_Translate_Lean(uint8_t builtin);
lean_object* initialize_Lake_CLI_Translate_Toml(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_CLI_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Build(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Help(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Serve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Shake(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Translate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Translate_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Translate_Toml(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
