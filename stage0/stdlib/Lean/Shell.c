// Lean compiler output
// Module: Lean.Shell
// Imports: Lean.Elab.Frontend Lean.Elab.ParseImportsFast Lean.Server.Watchdog Lean.Server.FileWorker Lean.Compiler.IR.EmitC
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
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__5____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__1;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__2;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__11;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__13____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
uint8_t lean_internal_is_debug(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__10;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initLLVM___boxed(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__0;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__0____x40_Lean_Shell_1197438456____hygCtx___hyg_2_;
extern lean_object* l_Lean_githash;
LEAN_EXPORT lean_object* l_IO_println___at_____private_Lean_Shell_0__Lean_displayHeader_spec__0(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__29;
lean_object* lean_internal_set_max_heartbeat(size_t, lean_object*);
lean_object* lean_decode_lossy_utf8(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__2____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__6;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__0____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__2;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__9____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__15;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__5;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__9;
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__5;
lean_object* l_Lean_Elab_printImports(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__8;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__40;
size_t lean_usize_mul(size_t, size_t);
static uint8_t l___private_Lean_Shell_0__Lean_shortVersionString___closed__2;
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__6;
lean_object* l_Lean_KVMap_find(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_lines(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__30;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__1;
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at_____private_Lean_Shell_0__Lean_shellMain_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__21;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__38;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultMaxHeartbeat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at_____private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_emitLLVM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__3;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__11;
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__9;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__25;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__26;
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__7;
lean_object* l_Lean_moduleNameOfFileName(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__10;
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHelp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultMaxMemory___boxed(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Server_FileWorker_workerMain(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__6;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__23;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__13;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__0;
extern uint8_t l_Lean_version_isRelease;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__27;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__16;
lean_object* lean_get_stdout(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at_____private_Lean_Shell_0__Lean_shellMain_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_display_header(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object**);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__18;
size_t lean_usize_of_nat(lean_object*);
static uint8_t l___private_Lean_Shell_0__Lean_versionHeader___closed__10;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__20;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_decodeLossyUTF8___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__8;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__15;
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at_____private_Lean_Shell_0__Lean_shellMain_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_maxMemory;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__13;
static uint8_t l___private_Lean_Shell_0__Lean_displayHelp___closed__36;
LEAN_EXPORT lean_object* l_IO_print___at___IO_println___at_____private_Lean_Shell_0__Lean_displayHeader_spec__0_spec__0(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readBinToEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_1197438456____hygCtx___hyg_2_(lean_object*);
static uint8_t l___private_Lean_Shell_0__Lean_versionHeader___closed__5;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__12;
lean_object* lean_emit_llvm(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__3____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__5;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__4;
lean_object* l_Lean_Elab_printImportSrcs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_watchdogMain(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_isDebug___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at_____private_Lean_Shell_0__Lean_shellMain_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__19;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__7;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__12____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__0;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__1____x40_Lean_Shell_1197438456____hygCtx___hyg_2_;
lean_object* lean_get_stdin(lean_object*);
static uint8_t l___private_Lean_Shell_0__Lean_displayHelp___closed__12;
lean_object* l_String_posOfAux(lean_object*, uint32_t, lean_object*, lean_object*);
lean_object* lean_get_stderr(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
static uint8_t l___private_Lean_Shell_0__Lean_versionHeader___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_3125322801____hygCtx___hyg_2_(lean_object*);
static uint8_t l___private_Lean_Shell_0__Lean_versionHeader___closed__9;
lean_object* lean_internal_get_default_max_heartbeat(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(uint8_t);
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__7____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__9;
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getBuildType___boxed(lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__3____x40_Lean_Shell_1197438456____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__34;
lean_object* l_Lean_ModuleSetup_load(lean_object*, lean_object*);
lean_object* lean_internal_set_max_memory(size_t, lean_object*);
lean_object* lean_internal_get_build_type(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_hasAddressSanitizer___boxed(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__7;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__37;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__17;
lean_object* lean_internal_get_default_max_memory(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__4____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__11;
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_runMain___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayCumulativeProfilingTimes___boxed(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__14;
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_runFrontend(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__16;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__10;
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at_____private_Lean_Shell_0__Lean_shellMain_spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__7;
LEAN_EXPORT lean_object* l_IO_println___at_____private_Lean_Shell_0__Lean_shellMain_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_noConfusion___redArg___lam__0___boxed(lean_object*);
lean_object* l_Lean_getBuildDir(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__35;
static uint8_t l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_noConfusion___redArg___lam__0(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at_____private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__4;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_shell_main(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* lean_run_main(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_timeout;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__24;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__3;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__3;
lean_object* lean_init_llvm(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__4____x40_Lean_Shell_1197438456____hygCtx___hyg_2_;
lean_object* lean_string_to_utf8(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setMaxHeartbeat___boxed(lean_object*, lean_object*);
lean_object* lean_io_exit(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lean_display_help(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_noConfusion___redArg___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__8____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
uint8_t l_instDecidableNot___redArg(uint8_t);
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__10____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
extern lean_object* l_Lean_versionStringCore;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__22;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_isMultiThread___boxed(lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__28;
uint8_t l_Substring_beq(lean_object*, lean_object*);
lean_object* lean_display_cumulative_profiling_times(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_noConfusion___redArg(uint8_t, uint8_t);
uint8_t lean_internal_has_address_sanitizer(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at_____private_Lean_Shell_0__Lean_shellMain_spec__5___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__0;
static uint8_t l___private_Lean_Shell_0__Lean_shortVersionString___closed__4;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__1;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__1;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__11____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString;
lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__33;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__2____x40_Lean_Shell_1197438456____hygCtx___hyg_2_;
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_internal_is_multi_thread(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__32;
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at_____private_Lean_Shell_0__Lean_shellMain_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at_____private_Lean_Shell_0__Lean_shellMain_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__6____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__2;
extern lean_object* l_System_Platform_target;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__14;
lean_object* l_Lean_getLibDir(lean_object*, lean_object*);
extern lean_object* l_Lean_version_specialDesc;
lean_object* l_Lean_printImportsJson(lean_object*, lean_object*);
static uint8_t l___private_Lean_Shell_0__Lean_shortVersionString___closed__3;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__4;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__39;
LEAN_EXPORT lean_object* l_IO_eprint___at___IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1_spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__31;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__8;
lean_object* lean_ir_emit_c(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setMaxMemory___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__1____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_decodeLossyUTF8___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_decode_lossy_utf8(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_runMain___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_run_main(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initLLVM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_init_llvm(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_emitLLVM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_emit_llvm(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayCumulativeProfilingTimes___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_display_cumulative_profiling_times(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_hasAddressSanitizer___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_internal_has_address_sanitizer(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_isMultiThread___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_internal_is_multi_thread(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_isDebug___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_internal_is_debug(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getBuildType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_internal_get_build_type(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultMaxMemory___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_internal_get_default_max_memory(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setMaxMemory___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_internal_set_max_memory(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultMaxHeartbeat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_internal_get_default_max_heartbeat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setMaxHeartbeat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_internal_set_max_heartbeat(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_version_specialDesc;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__1;
x_2 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__0;
x_3 = lean_string_dec_eq(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__3() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__2;
x_2 = l_instDecidableNot___redArg(x_1);
return x_2;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__4() {
_start:
{
uint8_t x_1; 
x_1 = l_Lean_version_isRelease;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_versionStringCore;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-pre", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__6;
x_2 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__5;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__8;
x_2 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__5;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__0;
x_2 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__9;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString() {
_start:
{
uint8_t x_1; 
x_1 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__3;
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__4;
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__7;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__5;
return x_4;
}
}
else
{
lean_object* x_5; 
x_5 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__10;
return x_5;
}
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean (version ", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_get_build_type(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_githash;
return x_1;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__1;
x_2 = l___private_Lean_Shell_0__Lean_versionHeader___closed__4;
x_3 = lean_string_dec_eq(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__6() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = l___private_Lean_Shell_0__Lean_versionHeader___closed__5;
x_2 = l_instDecidableNot___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", commit ", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = l_System_Platform_target;
return x_1;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__1;
x_2 = l___private_Lean_Shell_0__Lean_versionHeader___closed__8;
x_3 = lean_string_dec_eq(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__10() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = l___private_Lean_Shell_0__Lean_versionHeader___closed__9;
x_2 = l_instDecidableNot___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Shell_0__Lean_versionHeader___closed__1;
x_2 = l___private_Lean_Shell_0__Lean_shortVersionString;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Shell_0__Lean_versionHeader___closed__8;
x_2 = l___private_Lean_Shell_0__Lean_versionHeader___closed__11;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader() {
_start:
{
lean_object* x_1; lean_object* x_11; lean_object* x_18; uint8_t x_19; 
x_18 = l___private_Lean_Shell_0__Lean_shortVersionString;
x_19 = l___private_Lean_Shell_0__Lean_versionHeader___closed__10;
if (x_19 == 0)
{
x_11 = x_18;
goto block_17;
}
else
{
lean_object* x_20; 
x_20 = l___private_Lean_Shell_0__Lean_versionHeader___closed__12;
x_11 = x_20;
goto block_17;
}
block_10:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = l___private_Lean_Shell_0__Lean_versionHeader___closed__0;
x_3 = lean_string_append(x_2, x_1);
lean_dec_ref(x_1);
x_4 = l___private_Lean_Shell_0__Lean_versionHeader___closed__1;
x_5 = lean_string_append(x_3, x_4);
x_6 = l___private_Lean_Shell_0__Lean_versionHeader___closed__2;
x_7 = lean_string_append(x_5, x_6);
x_8 = l___private_Lean_Shell_0__Lean_versionHeader___closed__3;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
block_17:
{
lean_object* x_12; uint8_t x_13; 
x_12 = l___private_Lean_Shell_0__Lean_versionHeader___closed__4;
x_13 = l___private_Lean_Shell_0__Lean_versionHeader___closed__6;
if (x_13 == 0)
{
x_1 = x_11;
goto block_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l___private_Lean_Shell_0__Lean_versionHeader___closed__7;
x_15 = lean_string_append(x_11, x_14);
x_16 = lean_string_append(x_15, x_12);
x_1 = x_16;
goto block_10;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_print___at___IO_println___at_____private_Lean_Shell_0__Lean_displayHeader_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_get_stdout(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_ctor_get(x_4, 4);
lean_inc_ref(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_6, x_1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_println___at_____private_Lean_Shell_0__Lean_displayHeader_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_print___at___IO_println___at_____private_Lean_Shell_0__Lean_displayHeader_spec__0_spec__0(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_display_header(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Shell_0__Lean_versionHeader;
x_3 = l_IO_println___at_____private_Lean_Shell_0__Lean_displayHeader_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      -D name=value      set a configuration option (see set_option command)", 76, 76);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --plugin=file      load and initialize Lean shared library for registering linters etc.", 93, 93);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --load-dynlib=file load shared library to make its symbols available to the interpreter", 93, 93);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --setup=file       JSON file with module setup data (supersedes the file's header)", 88, 88);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --json             report Lean output (e.g., messages) as JSON (one per line)", 83, 83);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -E  --error=kind       report Lean messages of kind as errors", 63, 63);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --deps             just print dependencies of a Lean input", 64, 64);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --src-deps         just print dependency sources of a Lean input", 70, 70);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --print-prefix     print the installation prefix for Lean and exit", 72, 72);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --print-libdir     print the installation directory for Lean's built-in libraries and exit", 96, 96);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --profile          display elaboration/type checking time for each definition/theorem", 91, 91);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --stats            display environment statistics", 55, 55);
return x_1;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_is_debug(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --debug=tag        enable assertions with the given tag", 61, 61);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Miscellaneous", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -h, --help             display this message", 45, 45);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --features         display features compiler provides (eg. LLVM support)", 78, 78);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -v, --version          display version information", 52, 52);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -V, --short-version    display short version number", 53, 53);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -g, --githash          display the git commit hash number used to build this binary", 85, 85);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --run <file>       call the 'main' definition in the given file with the remaining arguments", 98, 98);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -o, --o=oname          create olean file", 42, 42);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -i, --i=iname          create ilean file", 42, 42);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -c, --c=fname          name of the C output file", 50, 50);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -b, --bc=fname         name of the LLVM bitcode file", 54, 54);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --stdin            take input from stdin", 46, 46);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --root=dir         set package root directory from which the module name\n", 79, 79);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("                         of the input file is calculated\n", 57, 57);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("                         (default: current working directory)\n", 62, 62);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -t, --trust=num        trust level (default: max) 0 means do not trust any macro,\n", 84, 84);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("                         and type check all imported modules\n", 61, 61);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -q, --quiet            do not print verbose messages", 54, 54);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -M, --memory=num       maximum amount of memory that should be used by Lean", 77, 77);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("                         (in megabytes)", 39, 39);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -T, --timeout=num      maximum number of memory allocations per task", 70, 70);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("                         this is a deterministic way of interrupting long running tasks", 87, 87);
return x_1;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__36() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_is_multi_thread(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -j, --threads=num      number of threads used to process lean files", 69, 69);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -s, --tstack=num       thread stack size in Kb", 48, 48);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__39() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --server           start lean in server mode", 50, 50);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --worker           start lean in server-worker mode", 57, 57);
return x_1;
}
}
LEAN_EXPORT lean_object* lean_display_help(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_8; lean_object* x_9; lean_object* x_48; lean_object* x_49; 
if (x_1 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_get_stdout(x_2);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec_ref(x_133);
x_48 = x_134;
x_49 = x_135;
goto block_132;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_get_stderr(x_2);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec_ref(x_136);
x_48 = x_137;
x_49 = x_138;
goto block_132;
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Shell_0__Lean_displayHelp___closed__0;
x_6 = l_IO_FS_Stream_putStrLn(x_3, x_5, x_4);
return x_6;
}
block_47:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lean_Shell_0__Lean_displayHelp___closed__1;
lean_inc_ref(x_8);
x_11 = l_IO_FS_Stream_putStrLn(x_8, x_10, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l___private_Lean_Shell_0__Lean_displayHelp___closed__2;
lean_inc_ref(x_8);
x_14 = l_IO_FS_Stream_putStrLn(x_8, x_13, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l___private_Lean_Shell_0__Lean_displayHelp___closed__3;
lean_inc_ref(x_8);
x_17 = l_IO_FS_Stream_putStrLn(x_8, x_16, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l___private_Lean_Shell_0__Lean_displayHelp___closed__4;
lean_inc_ref(x_8);
x_20 = l_IO_FS_Stream_putStrLn(x_8, x_19, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l___private_Lean_Shell_0__Lean_displayHelp___closed__5;
lean_inc_ref(x_8);
x_23 = l_IO_FS_Stream_putStrLn(x_8, x_22, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = l___private_Lean_Shell_0__Lean_displayHelp___closed__6;
lean_inc_ref(x_8);
x_26 = l_IO_FS_Stream_putStrLn(x_8, x_25, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l___private_Lean_Shell_0__Lean_displayHelp___closed__7;
lean_inc_ref(x_8);
x_29 = l_IO_FS_Stream_putStrLn(x_8, x_28, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = l___private_Lean_Shell_0__Lean_displayHelp___closed__8;
lean_inc_ref(x_8);
x_32 = l_IO_FS_Stream_putStrLn(x_8, x_31, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = l___private_Lean_Shell_0__Lean_displayHelp___closed__9;
lean_inc_ref(x_8);
x_35 = l_IO_FS_Stream_putStrLn(x_8, x_34, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = l___private_Lean_Shell_0__Lean_displayHelp___closed__10;
lean_inc_ref(x_8);
x_38 = l_IO_FS_Stream_putStrLn(x_8, x_37, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = l___private_Lean_Shell_0__Lean_displayHelp___closed__11;
lean_inc_ref(x_8);
x_41 = l_IO_FS_Stream_putStrLn(x_8, x_40, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = l___private_Lean_Shell_0__Lean_displayHelp___closed__12;
if (x_43 == 0)
{
x_3 = x_8;
x_4 = x_42;
goto block_7;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = l___private_Lean_Shell_0__Lean_displayHelp___closed__13;
lean_inc_ref(x_8);
x_45 = l_IO_FS_Stream_putStrLn(x_8, x_44, x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec_ref(x_45);
x_3 = x_8;
x_4 = x_46;
goto block_7;
}
else
{
lean_dec_ref(x_8);
return x_45;
}
}
}
else
{
lean_dec_ref(x_8);
return x_41;
}
}
else
{
lean_dec_ref(x_8);
return x_38;
}
}
else
{
lean_dec_ref(x_8);
return x_35;
}
}
else
{
lean_dec_ref(x_8);
return x_32;
}
}
else
{
lean_dec_ref(x_8);
return x_29;
}
}
else
{
lean_dec_ref(x_8);
return x_26;
}
}
else
{
lean_dec_ref(x_8);
return x_23;
}
}
else
{
lean_dec_ref(x_8);
return x_20;
}
}
else
{
lean_dec_ref(x_8);
return x_17;
}
}
else
{
lean_dec_ref(x_8);
return x_14;
}
}
else
{
lean_dec_ref(x_8);
return x_11;
}
}
block_132:
{
lean_object* x_50; lean_object* x_51; 
x_50 = l___private_Lean_Shell_0__Lean_versionHeader;
lean_inc_ref(x_48);
x_51 = l_IO_FS_Stream_putStrLn(x_48, x_50, x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = l___private_Lean_Shell_0__Lean_displayHelp___closed__14;
lean_inc_ref(x_48);
x_54 = l_IO_FS_Stream_putStrLn(x_48, x_53, x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = l___private_Lean_Shell_0__Lean_displayHelp___closed__15;
lean_inc_ref(x_48);
x_57 = l_IO_FS_Stream_putStrLn(x_48, x_56, x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = l___private_Lean_Shell_0__Lean_displayHelp___closed__16;
lean_inc_ref(x_48);
x_60 = l_IO_FS_Stream_putStrLn(x_48, x_59, x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec_ref(x_60);
x_62 = l___private_Lean_Shell_0__Lean_displayHelp___closed__17;
lean_inc_ref(x_48);
x_63 = l_IO_FS_Stream_putStrLn(x_48, x_62, x_61);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = l___private_Lean_Shell_0__Lean_displayHelp___closed__18;
lean_inc_ref(x_48);
x_66 = l_IO_FS_Stream_putStrLn(x_48, x_65, x_64);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = l___private_Lean_Shell_0__Lean_displayHelp___closed__19;
lean_inc_ref(x_48);
x_69 = l_IO_FS_Stream_putStrLn(x_48, x_68, x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = l___private_Lean_Shell_0__Lean_displayHelp___closed__20;
lean_inc_ref(x_48);
x_72 = l_IO_FS_Stream_putStrLn(x_48, x_71, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec_ref(x_72);
x_74 = l___private_Lean_Shell_0__Lean_displayHelp___closed__21;
lean_inc_ref(x_48);
x_75 = l_IO_FS_Stream_putStrLn(x_48, x_74, x_73);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec_ref(x_75);
x_77 = l___private_Lean_Shell_0__Lean_displayHelp___closed__22;
lean_inc_ref(x_48);
x_78 = l_IO_FS_Stream_putStrLn(x_48, x_77, x_76);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec_ref(x_78);
x_80 = l___private_Lean_Shell_0__Lean_displayHelp___closed__23;
lean_inc_ref(x_48);
x_81 = l_IO_FS_Stream_putStrLn(x_48, x_80, x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec_ref(x_81);
x_83 = l___private_Lean_Shell_0__Lean_displayHelp___closed__24;
lean_inc_ref(x_48);
x_84 = l_IO_FS_Stream_putStrLn(x_48, x_83, x_82);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = l___private_Lean_Shell_0__Lean_displayHelp___closed__25;
lean_inc_ref(x_48);
x_87 = l_IO_FS_Stream_putStrLn(x_48, x_86, x_85);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec_ref(x_87);
x_89 = l___private_Lean_Shell_0__Lean_displayHelp___closed__26;
lean_inc_ref(x_48);
x_90 = l_IO_FS_Stream_putStrLn(x_48, x_89, x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec_ref(x_90);
x_92 = l___private_Lean_Shell_0__Lean_displayHelp___closed__27;
lean_inc_ref(x_48);
x_93 = l_IO_FS_Stream_putStrLn(x_48, x_92, x_91);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec_ref(x_93);
x_95 = l___private_Lean_Shell_0__Lean_displayHelp___closed__28;
lean_inc_ref(x_48);
x_96 = l_IO_FS_Stream_putStrLn(x_48, x_95, x_94);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec_ref(x_96);
x_98 = l___private_Lean_Shell_0__Lean_displayHelp___closed__29;
lean_inc_ref(x_48);
x_99 = l_IO_FS_Stream_putStrLn(x_48, x_98, x_97);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = l___private_Lean_Shell_0__Lean_displayHelp___closed__30;
lean_inc_ref(x_48);
x_102 = l_IO_FS_Stream_putStrLn(x_48, x_101, x_100);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec_ref(x_102);
x_104 = l___private_Lean_Shell_0__Lean_displayHelp___closed__31;
lean_inc_ref(x_48);
x_105 = l_IO_FS_Stream_putStrLn(x_48, x_104, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec_ref(x_105);
x_107 = l___private_Lean_Shell_0__Lean_displayHelp___closed__32;
lean_inc_ref(x_48);
x_108 = l_IO_FS_Stream_putStrLn(x_48, x_107, x_106);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec_ref(x_108);
x_110 = l___private_Lean_Shell_0__Lean_displayHelp___closed__33;
lean_inc_ref(x_48);
x_111 = l_IO_FS_Stream_putStrLn(x_48, x_110, x_109);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec_ref(x_111);
x_113 = l___private_Lean_Shell_0__Lean_displayHelp___closed__34;
lean_inc_ref(x_48);
x_114 = l_IO_FS_Stream_putStrLn(x_48, x_113, x_112);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec_ref(x_114);
x_116 = l___private_Lean_Shell_0__Lean_displayHelp___closed__35;
lean_inc_ref(x_48);
x_117 = l_IO_FS_Stream_putStrLn(x_48, x_116, x_115);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; uint8_t x_119; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec_ref(x_117);
x_119 = l___private_Lean_Shell_0__Lean_displayHelp___closed__36;
if (x_119 == 0)
{
x_8 = x_48;
x_9 = x_118;
goto block_47;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = l___private_Lean_Shell_0__Lean_displayHelp___closed__37;
lean_inc_ref(x_48);
x_121 = l_IO_FS_Stream_putStrLn(x_48, x_120, x_118);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec_ref(x_121);
x_123 = l___private_Lean_Shell_0__Lean_displayHelp___closed__38;
lean_inc_ref(x_48);
x_124 = l_IO_FS_Stream_putStrLn(x_48, x_123, x_122);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec_ref(x_124);
x_126 = l___private_Lean_Shell_0__Lean_displayHelp___closed__39;
lean_inc_ref(x_48);
x_127 = l_IO_FS_Stream_putStrLn(x_48, x_126, x_125);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec_ref(x_127);
x_129 = l___private_Lean_Shell_0__Lean_displayHelp___closed__40;
lean_inc_ref(x_48);
x_130 = l_IO_FS_Stream_putStrLn(x_48, x_129, x_128);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec_ref(x_130);
x_8 = x_48;
x_9 = x_131;
goto block_47;
}
else
{
lean_dec_ref(x_48);
return x_130;
}
}
else
{
lean_dec_ref(x_48);
return x_127;
}
}
else
{
lean_dec_ref(x_48);
return x_124;
}
}
else
{
lean_dec_ref(x_48);
return x_121;
}
}
}
else
{
lean_dec_ref(x_48);
return x_117;
}
}
else
{
lean_dec_ref(x_48);
return x_114;
}
}
else
{
lean_dec_ref(x_48);
return x_111;
}
}
else
{
lean_dec_ref(x_48);
return x_108;
}
}
else
{
lean_dec_ref(x_48);
return x_105;
}
}
else
{
lean_dec_ref(x_48);
return x_102;
}
}
else
{
lean_dec_ref(x_48);
return x_99;
}
}
else
{
lean_dec_ref(x_48);
return x_96;
}
}
else
{
lean_dec_ref(x_48);
return x_93;
}
}
else
{
lean_dec_ref(x_48);
return x_90;
}
}
else
{
lean_dec_ref(x_48);
return x_87;
}
}
else
{
lean_dec_ref(x_48);
return x_84;
}
}
else
{
lean_dec_ref(x_48);
return x_81;
}
}
else
{
lean_dec_ref(x_48);
return x_78;
}
}
else
{
lean_dec_ref(x_48);
return x_75;
}
}
else
{
lean_dec_ref(x_48);
return x_72;
}
}
else
{
lean_dec_ref(x_48);
return x_69;
}
}
else
{
lean_dec_ref(x_48);
return x_66;
}
}
else
{
lean_dec_ref(x_48);
return x_63;
}
}
else
{
lean_dec_ref(x_48);
return x_60;
}
}
else
{
lean_dec_ref(x_48);
return x_57;
}
}
else
{
lean_dec_ref(x_48);
return x_54;
}
}
else
{
lean_dec_ref(x_48);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHelp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = lean_display_help(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_ShellComponent_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Shell_0__Lean_ShellComponent_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Shell_0__Lean_ShellComponent_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l___private_Lean_Shell_0__Lean_ShellComponent_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
x_6 = lean_unbox(x_3);
x_7 = l___private_Lean_Shell_0__Lean_ShellComponent_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at_____private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_5);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_inc(x_1);
x_10 = lean_register_option(x_1, x_9, x_4);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_inc(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
lean_inc(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__0____x40_Lean_Shell_3125322801____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("max_memory", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__1____x40_Lean_Shell_3125322801____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Shell_0__Lean_initFn___closed__0____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__2____x40_Lean_Shell_3125322801____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_get_default_max_memory(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3____x40_Lean_Shell_3125322801____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__1;
x_2 = l___private_Lean_Shell_0__Lean_initFn___closed__2____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__4____x40_Lean_Shell_3125322801____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__5____x40_Lean_Shell_3125322801____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Shell_0__Lean_initFn___closed__4____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__6____x40_Lean_Shell_3125322801____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__7____x40_Lean_Shell_3125322801____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Shell_0__Lean_initFn___closed__6____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
x_2 = l___private_Lean_Shell_0__Lean_initFn___closed__5____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__8____x40_Lean_Shell_3125322801____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Shell", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__9____x40_Lean_Shell_3125322801____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Shell_0__Lean_initFn___closed__8____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
x_2 = l___private_Lean_Shell_0__Lean_initFn___closed__7____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__10____x40_Lean_Shell_3125322801____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_Shell_0__Lean_initFn___closed__9____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__11____x40_Lean_Shell_3125322801____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Shell_0__Lean_initFn___closed__6____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
x_2 = l___private_Lean_Shell_0__Lean_initFn___closed__10____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__12____x40_Lean_Shell_3125322801____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxMemory", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__13____x40_Lean_Shell_3125322801____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Shell_0__Lean_initFn___closed__12____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
x_2 = l___private_Lean_Shell_0__Lean_initFn___closed__11____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_3125322801____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Shell_0__Lean_initFn___closed__1____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
x_3 = l___private_Lean_Shell_0__Lean_initFn___closed__3____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
x_4 = l___private_Lean_Shell_0__Lean_initFn___closed__13____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
x_5 = l_Lean_Option_register___at_____private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at_____private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at_____private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__0____x40_Lean_Shell_1197438456____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("timeout", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__1____x40_Lean_Shell_1197438456____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Shell_0__Lean_initFn___closed__0____x40_Lean_Shell_1197438456____hygCtx___hyg_2_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__2____x40_Lean_Shell_1197438456____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_get_default_max_heartbeat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3____x40_Lean_Shell_1197438456____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__1;
x_2 = l___private_Lean_Shell_0__Lean_initFn___closed__2____x40_Lean_Shell_1197438456____hygCtx___hyg_2_;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__4____x40_Lean_Shell_1197438456____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Shell_0__Lean_initFn___closed__0____x40_Lean_Shell_1197438456____hygCtx___hyg_2_;
x_2 = l___private_Lean_Shell_0__Lean_initFn___closed__11____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_1197438456____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Shell_0__Lean_initFn___closed__1____x40_Lean_Shell_1197438456____hygCtx___hyg_2_;
x_3 = l___private_Lean_Shell_0__Lean_initFn___closed__3____x40_Lean_Shell_1197438456____hygCtx___hyg_2_;
x_4 = l___private_Lean_Shell_0__Lean_initFn___closed__4____x40_Lean_Shell_1197438456____hygCtx___hyg_2_;
x_5 = l_Lean_Option_register___at_____private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at_____private_Lean_Shell_0__Lean_shellMain_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_mk_io_user_error(x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at_____private_Lean_Shell_0__Lean_shellMain_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at_____private_Lean_Shell_0__Lean_shellMain_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_get_stderr(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_ctor_get(x_4, 4);
lean_inc_ref(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_6, x_1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_eprint___at___IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1_spec__1(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at_____private_Lean_Shell_0__Lean_shellMain_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_7; uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_3, x_2);
if (x_9 == 0)
{
return x_3;
}
else
{
uint32_t x_10; uint8_t x_11; uint32_t x_17; uint8_t x_18; 
x_10 = lean_string_utf8_get(x_1, x_3);
x_17 = 32;
x_18 = lean_uint32_dec_eq(x_10, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 9;
x_20 = lean_uint32_dec_eq(x_10, x_19);
x_11 = x_20;
goto block_16;
}
else
{
x_11 = x_18;
goto block_16;
}
block_16:
{
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 13;
x_13 = lean_uint32_dec_eq(x_10, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 10;
x_15 = lean_uint32_dec_eq(x_10, x_14);
x_7 = x_15;
goto block_8;
}
else
{
x_7 = x_13;
goto block_8;
}
}
else
{
goto block_6;
}
}
}
block_6:
{
lean_object* x_4; 
x_4 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_4;
goto _start;
}
block_8:
{
if (x_7 == 0)
{
return x_3;
}
else
{
goto block_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at_____private_Lean_Shell_0__Lean_shellMain_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; uint8_t x_6; uint32_t x_9; uint8_t x_10; uint32_t x_17; uint8_t x_18; 
x_5 = lean_string_utf8_prev(x_1, x_3);
x_9 = lean_string_utf8_get(x_1, x_5);
x_17 = 32;
x_18 = lean_uint32_dec_eq(x_9, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 9;
x_20 = lean_uint32_dec_eq(x_9, x_19);
x_10 = x_20;
goto block_16;
}
else
{
x_10 = x_18;
goto block_16;
}
block_8:
{
if (x_6 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
}
block_16:
{
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 13;
x_12 = lean_uint32_dec_eq(x_9, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 10;
x_14 = lean_uint32_dec_eq(x_9, x_13);
x_6 = x_14;
goto block_8;
}
else
{
x_6 = x_12;
goto block_8;
}
}
else
{
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at_____private_Lean_Shell_0__Lean_shellMain_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_find(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_6) == 3)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
return x_7;
}
else
{
lean_dec(x_6);
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_println___at_____private_Lean_Shell_0__Lean_shellMain_spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_print___at___IO_println___at_____private_Lean_Shell_0__Lean_displayHeader_spec__0_spec__0(x_4, x_2);
return x_5;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_has_address_sanitizer(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_10; 
x_4 = lean_display_cumulative_profiling_times(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_6 = x_4;
} else {
 lean_dec_ref(x_4);
 x_6 = lean_box(0);
}
x_10 = l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0;
if (x_10 == 0)
{
lean_dec(x_6);
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
x_12 = lean_io_exit(x_11, x_5);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; 
x_13 = 0;
x_14 = lean_io_exit(x_13, x_5);
return x_14;
}
}
else
{
if (lean_obj_tag(x_1) == 0)
{
goto block_9;
}
else
{
if (x_10 == 0)
{
goto block_9;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
x_15 = l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__2;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
return x_16;
}
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__1;
if (lean_is_scalar(x_6)) {
 x_8 = lean_alloc_ctor(0, 2, 0);
} else {
 x_8 = x_6;
}
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at_____private_Lean_Shell_0__Lean_shellMain_spec__0___redArg(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_string_to_utf8(x_5);
lean_dec(x_5);
x_8 = lean_io_prim_handle_write(x_2, x_7, x_6);
lean_dec_ref(x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LLVM code generation", 20, 20);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("C code generation", 17, 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to create '", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_stdin", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Shell_0__Lean_shellMain___closed__5;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#lang", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Shell_0__Lean_shellMain___closed__7;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Shell_0__Lean_shellMain___closed__8;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Shell_0__Lean_shellMain___closed__7;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean4", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown language '", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'\n", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expected exactly one file name", 30, 30);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<stdin>", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Shell_0__Lean_timeout;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Shell_0__Lean_maxMemory;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_shell_main(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10, uint32_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, uint8_t x_18, lean_object* x_19, uint8_t x_20, uint8_t x_21, lean_object* x_22) {
_start:
{
lean_object* x_23; lean_object* x_24; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_292; lean_object* x_298; lean_object* x_313; 
if (x_4 == 0)
{
if (x_5 == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_324 = l___private_Lean_Shell_0__Lean_shellMain___closed__16;
x_325 = l_Lean_Option_get___at_____private_Lean_Shell_0__Lean_shellMain_spec__5(x_10, x_324);
x_326 = lean_unsigned_to_nat(0u);
x_327 = lean_nat_dec_eq(x_325, x_326);
if (x_327 == 0)
{
size_t x_328; size_t x_329; size_t x_330; size_t x_331; lean_object* x_332; lean_object* x_333; 
x_328 = lean_usize_of_nat(x_325);
lean_dec(x_325);
x_329 = 1024;
x_330 = lean_usize_mul(x_328, x_329);
x_331 = lean_usize_mul(x_330, x_329);
x_332 = lean_internal_set_max_memory(x_331, x_22);
x_333 = lean_ctor_get(x_332, 1);
lean_inc(x_333);
lean_dec_ref(x_332);
x_313 = x_333;
goto block_323;
}
else
{
lean_dec(x_325);
x_313 = x_22;
goto block_323;
}
}
else
{
lean_object* x_334; 
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_334 = l_Lean_getBuildDir(x_22);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
lean_dec_ref(x_334);
x_337 = l_Lean_getLibDir(x_335, x_336);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec_ref(x_337);
x_340 = l_IO_println___at_____private_Lean_Shell_0__Lean_shellMain_spec__6(x_338, x_339);
if (lean_obj_tag(x_340) == 0)
{
uint8_t x_341; 
x_341 = !lean_is_exclusive(x_340);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; 
x_342 = lean_ctor_get(x_340, 0);
lean_dec(x_342);
x_343 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
lean_ctor_set(x_340, 0, x_343);
return x_340;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_340, 1);
lean_inc(x_344);
lean_dec(x_340);
x_345 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_344);
return x_346;
}
}
else
{
uint8_t x_347; 
x_347 = !lean_is_exclusive(x_340);
if (x_347 == 0)
{
return x_340;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_340, 0);
x_349 = lean_ctor_get(x_340, 1);
lean_inc(x_349);
lean_inc(x_348);
lean_dec(x_340);
x_350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
return x_350;
}
}
}
else
{
uint8_t x_351; 
x_351 = !lean_is_exclusive(x_337);
if (x_351 == 0)
{
return x_337;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_352 = lean_ctor_get(x_337, 0);
x_353 = lean_ctor_get(x_337, 1);
lean_inc(x_353);
lean_inc(x_352);
lean_dec(x_337);
x_354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set(x_354, 1, x_353);
return x_354;
}
}
}
else
{
uint8_t x_355; 
x_355 = !lean_is_exclusive(x_334);
if (x_355 == 0)
{
return x_334;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_356 = lean_ctor_get(x_334, 0);
x_357 = lean_ctor_get(x_334, 1);
lean_inc(x_357);
lean_inc(x_356);
lean_dec(x_334);
x_358 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_357);
return x_358;
}
}
}
}
else
{
lean_object* x_359; 
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_359 = l_Lean_getBuildDir(x_22);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
lean_dec_ref(x_359);
x_362 = l_IO_println___at_____private_Lean_Shell_0__Lean_shellMain_spec__6(x_360, x_361);
if (lean_obj_tag(x_362) == 0)
{
uint8_t x_363; 
x_363 = !lean_is_exclusive(x_362);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; 
x_364 = lean_ctor_get(x_362, 0);
lean_dec(x_364);
x_365 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
lean_ctor_set(x_362, 0, x_365);
return x_362;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_366 = lean_ctor_get(x_362, 1);
lean_inc(x_366);
lean_dec(x_362);
x_367 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
x_368 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_366);
return x_368;
}
}
else
{
uint8_t x_369; 
x_369 = !lean_is_exclusive(x_362);
if (x_369 == 0)
{
return x_362;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_370 = lean_ctor_get(x_362, 0);
x_371 = lean_ctor_get(x_362, 1);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_362);
x_372 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
return x_372;
}
}
}
else
{
uint8_t x_373; 
x_373 = !lean_is_exclusive(x_359);
if (x_373 == 0)
{
return x_359;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_374 = lean_ctor_get(x_359, 0);
x_375 = lean_ctor_get(x_359, 1);
lean_inc(x_375);
lean_inc(x_374);
lean_dec(x_359);
x_376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_376, 0, x_374);
lean_ctor_set(x_376, 1, x_375);
return x_376;
}
}
}
block_36:
{
lean_object* x_25; 
x_25 = l_Lean_printImportsJson(x_23, x_24);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
block_61:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_10);
x_41 = lean_box(0);
x_42 = lean_apply_2(x_39, x_41, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_17, 0);
lean_inc(x_43);
lean_dec_ref(x_17);
x_44 = lean_init_llvm(x_40);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = l___private_Lean_Shell_0__Lean_shellMain___closed__0;
x_47 = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_emitLLVM___boxed), 4, 3);
lean_closure_set(x_47, 0, x_37);
lean_closure_set(x_47, 1, x_38);
lean_closure_set(x_47, 2, x_43);
x_48 = lean_box(0);
x_49 = l_Lean_profileitIOUnsafe___redArg(x_46, x_10, x_47, x_48, x_45);
lean_dec(x_10);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec_ref(x_49);
x_52 = lean_apply_2(x_39, x_50, x_51);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec_ref(x_39);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
return x_49;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_49, 0);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_49);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_43);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_10);
x_57 = !lean_is_exclusive(x_44);
if (x_57 == 0)
{
return x_44;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_44, 0);
x_59 = lean_ctor_get(x_44, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_44);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
block_118:
{
lean_object* x_68; lean_object* x_69; 
x_68 = l___private_Lean_Shell_0__Lean_shellMain___closed__1;
lean_inc(x_66);
lean_inc(x_10);
x_69 = l_Lean_Elab_runFrontend(x_64, x_10, x_65, x_66, x_11, x_14, x_15, x_18, x_19, x_68, x_20, x_62, x_67);
lean_dec_ref(x_19);
lean_dec(x_15);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
lean_inc(x_70);
x_72 = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed), 3, 1);
lean_closure_set(x_72, 0, x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec_ref(x_72);
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
x_73 = lean_box(0);
x_74 = l___private_Lean_Shell_0__Lean_shellMain___lam__0(x_70, x_73, x_71);
return x_74;
}
else
{
if (x_21 == 0)
{
lean_dec(x_63);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
lean_dec_ref(x_70);
x_37 = x_75;
x_38 = x_66;
x_39 = x_72;
x_40 = x_71;
goto block_61;
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_70, 0);
lean_inc(x_76);
lean_dec_ref(x_70);
x_77 = lean_ctor_get(x_16, 0);
lean_inc(x_77);
lean_dec_ref(x_16);
x_78 = 1;
x_79 = lean_io_prim_handle_mk(x_77, x_78, x_71);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_77);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec_ref(x_79);
x_82 = l___private_Lean_Shell_0__Lean_shellMain___closed__2;
lean_inc(x_66);
lean_inc(x_76);
x_83 = lean_ir_emit_c(x_76, x_66);
x_84 = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed), 3, 2);
lean_closure_set(x_84, 0, x_83);
lean_closure_set(x_84, 1, x_80);
x_85 = lean_box(0);
x_86 = l_Lean_profileitIOUnsafe___redArg(x_82, x_10, x_84, x_85, x_81);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec_ref(x_86);
x_37 = x_76;
x_38 = x_66;
x_39 = x_72;
x_40 = x_87;
goto block_61;
}
else
{
uint8_t x_88; 
lean_dec(x_76);
lean_dec_ref(x_72);
lean_dec(x_66);
lean_dec(x_17);
lean_dec(x_10);
x_88 = !lean_is_exclusive(x_86);
if (x_88 == 0)
{
return x_86;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_86, 0);
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_86);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_76);
lean_dec_ref(x_72);
lean_dec(x_66);
lean_dec(x_17);
lean_dec(x_10);
x_92 = lean_ctor_get(x_79, 1);
lean_inc(x_92);
lean_dec_ref(x_79);
x_93 = l___private_Lean_Shell_0__Lean_shellMain___closed__3;
x_94 = lean_string_append(x_93, x_77);
lean_dec(x_77);
x_95 = l___private_Lean_Shell_0__Lean_shellMain___closed__4;
x_96 = lean_string_append(x_94, x_95);
x_97 = l_IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1(x_96, x_92);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_97, 0);
lean_dec(x_99);
x_100 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
lean_ctor_set(x_97, 0, x_100);
return x_97;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_97, 1);
lean_inc(x_101);
lean_dec(x_97);
x_102 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
else
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_97);
if (x_104 == 0)
{
return x_97;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_97, 0);
x_106 = lean_ctor_get(x_97, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_97);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
lean_dec_ref(x_72);
lean_dec(x_66);
lean_dec(x_17);
lean_dec(x_16);
x_108 = lean_ctor_get(x_70, 0);
lean_inc(x_108);
lean_dec_ref(x_70);
x_109 = lean_run_main(x_108, x_10, x_63, x_71);
lean_dec(x_63);
lean_dec(x_10);
lean_dec(x_108);
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
return x_109;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_109);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
x_114 = !lean_is_exclusive(x_69);
if (x_114 == 0)
{
return x_69;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_69, 0);
x_116 = lean_ctor_get(x_69, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_69);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
block_130:
{
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec_ref(x_123);
x_62 = x_119;
x_63 = x_120;
x_64 = x_121;
x_65 = x_122;
x_66 = x_124;
x_67 = x_125;
goto block_118;
}
else
{
uint8_t x_126; 
lean_dec_ref(x_122);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
x_126 = !lean_is_exclusive(x_123);
if (x_126 == 0)
{
return x_123;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_123, 0);
x_128 = lean_ctor_get(x_123, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_123);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
block_162:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_136; 
x_136 = lean_box(0);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_137; 
lean_dec(x_12);
x_137 = l___private_Lean_Shell_0__Lean_shellMain___closed__6;
x_62 = x_136;
x_63 = x_132;
x_64 = x_134;
x_65 = x_133;
x_66 = x_137;
x_67 = x_135;
goto block_118;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_131, 0);
lean_inc(x_138);
lean_dec_ref(x_131);
x_139 = l_Lean_moduleNameOfFileName(x_138, x_12, x_135);
if (lean_obj_tag(x_139) == 0)
{
x_119 = x_136;
x_120 = x_132;
x_121 = x_134;
x_122 = x_133;
x_123 = x_139;
goto block_130;
}
else
{
if (lean_obj_tag(x_14) == 0)
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec_ref(x_139);
x_141 = l___private_Lean_Shell_0__Lean_shellMain___closed__6;
x_62 = x_136;
x_63 = x_132;
x_64 = x_134;
x_65 = x_133;
x_66 = x_141;
x_67 = x_140;
goto block_118;
}
else
{
x_119 = x_136;
x_120 = x_132;
x_121 = x_134;
x_122 = x_133;
x_123 = x_139;
goto block_130;
}
}
else
{
x_119 = x_136;
x_120 = x_132;
x_121 = x_134;
x_122 = x_133;
x_123 = x_139;
goto block_130;
}
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_131);
lean_dec(x_12);
x_142 = !lean_is_exclusive(x_13);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_13, 0);
x_144 = l_Lean_ModuleSetup_load(x_143, x_135);
lean_dec(x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec_ref(x_144);
x_147 = lean_ctor_get(x_145, 0);
lean_inc(x_147);
lean_ctor_set(x_13, 0, x_145);
x_62 = x_13;
x_63 = x_132;
x_64 = x_134;
x_65 = x_133;
x_66 = x_147;
x_67 = x_146;
goto block_118;
}
else
{
uint8_t x_148; 
lean_free_object(x_13);
lean_dec_ref(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
x_148 = !lean_is_exclusive(x_144);
if (x_148 == 0)
{
return x_144;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_144, 0);
x_150 = lean_ctor_get(x_144, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_144);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_13, 0);
lean_inc(x_152);
lean_dec(x_13);
x_153 = l_Lean_ModuleSetup_load(x_152, x_135);
lean_dec(x_152);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec_ref(x_153);
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_154);
x_62 = x_157;
x_63 = x_132;
x_64 = x_134;
x_65 = x_133;
x_66 = x_156;
x_67 = x_155;
goto block_118;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec_ref(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
x_158 = lean_ctor_get(x_153, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_153, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_160 = x_153;
} else {
 lean_dec_ref(x_153);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
}
}
}
block_232:
{
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec_ref(x_166);
x_169 = lean_decode_lossy_utf8(x_167);
lean_dec(x_167);
if (x_7 == 0)
{
if (x_8 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_170 = lean_unsigned_to_nat(0u);
x_171 = lean_string_utf8_byte_size(x_169);
lean_inc(x_171);
lean_inc_ref(x_169);
x_172 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
lean_ctor_set(x_172, 2, x_171);
x_173 = lean_unsigned_to_nat(5u);
x_174 = l_Substring_nextn(x_172, x_173, x_170);
lean_dec_ref(x_172);
lean_inc_ref(x_169);
x_175 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_175, 0, x_169);
lean_ctor_set(x_175, 1, x_170);
lean_ctor_set(x_175, 2, x_174);
x_176 = l___private_Lean_Shell_0__Lean_shellMain___closed__9;
x_177 = l_Substring_beq(x_175, x_176);
if (x_177 == 0)
{
lean_dec(x_171);
x_131 = x_163;
x_132 = x_164;
x_133 = x_165;
x_134 = x_169;
x_135 = x_168;
goto block_162;
}
else
{
uint32_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_178 = 10;
x_179 = l_String_posOfAux(x_169, x_178, x_171, x_170);
x_180 = lean_unsigned_to_nat(6u);
x_181 = lean_string_utf8_extract(x_169, x_180, x_179);
x_182 = lean_string_utf8_byte_size(x_181);
x_183 = l_Substring_takeWhileAux___at_____private_Lean_Shell_0__Lean_shellMain_spec__3(x_181, x_182, x_170);
x_184 = l_Substring_takeRightWhileAux___at_____private_Lean_Shell_0__Lean_shellMain_spec__4(x_181, x_183, x_182);
x_185 = lean_string_utf8_extract(x_181, x_183, x_184);
lean_dec(x_184);
lean_dec(x_183);
lean_dec_ref(x_181);
x_186 = l___private_Lean_Shell_0__Lean_shellMain___closed__10;
x_187 = lean_string_dec_eq(x_185, x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_179);
lean_dec(x_171);
lean_dec_ref(x_169);
lean_dec_ref(x_165);
lean_dec(x_164);
lean_dec(x_163);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
x_188 = l___private_Lean_Shell_0__Lean_shellMain___closed__11;
x_189 = lean_string_append(x_188, x_185);
lean_dec_ref(x_185);
x_190 = l___private_Lean_Shell_0__Lean_shellMain___closed__12;
x_191 = lean_string_append(x_189, x_190);
x_192 = l_IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1(x_191, x_168);
if (lean_obj_tag(x_192) == 0)
{
uint8_t x_193; 
x_193 = !lean_is_exclusive(x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_192, 0);
lean_dec(x_194);
x_195 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
lean_ctor_set(x_192, 0, x_195);
return x_192;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_192, 1);
lean_inc(x_196);
lean_dec(x_192);
x_197 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
else
{
uint8_t x_199; 
x_199 = !lean_is_exclusive(x_192);
if (x_199 == 0)
{
return x_192;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_192, 0);
x_201 = lean_ctor_get(x_192, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_192);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
else
{
lean_object* x_203; 
lean_dec_ref(x_185);
x_203 = lean_string_utf8_extract(x_169, x_179, x_171);
lean_dec(x_171);
lean_dec(x_179);
lean_dec_ref(x_169);
x_131 = x_163;
x_132 = x_164;
x_133 = x_165;
x_134 = x_203;
x_135 = x_168;
goto block_162;
}
}
}
else
{
lean_object* x_204; lean_object* x_205; 
lean_dec(x_164);
lean_dec(x_163);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_165);
x_205 = l_Lean_Elab_printImportSrcs(x_169, x_204, x_168);
if (lean_obj_tag(x_205) == 0)
{
uint8_t x_206; 
x_206 = !lean_is_exclusive(x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_205, 0);
lean_dec(x_207);
x_208 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
lean_ctor_set(x_205, 0, x_208);
return x_205;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_205, 1);
lean_inc(x_209);
lean_dec(x_205);
x_210 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
}
else
{
uint8_t x_212; 
x_212 = !lean_is_exclusive(x_205);
if (x_212 == 0)
{
return x_205;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_205, 0);
x_214 = lean_ctor_get(x_205, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_205);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
}
else
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_164);
lean_dec(x_163);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_165);
x_217 = l_Lean_Elab_printImports(x_169, x_216, x_168);
if (lean_obj_tag(x_217) == 0)
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_217, 0);
lean_dec(x_219);
x_220 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
lean_ctor_set(x_217, 0, x_220);
return x_217;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_217, 1);
lean_inc(x_221);
lean_dec(x_217);
x_222 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_221);
return x_223;
}
}
else
{
uint8_t x_224; 
x_224 = !lean_is_exclusive(x_217);
if (x_224 == 0)
{
return x_217;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_217, 0);
x_226 = lean_ctor_get(x_217, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_217);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
}
else
{
uint8_t x_228; 
lean_dec_ref(x_165);
lean_dec(x_164);
lean_dec(x_163);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
x_228 = !lean_is_exclusive(x_166);
if (x_228 == 0)
{
return x_166;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_166, 0);
x_230 = lean_ctor_get(x_166, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_166);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
block_242:
{
if (x_6 == 0)
{
lean_object* x_237; 
x_237 = l_IO_FS_readBinFile(x_235, x_236);
x_163 = x_233;
x_164 = x_234;
x_165 = x_235;
x_166 = x_237;
goto block_232;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_238 = lean_get_stdin(x_236);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec_ref(x_238);
x_241 = l_IO_FS_Stream_readBinToEnd(x_239, x_240);
x_163 = x_233;
x_164 = x_234;
x_165 = x_235;
x_166 = x_241;
goto block_232;
}
}
block_267:
{
if (lean_obj_tag(x_243) == 0)
{
if (x_6 == 0)
{
lean_object* x_246; lean_object* x_247; 
lean_dec(x_245);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
x_246 = l___private_Lean_Shell_0__Lean_shellMain___closed__13;
x_247 = l_IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1(x_246, x_244);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; uint8_t x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_247, 1);
lean_inc(x_248);
lean_dec_ref(x_247);
x_249 = 1;
x_250 = lean_display_help(x_249, x_248);
if (lean_obj_tag(x_250) == 0)
{
uint8_t x_251; 
x_251 = !lean_is_exclusive(x_250);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; 
x_252 = lean_ctor_get(x_250, 0);
lean_dec(x_252);
x_253 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
lean_ctor_set(x_250, 0, x_253);
return x_250;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_250, 1);
lean_inc(x_254);
lean_dec(x_250);
x_255 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
else
{
uint8_t x_257; 
x_257 = !lean_is_exclusive(x_250);
if (x_257 == 0)
{
return x_250;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_250, 0);
x_259 = lean_ctor_get(x_250, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_250);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
}
}
else
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_247);
if (x_261 == 0)
{
return x_247;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_247, 0);
x_263 = lean_ctor_get(x_247, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_247);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
}
}
else
{
lean_object* x_265; 
x_265 = l___private_Lean_Shell_0__Lean_shellMain___closed__14;
x_233 = x_243;
x_234 = x_245;
x_235 = x_265;
x_236 = x_244;
goto block_242;
}
}
else
{
lean_object* x_266; 
x_266 = lean_ctor_get(x_243, 0);
lean_inc(x_266);
x_233 = x_243;
x_234 = x_245;
x_235 = x_266;
x_236 = x_244;
goto block_242;
}
}
block_291:
{
if (x_21 == 0)
{
uint8_t x_271; 
x_271 = l_List_isEmpty___redArg(x_270);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; 
lean_dec(x_270);
lean_dec(x_269);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
x_272 = l___private_Lean_Shell_0__Lean_shellMain___closed__13;
x_273 = l_IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1(x_272, x_268);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; uint8_t x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_273, 1);
lean_inc(x_274);
lean_dec_ref(x_273);
x_275 = 1;
x_276 = lean_display_help(x_275, x_274);
if (lean_obj_tag(x_276) == 0)
{
uint8_t x_277; 
x_277 = !lean_is_exclusive(x_276);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_276, 0);
lean_dec(x_278);
x_279 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
lean_ctor_set(x_276, 0, x_279);
return x_276;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_276, 1);
lean_inc(x_280);
lean_dec(x_276);
x_281 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
else
{
uint8_t x_283; 
x_283 = !lean_is_exclusive(x_276);
if (x_283 == 0)
{
return x_276;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_276, 0);
x_285 = lean_ctor_get(x_276, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_276);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
return x_286;
}
}
}
else
{
uint8_t x_287; 
x_287 = !lean_is_exclusive(x_273);
if (x_287 == 0)
{
return x_273;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_273, 0);
x_289 = lean_ctor_get(x_273, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_273);
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
return x_290;
}
}
}
else
{
x_243 = x_269;
x_244 = x_268;
x_245 = x_270;
goto block_267;
}
}
else
{
x_243 = x_269;
x_244 = x_268;
x_245 = x_270;
goto block_267;
}
}
block_297:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_293; 
x_293 = lean_box(0);
x_268 = x_292;
x_269 = x_293;
x_270 = x_1;
goto block_291;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_1, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_1, 1);
lean_inc(x_295);
lean_dec_ref(x_1);
x_296 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_296, 0, x_294);
x_268 = x_292;
x_269 = x_296;
x_270 = x_295;
goto block_291;
}
}
block_312:
{
switch (x_3) {
case 0:
{
lean_dec(x_2);
if (x_7 == 0)
{
x_292 = x_298;
goto block_297;
}
else
{
if (x_9 == 0)
{
x_292 = x_298;
goto block_297;
}
else
{
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
if (x_6 == 0)
{
lean_object* x_299; 
x_299 = lean_array_mk(x_1);
x_23 = x_299;
x_24 = x_298;
goto block_36;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_1);
x_300 = lean_get_stdin(x_298);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec_ref(x_300);
x_303 = l_IO_FS_Stream_lines(x_301, x_302);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
lean_dec_ref(x_303);
x_23 = x_304;
x_24 = x_305;
goto block_36;
}
else
{
uint8_t x_306; 
x_306 = !lean_is_exclusive(x_303);
if (x_306 == 0)
{
return x_303;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_303, 0);
x_308 = lean_ctor_get(x_303, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_303);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
}
}
}
case 1:
{
lean_object* x_310; 
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_1);
x_310 = l_Lean_Server_Watchdog_watchdogMain(x_2, x_298);
return x_310;
}
default: 
{
lean_object* x_311; 
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_311 = l_Lean_Server_FileWorker_workerMain(x_10, x_298);
return x_311;
}
}
}
block_323:
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_314 = l___private_Lean_Shell_0__Lean_shellMain___closed__15;
x_315 = l_Lean_Option_get___at_____private_Lean_Shell_0__Lean_shellMain_spec__5(x_10, x_314);
x_316 = lean_unsigned_to_nat(0u);
x_317 = lean_nat_dec_eq(x_315, x_316);
if (x_317 == 0)
{
size_t x_318; size_t x_319; size_t x_320; lean_object* x_321; lean_object* x_322; 
x_318 = lean_usize_of_nat(x_315);
lean_dec(x_315);
x_319 = 1000;
x_320 = lean_usize_mul(x_318, x_319);
x_321 = lean_internal_set_max_heartbeat(x_320, x_313);
x_322 = lean_ctor_get(x_321, 1);
lean_inc(x_322);
lean_dec_ref(x_321);
x_298 = x_322;
goto block_312;
}
else
{
lean_dec(x_315);
x_298 = x_313;
goto block_312;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at_____private_Lean_Shell_0__Lean_shellMain_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeWhileAux___at_____private_Lean_Shell_0__Lean_shellMain_spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at_____private_Lean_Shell_0__Lean_shellMain_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeRightWhileAux___at_____private_Lean_Shell_0__Lean_shellMain_spec__4(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at_____private_Lean_Shell_0__Lean_shellMain_spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at_____private_Lean_Shell_0__Lean_shellMain_spec__5(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Shell_0__Lean_shellMain___lam__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Shell_0__Lean_shellMain___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
_start:
{
uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint32_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_23 = lean_unbox(x_3);
x_24 = lean_unbox(x_4);
x_25 = lean_unbox(x_5);
x_26 = lean_unbox(x_6);
x_27 = lean_unbox(x_7);
x_28 = lean_unbox(x_8);
x_29 = lean_unbox(x_9);
x_30 = lean_unbox_uint32(x_11);
lean_dec(x_11);
x_31 = lean_unbox(x_18);
x_32 = lean_unbox(x_20);
x_33 = lean_unbox(x_21);
x_34 = lean_shell_main(x_1, x_2, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_10, x_30, x_12, x_13, x_14, x_15, x_16, x_17, x_31, x_19, x_32, x_33, x_22);
return x_34;
}
}
lean_object* initialize_Lean_Elab_Frontend(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_ParseImportsFast(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Watchdog(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_FileWorker(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_EmitC(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Shell(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Frontend(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ParseImportsFast(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Watchdog(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileWorker(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_EmitC(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Shell_0__Lean_shortVersionString___closed__0 = _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__0();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0);
l___private_Lean_Shell_0__Lean_shortVersionString___closed__1 = _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__1();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shortVersionString___closed__1);
l___private_Lean_Shell_0__Lean_shortVersionString___closed__2 = _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__2();
l___private_Lean_Shell_0__Lean_shortVersionString___closed__3 = _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__3();
l___private_Lean_Shell_0__Lean_shortVersionString___closed__4 = _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__4();
l___private_Lean_Shell_0__Lean_shortVersionString___closed__5 = _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__5();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shortVersionString___closed__5);
l___private_Lean_Shell_0__Lean_shortVersionString___closed__6 = _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__6();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shortVersionString___closed__6);
l___private_Lean_Shell_0__Lean_shortVersionString___closed__7 = _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__7();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shortVersionString___closed__7);
l___private_Lean_Shell_0__Lean_shortVersionString___closed__8 = _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__8();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shortVersionString___closed__8);
l___private_Lean_Shell_0__Lean_shortVersionString___closed__9 = _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__9();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shortVersionString___closed__9);
l___private_Lean_Shell_0__Lean_shortVersionString___closed__10 = _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__10();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shortVersionString___closed__10);
l___private_Lean_Shell_0__Lean_shortVersionString = _init_l___private_Lean_Shell_0__Lean_shortVersionString();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shortVersionString);
l___private_Lean_Shell_0__Lean_versionHeader___closed__0 = _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__0();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_versionHeader___closed__0);
l___private_Lean_Shell_0__Lean_versionHeader___closed__1 = _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__1();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_versionHeader___closed__1);
l___private_Lean_Shell_0__Lean_versionHeader___closed__2 = _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__2();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_versionHeader___closed__2);
l___private_Lean_Shell_0__Lean_versionHeader___closed__3 = _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__3();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_versionHeader___closed__3);
l___private_Lean_Shell_0__Lean_versionHeader___closed__4 = _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__4();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_versionHeader___closed__4);
l___private_Lean_Shell_0__Lean_versionHeader___closed__5 = _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__5();
l___private_Lean_Shell_0__Lean_versionHeader___closed__6 = _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__6();
l___private_Lean_Shell_0__Lean_versionHeader___closed__7 = _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__7();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_versionHeader___closed__7);
l___private_Lean_Shell_0__Lean_versionHeader___closed__8 = _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__8();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_versionHeader___closed__8);
l___private_Lean_Shell_0__Lean_versionHeader___closed__9 = _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__9();
l___private_Lean_Shell_0__Lean_versionHeader___closed__10 = _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__10();
l___private_Lean_Shell_0__Lean_versionHeader___closed__11 = _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__11();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_versionHeader___closed__11);
l___private_Lean_Shell_0__Lean_versionHeader___closed__12 = _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__12();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_versionHeader___closed__12);
l___private_Lean_Shell_0__Lean_versionHeader = _init_l___private_Lean_Shell_0__Lean_versionHeader();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_versionHeader);
l___private_Lean_Shell_0__Lean_displayHelp___closed__0 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__0();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__0);
l___private_Lean_Shell_0__Lean_displayHelp___closed__1 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__1();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__1);
l___private_Lean_Shell_0__Lean_displayHelp___closed__2 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__2();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__2);
l___private_Lean_Shell_0__Lean_displayHelp___closed__3 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__3();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__3);
l___private_Lean_Shell_0__Lean_displayHelp___closed__4 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__4();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__4);
l___private_Lean_Shell_0__Lean_displayHelp___closed__5 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__5();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__5);
l___private_Lean_Shell_0__Lean_displayHelp___closed__6 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__6();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__6);
l___private_Lean_Shell_0__Lean_displayHelp___closed__7 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__7();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__7);
l___private_Lean_Shell_0__Lean_displayHelp___closed__8 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__8();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__8);
l___private_Lean_Shell_0__Lean_displayHelp___closed__9 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__9();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__9);
l___private_Lean_Shell_0__Lean_displayHelp___closed__10 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__10();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__10);
l___private_Lean_Shell_0__Lean_displayHelp___closed__11 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__11();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__11);
l___private_Lean_Shell_0__Lean_displayHelp___closed__12 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__12();
l___private_Lean_Shell_0__Lean_displayHelp___closed__13 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__13();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__13);
l___private_Lean_Shell_0__Lean_displayHelp___closed__14 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__14();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__14);
l___private_Lean_Shell_0__Lean_displayHelp___closed__15 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__15();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__15);
l___private_Lean_Shell_0__Lean_displayHelp___closed__16 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__16();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__16);
l___private_Lean_Shell_0__Lean_displayHelp___closed__17 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__17();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__17);
l___private_Lean_Shell_0__Lean_displayHelp___closed__18 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__18();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__18);
l___private_Lean_Shell_0__Lean_displayHelp___closed__19 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__19();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__19);
l___private_Lean_Shell_0__Lean_displayHelp___closed__20 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__20();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__20);
l___private_Lean_Shell_0__Lean_displayHelp___closed__21 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__21();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__21);
l___private_Lean_Shell_0__Lean_displayHelp___closed__22 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__22();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__22);
l___private_Lean_Shell_0__Lean_displayHelp___closed__23 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__23();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__23);
l___private_Lean_Shell_0__Lean_displayHelp___closed__24 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__24();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__24);
l___private_Lean_Shell_0__Lean_displayHelp___closed__25 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__25();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__25);
l___private_Lean_Shell_0__Lean_displayHelp___closed__26 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__26();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__26);
l___private_Lean_Shell_0__Lean_displayHelp___closed__27 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__27();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__27);
l___private_Lean_Shell_0__Lean_displayHelp___closed__28 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__28();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__28);
l___private_Lean_Shell_0__Lean_displayHelp___closed__29 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__29();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__29);
l___private_Lean_Shell_0__Lean_displayHelp___closed__30 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__30();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__30);
l___private_Lean_Shell_0__Lean_displayHelp___closed__31 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__31();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__31);
l___private_Lean_Shell_0__Lean_displayHelp___closed__32 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__32();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__32);
l___private_Lean_Shell_0__Lean_displayHelp___closed__33 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__33();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__33);
l___private_Lean_Shell_0__Lean_displayHelp___closed__34 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__34();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__34);
l___private_Lean_Shell_0__Lean_displayHelp___closed__35 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__35();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__35);
l___private_Lean_Shell_0__Lean_displayHelp___closed__36 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__36();
l___private_Lean_Shell_0__Lean_displayHelp___closed__37 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__37();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__37);
l___private_Lean_Shell_0__Lean_displayHelp___closed__38 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__38();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__38);
l___private_Lean_Shell_0__Lean_displayHelp___closed__39 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__39();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__39);
l___private_Lean_Shell_0__Lean_displayHelp___closed__40 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__40();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__40);
l___private_Lean_Shell_0__Lean_initFn___closed__0____x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = _init_l___private_Lean_Shell_0__Lean_initFn___closed__0____x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_initFn___closed__0____x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
l___private_Lean_Shell_0__Lean_initFn___closed__1____x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = _init_l___private_Lean_Shell_0__Lean_initFn___closed__1____x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_initFn___closed__1____x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
l___private_Lean_Shell_0__Lean_initFn___closed__2____x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = _init_l___private_Lean_Shell_0__Lean_initFn___closed__2____x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_initFn___closed__2____x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
l___private_Lean_Shell_0__Lean_initFn___closed__3____x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = _init_l___private_Lean_Shell_0__Lean_initFn___closed__3____x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_initFn___closed__3____x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
l___private_Lean_Shell_0__Lean_initFn___closed__4____x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = _init_l___private_Lean_Shell_0__Lean_initFn___closed__4____x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_initFn___closed__4____x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
l___private_Lean_Shell_0__Lean_initFn___closed__5____x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = _init_l___private_Lean_Shell_0__Lean_initFn___closed__5____x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_initFn___closed__5____x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
l___private_Lean_Shell_0__Lean_initFn___closed__6____x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = _init_l___private_Lean_Shell_0__Lean_initFn___closed__6____x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_initFn___closed__6____x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
l___private_Lean_Shell_0__Lean_initFn___closed__7____x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = _init_l___private_Lean_Shell_0__Lean_initFn___closed__7____x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_initFn___closed__7____x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
l___private_Lean_Shell_0__Lean_initFn___closed__8____x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = _init_l___private_Lean_Shell_0__Lean_initFn___closed__8____x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_initFn___closed__8____x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
l___private_Lean_Shell_0__Lean_initFn___closed__9____x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = _init_l___private_Lean_Shell_0__Lean_initFn___closed__9____x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_initFn___closed__9____x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
l___private_Lean_Shell_0__Lean_initFn___closed__10____x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = _init_l___private_Lean_Shell_0__Lean_initFn___closed__10____x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_initFn___closed__10____x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
l___private_Lean_Shell_0__Lean_initFn___closed__11____x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = _init_l___private_Lean_Shell_0__Lean_initFn___closed__11____x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_initFn___closed__11____x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
l___private_Lean_Shell_0__Lean_initFn___closed__12____x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = _init_l___private_Lean_Shell_0__Lean_initFn___closed__12____x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_initFn___closed__12____x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
l___private_Lean_Shell_0__Lean_initFn___closed__13____x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = _init_l___private_Lean_Shell_0__Lean_initFn___closed__13____x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_initFn___closed__13____x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
if (builtin) {res = l___private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_3125322801____hygCtx___hyg_2_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Shell_0__Lean_maxMemory = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Shell_0__Lean_maxMemory);
lean_dec_ref(res);
}l___private_Lean_Shell_0__Lean_initFn___closed__0____x40_Lean_Shell_1197438456____hygCtx___hyg_2_ = _init_l___private_Lean_Shell_0__Lean_initFn___closed__0____x40_Lean_Shell_1197438456____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_initFn___closed__0____x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
l___private_Lean_Shell_0__Lean_initFn___closed__1____x40_Lean_Shell_1197438456____hygCtx___hyg_2_ = _init_l___private_Lean_Shell_0__Lean_initFn___closed__1____x40_Lean_Shell_1197438456____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_initFn___closed__1____x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
l___private_Lean_Shell_0__Lean_initFn___closed__2____x40_Lean_Shell_1197438456____hygCtx___hyg_2_ = _init_l___private_Lean_Shell_0__Lean_initFn___closed__2____x40_Lean_Shell_1197438456____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_initFn___closed__2____x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
l___private_Lean_Shell_0__Lean_initFn___closed__3____x40_Lean_Shell_1197438456____hygCtx___hyg_2_ = _init_l___private_Lean_Shell_0__Lean_initFn___closed__3____x40_Lean_Shell_1197438456____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_initFn___closed__3____x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
l___private_Lean_Shell_0__Lean_initFn___closed__4____x40_Lean_Shell_1197438456____hygCtx___hyg_2_ = _init_l___private_Lean_Shell_0__Lean_initFn___closed__4____x40_Lean_Shell_1197438456____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_initFn___closed__4____x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
if (builtin) {res = l___private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_1197438456____hygCtx___hyg_2_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Shell_0__Lean_timeout = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Shell_0__Lean_timeout);
lean_dec_ref(res);
}l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0 = _init_l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0();
l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__1 = _init_l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__1();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__1);
l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__2 = _init_l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__2();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__2);
l___private_Lean_Shell_0__Lean_shellMain___closed__0 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__0();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__0);
l___private_Lean_Shell_0__Lean_shellMain___closed__1 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__1();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__1);
l___private_Lean_Shell_0__Lean_shellMain___closed__2 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__2();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__2);
l___private_Lean_Shell_0__Lean_shellMain___closed__3 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__3();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__3);
l___private_Lean_Shell_0__Lean_shellMain___closed__4 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__4();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__4);
l___private_Lean_Shell_0__Lean_shellMain___closed__5 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__5();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__5);
l___private_Lean_Shell_0__Lean_shellMain___closed__6 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__6();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__6);
l___private_Lean_Shell_0__Lean_shellMain___closed__7 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__7();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__7);
l___private_Lean_Shell_0__Lean_shellMain___closed__8 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__8();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__8);
l___private_Lean_Shell_0__Lean_shellMain___closed__9 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__9();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__9);
l___private_Lean_Shell_0__Lean_shellMain___closed__10 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__10);
l___private_Lean_Shell_0__Lean_shellMain___closed__11 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__11);
l___private_Lean_Shell_0__Lean_shellMain___closed__12 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__12();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__12);
l___private_Lean_Shell_0__Lean_shellMain___closed__13 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__13);
l___private_Lean_Shell_0__Lean_shellMain___closed__14 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__14);
l___private_Lean_Shell_0__Lean_shellMain___closed__15 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__15();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__15);
l___private_Lean_Shell_0__Lean_shellMain___closed__16 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__16);
l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1 = _init_l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1);
l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2 = _init_l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
