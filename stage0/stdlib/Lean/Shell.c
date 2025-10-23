// Lean compiler output
// Module: Lean.Shell
// Imports: import Lean.Elab.Frontend import Lean.Elab.ParseImportsFast import Lean.Server.Watchdog import Lean.Server.FileWorker import Lean.Compiler.IR.EmitC
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
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__2;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__11;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__13____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
uint8_t lean_internal_is_debug(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__10;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initLLVM___boxed(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_1197438456____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__0____x40_Lean_Shell_1197438456____hygCtx___hyg_2_;
extern lean_object* l_Lean_githash;
LEAN_EXPORT lean_object* l_IO_println___at_____private_Lean_Shell_0__Lean_displayHeader_spec__0(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__29;
lean_object* lean_internal_set_max_heartbeat(size_t);
lean_object* lean_decode_lossy_utf8(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__2____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__0____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__2;
LEAN_EXPORT lean_object* l_IO_ofExcept___at_____private_Lean_Shell_0__Lean_shellMain_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__9____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_3125322801____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__5;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__9;
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__5;
lean_object* l_Lean_Elab_printImports(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__8;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__40;
size_t lean_usize_mul(size_t, size_t);
static uint8_t l___private_Lean_Shell_0__Lean_shortVersionString___closed__2;
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__6;
lean_object* l_Lean_KVMap_find(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_lines(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__30;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__1;
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at_____private_Lean_Shell_0__Lean_shellMain_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__21;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__38;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultMaxHeartbeat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at_____private_Lean_Shell_0__Lean_displayHeader_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at_____private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_emitLLVM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__3;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__11;
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__9;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__25;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__26;
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__7;
lean_object* l_Lean_moduleNameOfFileName(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__10;
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__1;
LEAN_EXPORT lean_object* l_IO_ofExcept___at_____private_Lean_Shell_0__Lean_shellMain_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHelp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultMaxMemory___boxed(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Server_FileWorker_workerMain(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__6;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__23;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__13;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__0;
extern uint8_t l_Lean_version_isRelease;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__27;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__16;
lean_object* lean_get_stdout();
LEAN_EXPORT lean_object* l_Lean_Option_get___at_____private_Lean_Shell_0__Lean_shellMain_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_display_header();
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object**);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__18;
size_t lean_usize_of_nat(lean_object*);
static uint8_t l___private_Lean_Shell_0__Lean_versionHeader___closed__10;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__20;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_decodeLossyUTF8___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__8;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__15;
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at_____private_Lean_Shell_0__Lean_shellMain_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_maxMemory;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__13;
static uint8_t l___private_Lean_Shell_0__Lean_displayHelp___closed__36;
LEAN_EXPORT lean_object* l_IO_print___at___IO_println___at_____private_Lean_Shell_0__Lean_displayHeader_spec__0_spec__0(lean_object*);
lean_object* l_IO_FS_Stream_readBinToEnd(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_1197438456____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim(lean_object*, uint8_t, lean_object*, lean_object*);
static uint8_t l___private_Lean_Shell_0__Lean_versionHeader___closed__5;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__12;
lean_object* lean_emit_llvm(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__3____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__5;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__4;
lean_object* l_Lean_Elab_printImportSrcs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHeader___boxed(lean_object*);
lean_object* l_Lean_Server_Watchdog_watchdogMain(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_isDebug___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at_____private_Lean_Shell_0__Lean_shellMain_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__19;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__7;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__12____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__0;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__1____x40_Lean_Shell_1197438456____hygCtx___hyg_2_;
lean_object* lean_get_stdin();
static uint8_t l___private_Lean_Shell_0__Lean_displayHelp___closed__12;
lean_object* l_String_posOfAux(lean_object*, uint32_t, lean_object*, lean_object*);
lean_object* lean_get_stderr();
lean_object* lean_mk_io_user_error(lean_object*);
static uint8_t l___private_Lean_Shell_0__Lean_versionHeader___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
static uint8_t l___private_Lean_Shell_0__Lean_versionHeader___closed__9;
lean_object* lean_internal_get_default_max_heartbeat(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(uint8_t);
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__7____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getBuildType___boxed(lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__3____x40_Lean_Shell_1197438456____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg___boxed(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__34;
lean_object* l_Lean_ModuleSetup_load(lean_object*);
lean_object* lean_internal_set_max_memory(size_t);
lean_object* lean_internal_get_build_type(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_hasAddressSanitizer___boxed(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__7;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__37;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__17;
lean_object* lean_internal_get_default_max_memory(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__4____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__11;
lean_object* lean_register_option(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_runMain___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayCumulativeProfilingTimes___boxed(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__14;
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_runFrontend(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1_spec__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__16;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__10;
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at_____private_Lean_Shell_0__Lean_shellMain_spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__7;
LEAN_EXPORT lean_object* l_IO_println___at_____private_Lean_Shell_0__Lean_shellMain_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at_____private_Lean_Shell_0__Lean_shellMain_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_noConfusion___redArg___lam__0___boxed(lean_object*);
lean_object* l_Lean_getBuildDir();
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__35;
static uint8_t l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_noConfusion___redArg___lam__0(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at_____private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__4;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_shell_main(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t);
uint32_t lean_run_main(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_timeout;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__24;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__3;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_init_llvm();
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__4____x40_Lean_Shell_1197438456____hygCtx___hyg_2_;
lean_object* lean_string_to_utf8(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setMaxHeartbeat___boxed(lean_object*, lean_object*);
lean_object* lean_io_exit(uint8_t);
LEAN_EXPORT lean_object* lean_display_help(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_noConfusion___redArg___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__8____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
uint8_t l_instDecidableNot___redArg(uint8_t);
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__10____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_versionStringCore;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__22;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_isMultiThread___boxed(lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__28;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Substring_beq(lean_object*, lean_object*);
lean_object* lean_display_cumulative_profiling_times();
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_noConfusion___redArg(uint8_t, uint8_t);
uint8_t lean_internal_has_address_sanitizer(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at_____private_Lean_Shell_0__Lean_shellMain_spec__5___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__0;
static uint8_t l___private_Lean_Shell_0__Lean_shortVersionString___closed__4;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__1;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__11____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shortVersionString;
lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__33;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__2____x40_Lean_Shell_1197438456____hygCtx___hyg_2_;
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_internal_is_multi_thread(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx(uint8_t);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__32;
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at_____private_Lean_Shell_0__Lean_shellMain_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at_____private_Lean_Shell_0__Lean_shellMain_spec__0___redArg(lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__6____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__2;
extern lean_object* l_System_Platform_target;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg___boxed(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__14;
lean_object* l_Lean_getLibDir(lean_object*);
extern lean_object* l_Lean_version_specialDesc;
lean_object* l_Lean_printImportsJson(lean_object*);
static uint8_t l___private_Lean_Shell_0__Lean_shortVersionString___closed__3;
LEAN_EXPORT lean_object* l_IO_print___at___IO_println___at_____private_Lean_Shell_0__Lean_displayHeader_spec__0_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__4;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__39;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1_spec__1(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__31;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__8;
lean_object* lean_ir_emit_c(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_versionHeader;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setMaxMemory___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__1____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim(lean_object*, uint8_t, lean_object*, lean_object*);
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
uint32_t x_5; lean_object* x_6; 
x_5 = lean_run_main(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initLLVM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_init_llvm();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_emitLLVM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_emit_llvm(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayCumulativeProfilingTimes___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_display_cumulative_profiling_times();
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
x_4 = lean_internal_set_max_memory(x_3);
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
x_4 = lean_internal_set_max_heartbeat(x_3);
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
LEAN_EXPORT lean_object* l_IO_print___at___IO_println___at_____private_Lean_Shell_0__Lean_displayHeader_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_get_stdout();
x_4 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_apply_2(x_4, x_1, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_println___at_____private_Lean_Shell_0__Lean_displayHeader_spec__0(lean_object* x_1) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_print___at___IO_println___at_____private_Lean_Shell_0__Lean_displayHeader_spec__0_spec__0(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_display_header() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Shell_0__Lean_versionHeader;
x_3 = l_IO_println___at_____private_Lean_Shell_0__Lean_displayHeader_spec__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___IO_println___at_____private_Lean_Shell_0__Lean_displayHeader_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_print___at___IO_println___at_____private_Lean_Shell_0__Lean_displayHeader_spec__0_spec__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_println___at_____private_Lean_Shell_0__Lean_displayHeader_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_println___at_____private_Lean_Shell_0__Lean_displayHeader_spec__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHeader___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_display_header();
return x_2;
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
LEAN_EXPORT lean_object* lean_display_help(uint8_t x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_8; lean_object* x_9; lean_object* x_36; lean_object* x_37; 
if (x_1 == 0)
{
lean_object* x_94; 
x_94 = lean_get_stdout();
x_36 = x_94;
x_37 = lean_box(0);
goto block_93;
}
else
{
lean_object* x_95; 
x_95 = lean_get_stderr();
x_36 = x_95;
x_37 = lean_box(0);
goto block_93;
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Shell_0__Lean_displayHelp___closed__0;
x_6 = l_IO_FS_Stream_putStrLn(x_3, x_5);
return x_6;
}
block_35:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lean_Shell_0__Lean_displayHelp___closed__1;
lean_inc_ref(x_8);
x_11 = l_IO_FS_Stream_putStrLn(x_8, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_11);
x_12 = l___private_Lean_Shell_0__Lean_displayHelp___closed__2;
lean_inc_ref(x_8);
x_13 = l_IO_FS_Stream_putStrLn(x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_13);
x_14 = l___private_Lean_Shell_0__Lean_displayHelp___closed__3;
lean_inc_ref(x_8);
x_15 = l_IO_FS_Stream_putStrLn(x_8, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_15);
x_16 = l___private_Lean_Shell_0__Lean_displayHelp___closed__4;
lean_inc_ref(x_8);
x_17 = l_IO_FS_Stream_putStrLn(x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_17);
x_18 = l___private_Lean_Shell_0__Lean_displayHelp___closed__5;
lean_inc_ref(x_8);
x_19 = l_IO_FS_Stream_putStrLn(x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_19);
x_20 = l___private_Lean_Shell_0__Lean_displayHelp___closed__6;
lean_inc_ref(x_8);
x_21 = l_IO_FS_Stream_putStrLn(x_8, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_21);
x_22 = l___private_Lean_Shell_0__Lean_displayHelp___closed__7;
lean_inc_ref(x_8);
x_23 = l_IO_FS_Stream_putStrLn(x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_23);
x_24 = l___private_Lean_Shell_0__Lean_displayHelp___closed__8;
lean_inc_ref(x_8);
x_25 = l_IO_FS_Stream_putStrLn(x_8, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_25);
x_26 = l___private_Lean_Shell_0__Lean_displayHelp___closed__9;
lean_inc_ref(x_8);
x_27 = l_IO_FS_Stream_putStrLn(x_8, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_27);
x_28 = l___private_Lean_Shell_0__Lean_displayHelp___closed__10;
lean_inc_ref(x_8);
x_29 = l_IO_FS_Stream_putStrLn(x_8, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_29);
x_30 = l___private_Lean_Shell_0__Lean_displayHelp___closed__11;
lean_inc_ref(x_8);
x_31 = l_IO_FS_Stream_putStrLn(x_8, x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec_ref(x_31);
x_32 = l___private_Lean_Shell_0__Lean_displayHelp___closed__12;
if (x_32 == 0)
{
x_3 = x_8;
x_4 = lean_box(0);
goto block_7;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = l___private_Lean_Shell_0__Lean_displayHelp___closed__13;
lean_inc_ref(x_8);
x_34 = l_IO_FS_Stream_putStrLn(x_8, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_dec_ref(x_34);
x_3 = x_8;
x_4 = lean_box(0);
goto block_7;
}
else
{
lean_dec_ref(x_8);
return x_34;
}
}
}
else
{
lean_dec_ref(x_8);
return x_31;
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
return x_27;
}
}
else
{
lean_dec_ref(x_8);
return x_25;
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
return x_21;
}
}
else
{
lean_dec_ref(x_8);
return x_19;
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
return x_15;
}
}
else
{
lean_dec_ref(x_8);
return x_13;
}
}
else
{
lean_dec_ref(x_8);
return x_11;
}
}
block_93:
{
lean_object* x_38; lean_object* x_39; 
x_38 = l___private_Lean_Shell_0__Lean_versionHeader;
lean_inc_ref(x_36);
x_39 = l_IO_FS_Stream_putStrLn(x_36, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_39);
x_40 = l___private_Lean_Shell_0__Lean_displayHelp___closed__14;
lean_inc_ref(x_36);
x_41 = l_IO_FS_Stream_putStrLn(x_36, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_41);
x_42 = l___private_Lean_Shell_0__Lean_displayHelp___closed__15;
lean_inc_ref(x_36);
x_43 = l_IO_FS_Stream_putStrLn(x_36, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_43);
x_44 = l___private_Lean_Shell_0__Lean_displayHelp___closed__16;
lean_inc_ref(x_36);
x_45 = l_IO_FS_Stream_putStrLn(x_36, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_45);
x_46 = l___private_Lean_Shell_0__Lean_displayHelp___closed__17;
lean_inc_ref(x_36);
x_47 = l_IO_FS_Stream_putStrLn(x_36, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_47);
x_48 = l___private_Lean_Shell_0__Lean_displayHelp___closed__18;
lean_inc_ref(x_36);
x_49 = l_IO_FS_Stream_putStrLn(x_36, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec_ref(x_49);
x_50 = l___private_Lean_Shell_0__Lean_displayHelp___closed__19;
lean_inc_ref(x_36);
x_51 = l_IO_FS_Stream_putStrLn(x_36, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_51);
x_52 = l___private_Lean_Shell_0__Lean_displayHelp___closed__20;
lean_inc_ref(x_36);
x_53 = l_IO_FS_Stream_putStrLn(x_36, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_53);
x_54 = l___private_Lean_Shell_0__Lean_displayHelp___closed__21;
lean_inc_ref(x_36);
x_55 = l_IO_FS_Stream_putStrLn(x_36, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec_ref(x_55);
x_56 = l___private_Lean_Shell_0__Lean_displayHelp___closed__22;
lean_inc_ref(x_36);
x_57 = l_IO_FS_Stream_putStrLn(x_36, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec_ref(x_57);
x_58 = l___private_Lean_Shell_0__Lean_displayHelp___closed__23;
lean_inc_ref(x_36);
x_59 = l_IO_FS_Stream_putStrLn(x_36, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec_ref(x_59);
x_60 = l___private_Lean_Shell_0__Lean_displayHelp___closed__24;
lean_inc_ref(x_36);
x_61 = l_IO_FS_Stream_putStrLn(x_36, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_61);
x_62 = l___private_Lean_Shell_0__Lean_displayHelp___closed__25;
lean_inc_ref(x_36);
x_63 = l_IO_FS_Stream_putStrLn(x_36, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_63);
x_64 = l___private_Lean_Shell_0__Lean_displayHelp___closed__26;
lean_inc_ref(x_36);
x_65 = l_IO_FS_Stream_putStrLn(x_36, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec_ref(x_65);
x_66 = l___private_Lean_Shell_0__Lean_displayHelp___closed__27;
lean_inc_ref(x_36);
x_67 = l_IO_FS_Stream_putStrLn(x_36, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec_ref(x_67);
x_68 = l___private_Lean_Shell_0__Lean_displayHelp___closed__28;
lean_inc_ref(x_36);
x_69 = l_IO_FS_Stream_putStrLn(x_36, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec_ref(x_69);
x_70 = l___private_Lean_Shell_0__Lean_displayHelp___closed__29;
lean_inc_ref(x_36);
x_71 = l_IO_FS_Stream_putStrLn(x_36, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec_ref(x_71);
x_72 = l___private_Lean_Shell_0__Lean_displayHelp___closed__30;
lean_inc_ref(x_36);
x_73 = l_IO_FS_Stream_putStrLn(x_36, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec_ref(x_73);
x_74 = l___private_Lean_Shell_0__Lean_displayHelp___closed__31;
lean_inc_ref(x_36);
x_75 = l_IO_FS_Stream_putStrLn(x_36, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec_ref(x_75);
x_76 = l___private_Lean_Shell_0__Lean_displayHelp___closed__32;
lean_inc_ref(x_36);
x_77 = l_IO_FS_Stream_putStrLn(x_36, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_77);
x_78 = l___private_Lean_Shell_0__Lean_displayHelp___closed__33;
lean_inc_ref(x_36);
x_79 = l_IO_FS_Stream_putStrLn(x_36, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec_ref(x_79);
x_80 = l___private_Lean_Shell_0__Lean_displayHelp___closed__34;
lean_inc_ref(x_36);
x_81 = l_IO_FS_Stream_putStrLn(x_36, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_dec_ref(x_81);
x_82 = l___private_Lean_Shell_0__Lean_displayHelp___closed__35;
lean_inc_ref(x_36);
x_83 = l_IO_FS_Stream_putStrLn(x_36, x_82);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
lean_dec_ref(x_83);
x_84 = l___private_Lean_Shell_0__Lean_displayHelp___closed__36;
if (x_84 == 0)
{
x_8 = x_36;
x_9 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = l___private_Lean_Shell_0__Lean_displayHelp___closed__37;
lean_inc_ref(x_36);
x_86 = l_IO_FS_Stream_putStrLn(x_36, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec_ref(x_86);
x_87 = l___private_Lean_Shell_0__Lean_displayHelp___closed__38;
lean_inc_ref(x_36);
x_88 = l_IO_FS_Stream_putStrLn(x_36, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec_ref(x_88);
x_89 = l___private_Lean_Shell_0__Lean_displayHelp___closed__39;
lean_inc_ref(x_36);
x_90 = l_IO_FS_Stream_putStrLn(x_36, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec_ref(x_90);
x_91 = l___private_Lean_Shell_0__Lean_displayHelp___closed__40;
lean_inc_ref(x_36);
x_92 = l_IO_FS_Stream_putStrLn(x_36, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_dec_ref(x_92);
x_8 = x_36;
x_9 = lean_box(0);
goto block_35;
}
else
{
lean_dec_ref(x_36);
return x_92;
}
}
else
{
lean_dec_ref(x_36);
return x_90;
}
}
else
{
lean_dec_ref(x_36);
return x_88;
}
}
else
{
lean_dec_ref(x_36);
return x_86;
}
}
}
else
{
lean_dec_ref(x_36);
return x_83;
}
}
else
{
lean_dec_ref(x_36);
return x_81;
}
}
else
{
lean_dec_ref(x_36);
return x_79;
}
}
else
{
lean_dec_ref(x_36);
return x_77;
}
}
else
{
lean_dec_ref(x_36);
return x_75;
}
}
else
{
lean_dec_ref(x_36);
return x_73;
}
}
else
{
lean_dec_ref(x_36);
return x_71;
}
}
else
{
lean_dec_ref(x_36);
return x_69;
}
}
else
{
lean_dec_ref(x_36);
return x_67;
}
}
else
{
lean_dec_ref(x_36);
return x_65;
}
}
else
{
lean_dec_ref(x_36);
return x_63;
}
}
else
{
lean_dec_ref(x_36);
return x_61;
}
}
else
{
lean_dec_ref(x_36);
return x_59;
}
}
else
{
lean_dec_ref(x_36);
return x_57;
}
}
else
{
lean_dec_ref(x_36);
return x_55;
}
}
else
{
lean_dec_ref(x_36);
return x_53;
}
}
else
{
lean_dec_ref(x_36);
return x_51;
}
}
else
{
lean_dec_ref(x_36);
return x_49;
}
}
else
{
lean_dec_ref(x_36);
return x_47;
}
}
else
{
lean_dec_ref(x_36);
return x_45;
}
}
else
{
lean_dec_ref(x_36);
return x_43;
}
}
else
{
lean_dec_ref(x_36);
return x_41;
}
}
else
{
lean_dec_ref(x_36);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHelp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = lean_display_help(x_3);
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
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(x_1);
x_4 = l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_ShellComponent_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_6;
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at_____private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = lean_register_option(x_1, x_9);
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
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_inc(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_5);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
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
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_3125322801____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Shell_0__Lean_initFn___closed__1____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
x_3 = l___private_Lean_Shell_0__Lean_initFn___closed__3____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
x_4 = l___private_Lean_Shell_0__Lean_initFn___closed__13____x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
x_5 = l_Lean_Option_register___at_____private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at_____private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at_____private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_3125322801____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
return x_2;
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
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_1197438456____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Shell_0__Lean_initFn___closed__1____x40_Lean_Shell_1197438456____hygCtx___hyg_2_;
x_3 = l___private_Lean_Shell_0__Lean_initFn___closed__3____x40_Lean_Shell_1197438456____hygCtx___hyg_2_;
x_4 = l___private_Lean_Shell_0__Lean_initFn___closed__4____x40_Lean_Shell_1197438456____hygCtx___hyg_2_;
x_5 = l_Lean_Option_register___at_____private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_1197438456____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_1197438456____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at_____private_Lean_Shell_0__Lean_shellMain_spec__0___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_mk_io_user_error(x_4);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_mk_io_user_error(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_ctor_set_tag(x_1, 0);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at_____private_Lean_Shell_0__Lean_shellMain_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at_____private_Lean_Shell_0__Lean_shellMain_spec__0___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_get_stderr();
x_4 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_apply_2(x_4, x_1, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object* x_1) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_eprint___at___IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1_spec__1(x_4);
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
LEAN_EXPORT lean_object* l_IO_println___at_____private_Lean_Shell_0__Lean_shellMain_spec__6(lean_object* x_1) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_print___at___IO_println___at_____private_Lean_Shell_0__Lean_displayHeader_spec__0_spec__0(x_4);
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
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_8; 
x_4 = lean_display_cumulative_profiling_times();
x_8 = l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0;
if (x_8 == 0)
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_9; lean_object* x_10; 
x_9 = 1;
x_10 = lean_io_exit(x_9);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; 
lean_dec_ref(x_1);
x_11 = 0;
x_12 = lean_io_exit(x_11);
return x_12;
}
}
else
{
if (lean_obj_tag(x_1) == 0)
{
goto block_7;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_1, 0);
lean_dec(x_14);
if (x_8 == 0)
{
lean_free_object(x_1);
goto block_7;
}
else
{
lean_object* x_15; 
x_15 = l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__2;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
}
else
{
lean_dec(x_1);
if (x_8 == 0)
{
goto block_7;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__2;
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__1;
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at_____private_Lean_Shell_0__Lean_shellMain_spec__0___redArg(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_string_to_utf8(x_5);
lean_dec(x_5);
x_7 = lean_io_prim_handle_write(x_2, x_6);
lean_dec_ref(x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
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
LEAN_EXPORT lean_object* lean_shell_main(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10, uint32_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, uint8_t x_18, lean_object* x_19, uint8_t x_20, uint8_t x_21) {
_start:
{
lean_object* x_23; lean_object* x_24; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_284; lean_object* x_290; lean_object* x_301; 
if (x_4 == 0)
{
if (x_5 == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_311 = l___private_Lean_Shell_0__Lean_shellMain___closed__16;
x_312 = l_Lean_Option_get___at_____private_Lean_Shell_0__Lean_shellMain_spec__5(x_10, x_311);
x_313 = lean_unsigned_to_nat(0u);
x_314 = lean_nat_dec_eq(x_312, x_313);
if (x_314 == 0)
{
size_t x_315; size_t x_316; size_t x_317; size_t x_318; lean_object* x_319; 
x_315 = lean_usize_of_nat(x_312);
lean_dec(x_312);
x_316 = 1024;
x_317 = lean_usize_mul(x_315, x_316);
x_318 = lean_usize_mul(x_317, x_316);
x_319 = lean_internal_set_max_memory(x_318);
x_301 = lean_box(0);
goto block_310;
}
else
{
lean_dec(x_312);
x_301 = lean_box(0);
goto block_310;
}
}
else
{
lean_object* x_320; 
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
x_320 = l_Lean_getBuildDir();
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
lean_dec_ref(x_320);
x_322 = l_Lean_getLibDir(x_321);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
lean_dec_ref(x_322);
x_324 = l_IO_println___at_____private_Lean_Shell_0__Lean_shellMain_spec__6(x_323);
if (lean_obj_tag(x_324) == 0)
{
uint8_t x_325; 
x_325 = !lean_is_exclusive(x_324);
if (x_325 == 0)
{
lean_object* x_326; lean_object* x_327; 
x_326 = lean_ctor_get(x_324, 0);
lean_dec(x_326);
x_327 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
lean_ctor_set(x_324, 0, x_327);
return x_324;
}
else
{
lean_object* x_328; lean_object* x_329; 
lean_dec(x_324);
x_328 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
x_329 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_329, 0, x_328);
return x_329;
}
}
else
{
uint8_t x_330; 
x_330 = !lean_is_exclusive(x_324);
if (x_330 == 0)
{
return x_324;
}
else
{
lean_object* x_331; lean_object* x_332; 
x_331 = lean_ctor_get(x_324, 0);
lean_inc(x_331);
lean_dec(x_324);
x_332 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_332, 0, x_331);
return x_332;
}
}
}
else
{
uint8_t x_333; 
x_333 = !lean_is_exclusive(x_322);
if (x_333 == 0)
{
return x_322;
}
else
{
lean_object* x_334; lean_object* x_335; 
x_334 = lean_ctor_get(x_322, 0);
lean_inc(x_334);
lean_dec(x_322);
x_335 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_335, 0, x_334);
return x_335;
}
}
}
else
{
uint8_t x_336; 
x_336 = !lean_is_exclusive(x_320);
if (x_336 == 0)
{
return x_320;
}
else
{
lean_object* x_337; lean_object* x_338; 
x_337 = lean_ctor_get(x_320, 0);
lean_inc(x_337);
lean_dec(x_320);
x_338 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_338, 0, x_337);
return x_338;
}
}
}
}
else
{
lean_object* x_339; 
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
x_339 = l_Lean_getBuildDir();
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; 
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
lean_dec_ref(x_339);
x_341 = l_IO_println___at_____private_Lean_Shell_0__Lean_shellMain_spec__6(x_340);
if (lean_obj_tag(x_341) == 0)
{
uint8_t x_342; 
x_342 = !lean_is_exclusive(x_341);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; 
x_343 = lean_ctor_get(x_341, 0);
lean_dec(x_343);
x_344 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
lean_ctor_set(x_341, 0, x_344);
return x_341;
}
else
{
lean_object* x_345; lean_object* x_346; 
lean_dec(x_341);
x_345 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
x_346 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_346, 0, x_345);
return x_346;
}
}
else
{
uint8_t x_347; 
x_347 = !lean_is_exclusive(x_341);
if (x_347 == 0)
{
return x_341;
}
else
{
lean_object* x_348; lean_object* x_349; 
x_348 = lean_ctor_get(x_341, 0);
lean_inc(x_348);
lean_dec(x_341);
x_349 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_349, 0, x_348);
return x_349;
}
}
}
else
{
uint8_t x_350; 
x_350 = !lean_is_exclusive(x_339);
if (x_350 == 0)
{
return x_339;
}
else
{
lean_object* x_351; lean_object* x_352; 
x_351 = lean_ctor_get(x_339, 0);
lean_inc(x_351);
lean_dec(x_339);
x_352 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_352, 0, x_351);
return x_352;
}
}
}
block_34:
{
lean_object* x_25; 
x_25 = l_Lean_printImportsJson(x_23);
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
lean_object* x_29; lean_object* x_30; 
lean_dec(x_25);
x_29 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
block_55:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec(x_10);
x_39 = lean_box(0);
x_40 = lean_apply_2(x_35, x_39, lean_box(0));
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_17, 0);
lean_inc(x_41);
lean_dec_ref(x_17);
x_42 = lean_init_llvm();
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec_ref(x_42);
x_43 = l___private_Lean_Shell_0__Lean_shellMain___closed__0;
x_44 = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_emitLLVM___boxed), 4, 3);
lean_closure_set(x_44, 0, x_37);
lean_closure_set(x_44, 1, x_36);
lean_closure_set(x_44, 2, x_41);
x_45 = lean_box(0);
x_46 = l_Lean_profileitIOUnsafe___redArg(x_43, x_10, x_44, x_45);
lean_dec(x_10);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = lean_apply_2(x_35, x_47, lean_box(0));
return x_48;
}
else
{
uint8_t x_49; 
lean_dec_ref(x_35);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_46, 0);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_41);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_10);
x_52 = !lean_is_exclusive(x_42);
if (x_52 == 0)
{
return x_42;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_42, 0);
lean_inc(x_53);
lean_dec(x_42);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
}
block_135:
{
lean_object* x_62; lean_object* x_63; 
x_62 = l___private_Lean_Shell_0__Lean_shellMain___closed__1;
lean_inc(x_60);
lean_inc(x_10);
x_63 = l_Lean_Elab_runFrontend(x_58, x_10, x_56, x_60, x_11, x_14, x_15, x_18, x_19, x_62, x_20, x_57);
lean_dec_ref(x_19);
lean_dec(x_15);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed), 3, 1);
lean_closure_set(x_66, 0, x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_66);
lean_free_object(x_63);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
x_67 = lean_box(0);
x_68 = l___private_Lean_Shell_0__Lean_shellMain___lam__0(x_65, x_67);
return x_68;
}
else
{
if (x_21 == 0)
{
lean_free_object(x_63);
lean_dec(x_59);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_65, 0);
lean_inc(x_69);
lean_dec_ref(x_65);
x_35 = x_66;
x_36 = x_60;
x_37 = x_69;
x_38 = lean_box(0);
goto block_55;
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
lean_dec_ref(x_65);
x_71 = lean_ctor_get(x_16, 0);
lean_inc(x_71);
lean_dec_ref(x_16);
x_72 = 1;
x_73 = lean_io_prim_handle_mk(x_71, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_71);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = l___private_Lean_Shell_0__Lean_shellMain___closed__2;
lean_inc(x_60);
lean_inc(x_70);
x_76 = lean_ir_emit_c(x_70, x_60);
x_77 = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed), 3, 2);
lean_closure_set(x_77, 0, x_76);
lean_closure_set(x_77, 1, x_74);
x_78 = lean_box(0);
x_79 = l_Lean_profileitIOUnsafe___redArg(x_75, x_10, x_77, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_dec_ref(x_79);
x_35 = x_66;
x_36 = x_60;
x_37 = x_70;
x_38 = lean_box(0);
goto block_55;
}
else
{
uint8_t x_80; 
lean_dec(x_70);
lean_dec_ref(x_66);
lean_dec(x_60);
lean_dec(x_17);
lean_dec(x_10);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
return x_79;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec_ref(x_73);
lean_dec(x_70);
lean_dec_ref(x_66);
lean_dec(x_60);
lean_dec(x_17);
lean_dec(x_10);
x_83 = l___private_Lean_Shell_0__Lean_shellMain___closed__3;
x_84 = lean_string_append(x_83, x_71);
lean_dec(x_71);
x_85 = l___private_Lean_Shell_0__Lean_shellMain___closed__4;
x_86 = lean_string_append(x_84, x_85);
x_87 = l_IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1(x_86);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_87, 0);
lean_dec(x_89);
x_90 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
lean_ctor_set(x_87, 0, x_90);
return x_87;
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_87);
x_91 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
else
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_87);
if (x_93 == 0)
{
return x_87;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_87, 0);
lean_inc(x_94);
lean_dec(x_87);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
}
}
}
else
{
lean_object* x_96; uint32_t x_97; lean_object* x_98; 
lean_dec_ref(x_66);
lean_dec(x_60);
lean_dec(x_17);
lean_dec(x_16);
x_96 = lean_ctor_get(x_65, 0);
lean_inc(x_96);
lean_dec_ref(x_65);
x_97 = lean_run_main(x_96, x_10, x_59);
lean_dec(x_59);
lean_dec(x_10);
lean_dec(x_96);
x_98 = lean_box_uint32(x_97);
lean_ctor_set(x_63, 0, x_98);
return x_63;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_63, 0);
lean_inc(x_99);
lean_dec(x_63);
lean_inc(x_99);
x_100 = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed), 3, 1);
lean_closure_set(x_100, 0, x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec_ref(x_100);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
x_101 = lean_box(0);
x_102 = l___private_Lean_Shell_0__Lean_shellMain___lam__0(x_99, x_101);
return x_102;
}
else
{
if (x_21 == 0)
{
lean_dec(x_59);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_99, 0);
lean_inc(x_103);
lean_dec_ref(x_99);
x_35 = x_100;
x_36 = x_60;
x_37 = x_103;
x_38 = lean_box(0);
goto block_55;
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_99, 0);
lean_inc(x_104);
lean_dec_ref(x_99);
x_105 = lean_ctor_get(x_16, 0);
lean_inc(x_105);
lean_dec_ref(x_16);
x_106 = 1;
x_107 = lean_io_prim_handle_mk(x_105, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_105);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = l___private_Lean_Shell_0__Lean_shellMain___closed__2;
lean_inc(x_60);
lean_inc(x_104);
x_110 = lean_ir_emit_c(x_104, x_60);
x_111 = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed), 3, 2);
lean_closure_set(x_111, 0, x_110);
lean_closure_set(x_111, 1, x_108);
x_112 = lean_box(0);
x_113 = l_Lean_profileitIOUnsafe___redArg(x_109, x_10, x_111, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_dec_ref(x_113);
x_35 = x_100;
x_36 = x_60;
x_37 = x_104;
x_38 = lean_box(0);
goto block_55;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_104);
lean_dec_ref(x_100);
lean_dec(x_60);
lean_dec(x_17);
lean_dec(x_10);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 x_115 = x_113;
} else {
 lean_dec_ref(x_113);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 1, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_114);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec_ref(x_107);
lean_dec(x_104);
lean_dec_ref(x_100);
lean_dec(x_60);
lean_dec(x_17);
lean_dec(x_10);
x_117 = l___private_Lean_Shell_0__Lean_shellMain___closed__3;
x_118 = lean_string_append(x_117, x_105);
lean_dec(x_105);
x_119 = l___private_Lean_Shell_0__Lean_shellMain___closed__4;
x_120 = lean_string_append(x_118, x_119);
x_121 = l_IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1(x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_122 = x_121;
} else {
 lean_dec_ref(x_121);
 x_122 = lean_box(0);
}
x_123 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 1, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_121, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_126 = x_121;
} else {
 lean_dec_ref(x_121);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 1, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_125);
return x_127;
}
}
}
}
else
{
lean_object* x_128; uint32_t x_129; lean_object* x_130; lean_object* x_131; 
lean_dec_ref(x_100);
lean_dec(x_60);
lean_dec(x_17);
lean_dec(x_16);
x_128 = lean_ctor_get(x_99, 0);
lean_inc(x_128);
lean_dec_ref(x_99);
x_129 = lean_run_main(x_128, x_10, x_59);
lean_dec(x_59);
lean_dec(x_10);
lean_dec(x_128);
x_130 = lean_box_uint32(x_129);
x_131 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_131, 0, x_130);
return x_131;
}
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
x_132 = !lean_is_exclusive(x_63);
if (x_132 == 0)
{
return x_63;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_63, 0);
lean_inc(x_133);
lean_dec(x_63);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
return x_134;
}
}
}
block_145:
{
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_dec_ref(x_140);
x_56 = x_136;
x_57 = x_137;
x_58 = x_138;
x_59 = x_139;
x_60 = x_141;
x_61 = lean_box(0);
goto block_135;
}
else
{
uint8_t x_142; 
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec_ref(x_136);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
x_142 = !lean_is_exclusive(x_140);
if (x_142 == 0)
{
return x_140;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_140, 0);
lean_inc(x_143);
lean_dec(x_140);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
return x_144;
}
}
}
block_172:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_151; 
x_151 = lean_box(0);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_152; 
lean_dec(x_12);
x_152 = l___private_Lean_Shell_0__Lean_shellMain___closed__6;
x_56 = x_146;
x_57 = x_151;
x_58 = x_149;
x_59 = x_148;
x_60 = x_152;
x_61 = lean_box(0);
goto block_135;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_147, 0);
lean_inc(x_153);
lean_dec_ref(x_147);
x_154 = l_Lean_moduleNameOfFileName(x_153, x_12);
if (lean_obj_tag(x_154) == 0)
{
x_136 = x_146;
x_137 = x_151;
x_138 = x_149;
x_139 = x_148;
x_140 = x_154;
goto block_145;
}
else
{
if (lean_obj_tag(x_14) == 0)
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_155; 
lean_dec_ref(x_154);
x_155 = l___private_Lean_Shell_0__Lean_shellMain___closed__6;
x_56 = x_146;
x_57 = x_151;
x_58 = x_149;
x_59 = x_148;
x_60 = x_155;
x_61 = lean_box(0);
goto block_135;
}
else
{
x_136 = x_146;
x_137 = x_151;
x_138 = x_149;
x_139 = x_148;
x_140 = x_154;
goto block_145;
}
}
else
{
x_136 = x_146;
x_137 = x_151;
x_138 = x_149;
x_139 = x_148;
x_140 = x_154;
goto block_145;
}
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_147);
lean_dec(x_12);
x_156 = !lean_is_exclusive(x_13);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_13, 0);
x_158 = l_Lean_ModuleSetup_load(x_157);
lean_dec(x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
lean_dec_ref(x_158);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_ctor_set(x_13, 0, x_159);
x_56 = x_146;
x_57 = x_13;
x_58 = x_149;
x_59 = x_148;
x_60 = x_160;
x_61 = lean_box(0);
goto block_135;
}
else
{
uint8_t x_161; 
lean_free_object(x_13);
lean_dec_ref(x_149);
lean_dec(x_148);
lean_dec_ref(x_146);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
x_161 = !lean_is_exclusive(x_158);
if (x_161 == 0)
{
return x_158;
}
else
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_158, 0);
lean_inc(x_162);
lean_dec(x_158);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
return x_163;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_13, 0);
lean_inc(x_164);
lean_dec(x_13);
x_165 = l_Lean_ModuleSetup_load(x_164);
lean_dec(x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
lean_dec_ref(x_165);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_168, 0, x_166);
x_56 = x_146;
x_57 = x_168;
x_58 = x_149;
x_59 = x_148;
x_60 = x_167;
x_61 = lean_box(0);
goto block_135;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec_ref(x_149);
lean_dec(x_148);
lean_dec_ref(x_146);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
x_169 = lean_ctor_get(x_165, 0);
lean_inc(x_169);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_170 = x_165;
} else {
 lean_dec_ref(x_165);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 1, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_169);
return x_171;
}
}
}
}
block_234:
{
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
lean_dec_ref(x_176);
x_178 = lean_decode_lossy_utf8(x_177);
lean_dec(x_177);
if (x_7 == 0)
{
if (x_8 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_179 = lean_unsigned_to_nat(0u);
x_180 = lean_string_utf8_byte_size(x_178);
lean_inc(x_180);
lean_inc_ref(x_178);
x_181 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_179);
lean_ctor_set(x_181, 2, x_180);
x_182 = lean_unsigned_to_nat(5u);
x_183 = l_Substring_nextn(x_181, x_182, x_179);
lean_dec_ref(x_181);
lean_inc_ref(x_178);
x_184 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_184, 0, x_178);
lean_ctor_set(x_184, 1, x_179);
lean_ctor_set(x_184, 2, x_183);
x_185 = l___private_Lean_Shell_0__Lean_shellMain___closed__9;
x_186 = l_Substring_beq(x_184, x_185);
if (x_186 == 0)
{
lean_dec(x_180);
x_146 = x_173;
x_147 = x_174;
x_148 = x_175;
x_149 = x_178;
x_150 = lean_box(0);
goto block_172;
}
else
{
uint32_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_187 = 10;
x_188 = l_String_posOfAux(x_178, x_187, x_180, x_179);
x_189 = lean_unsigned_to_nat(6u);
x_190 = lean_string_utf8_extract(x_178, x_189, x_188);
x_191 = lean_string_utf8_byte_size(x_190);
x_192 = l_Substring_takeWhileAux___at_____private_Lean_Shell_0__Lean_shellMain_spec__3(x_190, x_191, x_179);
x_193 = l_Substring_takeRightWhileAux___at_____private_Lean_Shell_0__Lean_shellMain_spec__4(x_190, x_192, x_191);
x_194 = lean_string_utf8_extract(x_190, x_192, x_193);
lean_dec(x_193);
lean_dec(x_192);
lean_dec_ref(x_190);
x_195 = l___private_Lean_Shell_0__Lean_shellMain___closed__10;
x_196 = lean_string_dec_eq(x_194, x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_188);
lean_dec(x_180);
lean_dec_ref(x_178);
lean_dec(x_175);
lean_dec(x_174);
lean_dec_ref(x_173);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
x_197 = l___private_Lean_Shell_0__Lean_shellMain___closed__11;
x_198 = lean_string_append(x_197, x_194);
lean_dec_ref(x_194);
x_199 = l___private_Lean_Shell_0__Lean_shellMain___closed__12;
x_200 = lean_string_append(x_198, x_199);
x_201 = l_IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1(x_200);
if (lean_obj_tag(x_201) == 0)
{
uint8_t x_202; 
x_202 = !lean_is_exclusive(x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_201, 0);
lean_dec(x_203);
x_204 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
lean_ctor_set(x_201, 0, x_204);
return x_201;
}
else
{
lean_object* x_205; lean_object* x_206; 
lean_dec(x_201);
x_205 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
x_206 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_206, 0, x_205);
return x_206;
}
}
else
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_201);
if (x_207 == 0)
{
return x_201;
}
else
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_201, 0);
lean_inc(x_208);
lean_dec(x_201);
x_209 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_209, 0, x_208);
return x_209;
}
}
}
else
{
lean_object* x_210; 
lean_dec_ref(x_194);
x_210 = lean_string_utf8_extract(x_178, x_188, x_180);
lean_dec(x_180);
lean_dec(x_188);
lean_dec_ref(x_178);
x_146 = x_173;
x_147 = x_174;
x_148 = x_175;
x_149 = x_210;
x_150 = lean_box(0);
goto block_172;
}
}
}
else
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_175);
lean_dec(x_174);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_173);
x_212 = l_Lean_Elab_printImportSrcs(x_178, x_211);
if (lean_obj_tag(x_212) == 0)
{
uint8_t x_213; 
x_213 = !lean_is_exclusive(x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_212, 0);
lean_dec(x_214);
x_215 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
lean_ctor_set(x_212, 0, x_215);
return x_212;
}
else
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_212);
x_216 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
x_217 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_217, 0, x_216);
return x_217;
}
}
else
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_212);
if (x_218 == 0)
{
return x_212;
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_212, 0);
lean_inc(x_219);
lean_dec(x_212);
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_219);
return x_220;
}
}
}
}
else
{
lean_object* x_221; lean_object* x_222; 
lean_dec(x_175);
lean_dec(x_174);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_173);
x_222 = l_Lean_Elab_printImports(x_178, x_221);
if (lean_obj_tag(x_222) == 0)
{
uint8_t x_223; 
x_223 = !lean_is_exclusive(x_222);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_222, 0);
lean_dec(x_224);
x_225 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
lean_ctor_set(x_222, 0, x_225);
return x_222;
}
else
{
lean_object* x_226; lean_object* x_227; 
lean_dec(x_222);
x_226 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
x_227 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_227, 0, x_226);
return x_227;
}
}
else
{
uint8_t x_228; 
x_228 = !lean_is_exclusive(x_222);
if (x_228 == 0)
{
return x_222;
}
else
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_222, 0);
lean_inc(x_229);
lean_dec(x_222);
x_230 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_230, 0, x_229);
return x_230;
}
}
}
}
else
{
uint8_t x_231; 
lean_dec(x_175);
lean_dec(x_174);
lean_dec_ref(x_173);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
x_231 = !lean_is_exclusive(x_176);
if (x_231 == 0)
{
return x_176;
}
else
{
lean_object* x_232; lean_object* x_233; 
x_232 = lean_ctor_get(x_176, 0);
lean_inc(x_232);
lean_dec(x_176);
x_233 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_233, 0, x_232);
return x_233;
}
}
}
block_242:
{
if (x_6 == 0)
{
lean_object* x_239; 
x_239 = l_IO_FS_readBinFile(x_237);
x_173 = x_237;
x_174 = x_235;
x_175 = x_236;
x_176 = x_239;
goto block_234;
}
else
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_get_stdin();
x_241 = l_IO_FS_Stream_readBinToEnd(x_240);
x_173 = x_237;
x_174 = x_235;
x_175 = x_236;
x_176 = x_241;
goto block_234;
}
}
block_263:
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
x_247 = l_IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1(x_246);
if (lean_obj_tag(x_247) == 0)
{
uint8_t x_248; lean_object* x_249; 
lean_dec_ref(x_247);
x_248 = 1;
x_249 = lean_display_help(x_248);
if (lean_obj_tag(x_249) == 0)
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_249);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_249, 0);
lean_dec(x_251);
x_252 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
lean_ctor_set(x_249, 0, x_252);
return x_249;
}
else
{
lean_object* x_253; lean_object* x_254; 
lean_dec(x_249);
x_253 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
x_254 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_254, 0, x_253);
return x_254;
}
}
else
{
uint8_t x_255; 
x_255 = !lean_is_exclusive(x_249);
if (x_255 == 0)
{
return x_249;
}
else
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_ctor_get(x_249, 0);
lean_inc(x_256);
lean_dec(x_249);
x_257 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_257, 0, x_256);
return x_257;
}
}
}
else
{
uint8_t x_258; 
x_258 = !lean_is_exclusive(x_247);
if (x_258 == 0)
{
return x_247;
}
else
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_247, 0);
lean_inc(x_259);
lean_dec(x_247);
x_260 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_260, 0, x_259);
return x_260;
}
}
}
else
{
lean_object* x_261; 
x_261 = l___private_Lean_Shell_0__Lean_shellMain___closed__14;
x_235 = x_243;
x_236 = x_245;
x_237 = x_261;
x_238 = lean_box(0);
goto block_242;
}
}
else
{
lean_object* x_262; 
x_262 = lean_ctor_get(x_243, 0);
lean_inc(x_262);
x_235 = x_243;
x_236 = x_245;
x_237 = x_262;
x_238 = lean_box(0);
goto block_242;
}
}
block_283:
{
if (x_21 == 0)
{
uint8_t x_267; 
x_267 = l_List_isEmpty___redArg(x_266);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; 
lean_dec(x_266);
lean_dec(x_265);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
x_268 = l___private_Lean_Shell_0__Lean_shellMain___closed__13;
x_269 = l_IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1(x_268);
if (lean_obj_tag(x_269) == 0)
{
uint8_t x_270; lean_object* x_271; 
lean_dec_ref(x_269);
x_270 = 1;
x_271 = lean_display_help(x_270);
if (lean_obj_tag(x_271) == 0)
{
uint8_t x_272; 
x_272 = !lean_is_exclusive(x_271);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_271, 0);
lean_dec(x_273);
x_274 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
lean_ctor_set(x_271, 0, x_274);
return x_271;
}
else
{
lean_object* x_275; lean_object* x_276; 
lean_dec(x_271);
x_275 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
x_276 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_276, 0, x_275);
return x_276;
}
}
else
{
uint8_t x_277; 
x_277 = !lean_is_exclusive(x_271);
if (x_277 == 0)
{
return x_271;
}
else
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_271, 0);
lean_inc(x_278);
lean_dec(x_271);
x_279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_279, 0, x_278);
return x_279;
}
}
}
else
{
uint8_t x_280; 
x_280 = !lean_is_exclusive(x_269);
if (x_280 == 0)
{
return x_269;
}
else
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_269, 0);
lean_inc(x_281);
lean_dec(x_269);
x_282 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_282, 0, x_281);
return x_282;
}
}
}
else
{
x_243 = x_265;
x_244 = lean_box(0);
x_245 = x_266;
goto block_263;
}
}
else
{
x_243 = x_265;
x_244 = lean_box(0);
x_245 = x_266;
goto block_263;
}
}
block_289:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_285; 
x_285 = lean_box(0);
x_264 = lean_box(0);
x_265 = x_285;
x_266 = x_1;
goto block_283;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_1, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_1, 1);
lean_inc(x_287);
lean_dec_ref(x_1);
x_288 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_288, 0, x_286);
x_264 = lean_box(0);
x_265 = x_288;
x_266 = x_287;
goto block_283;
}
}
block_300:
{
switch (x_3) {
case 0:
{
lean_dec(x_2);
if (x_7 == 0)
{
x_284 = lean_box(0);
goto block_289;
}
else
{
if (x_9 == 0)
{
x_284 = lean_box(0);
goto block_289;
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
lean_object* x_291; 
x_291 = lean_array_mk(x_1);
x_23 = x_291;
x_24 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_292; lean_object* x_293; 
lean_dec(x_1);
x_292 = lean_get_stdin();
x_293 = l_IO_FS_Stream_lines(x_292);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
lean_dec_ref(x_293);
x_23 = x_294;
x_24 = lean_box(0);
goto block_34;
}
else
{
uint8_t x_295; 
x_295 = !lean_is_exclusive(x_293);
if (x_295 == 0)
{
return x_293;
}
else
{
lean_object* x_296; lean_object* x_297; 
x_296 = lean_ctor_get(x_293, 0);
lean_inc(x_296);
lean_dec(x_293);
x_297 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_297, 0, x_296);
return x_297;
}
}
}
}
}
}
case 1:
{
lean_object* x_298; 
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_1);
x_298 = l_Lean_Server_Watchdog_watchdogMain(x_2);
return x_298;
}
default: 
{
lean_object* x_299; 
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_299 = l_Lean_Server_FileWorker_workerMain(x_10);
return x_299;
}
}
}
block_310:
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_302 = l___private_Lean_Shell_0__Lean_shellMain___closed__15;
x_303 = l_Lean_Option_get___at_____private_Lean_Shell_0__Lean_shellMain_spec__5(x_10, x_302);
x_304 = lean_unsigned_to_nat(0u);
x_305 = lean_nat_dec_eq(x_303, x_304);
if (x_305 == 0)
{
size_t x_306; size_t x_307; size_t x_308; lean_object* x_309; 
x_306 = lean_usize_of_nat(x_303);
lean_dec(x_303);
x_307 = 1000;
x_308 = lean_usize_mul(x_306, x_307);
x_309 = lean_internal_set_max_heartbeat(x_308);
x_290 = lean_box(0);
goto block_300;
}
else
{
lean_dec(x_303);
x_290 = lean_box(0);
goto block_300;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at_____private_Lean_Shell_0__Lean_shellMain_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at_____private_Lean_Shell_0__Lean_shellMain_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at_____private_Lean_Shell_0__Lean_shellMain_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at_____private_Lean_Shell_0__Lean_shellMain_spec__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_eprint___at___IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1_spec__1(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_eprintln___at_____private_Lean_Shell_0__Lean_shellMain_spec__1(x_1);
return x_3;
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
LEAN_EXPORT lean_object* l_IO_println___at_____private_Lean_Shell_0__Lean_shellMain_spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_println___at_____private_Lean_Shell_0__Lean_shellMain_spec__6(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Shell_0__Lean_shellMain___lam__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Shell_0__Lean_shellMain___lam__1(x_1, x_2);
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
x_34 = lean_shell_main(x_1, x_2, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_10, x_30, x_12, x_13, x_14, x_15, x_16, x_17, x_31, x_19, x_32, x_33);
return x_34;
}
}
lean_object* initialize_Lean_Elab_Frontend(uint8_t builtin);
lean_object* initialize_Lean_Elab_ParseImportsFast(uint8_t builtin);
lean_object* initialize_Lean_Server_Watchdog(uint8_t builtin);
lean_object* initialize_Lean_Server_FileWorker(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_EmitC(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Shell(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Frontend(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ParseImportsFast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Watchdog(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileWorker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_EmitC(builtin);
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
if (builtin) {res = l___private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
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
if (builtin) {res = l___private_Lean_Shell_0__Lean_initFn____x40_Lean_Shell_1197438456____hygCtx___hyg_2_();
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
