// Lean compiler output
// Module: Lean.Shell
// Imports: import Lean.Elab.Frontend import Lean.Elab.ParseImportsFast import Lean.Server.Watchdog import Lean.Server.FileWorker import Lean.Compiler.LCNF.EmitC import Init.System.Platform import Lean.Compiler.Options import Std.Async.Process
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
extern lean_object* l_Lean_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
lean_object* l_IO_eprint___redArg(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Compiler_LCNF_emitC(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stderr();
uint32_t lean_internal_get_hardware_concurrency(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_toName(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecls();
lean_object* l_Lean_Language_Lean_setOption(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
extern lean_object* l_Lean_version_specialDesc;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_versionStringCore;
extern uint8_t l_Lean_version_isRelease;
lean_object* lean_uv_os_getpid();
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* lean_io_remove_file(lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
lean_object* lean_io_prim_handle_flush(lean_object*);
lean_object* lean_io_rename(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*);
extern lean_object* l_Lean_githash;
extern lean_object* l_System_Platform_target;
lean_object* lean_get_stdout();
lean_object* l_String_toName(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_load_dynlib(lean_object*);
lean_object* lean_load_plugin(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
extern lean_object* l_Lean_Compiler_compiler_postponeCompile;
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
extern lean_object* l_System_Platform_numBits;
lean_object* lean_nat_pow(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_internal_has_llvm_backend(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
extern lean_object* l_Lean_Options_empty;
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_printImportsJson(lean_object*);
lean_object* lean_io_exit(uint8_t);
lean_object* lean_display_cumulative_profiling_times();
lean_object* l_Lean_Options_mergeBy(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_runFrontend(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_moduleNameOfFileName(lean_object*, lean_object*);
lean_object* l_Lean_ModuleSetup_load(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
uint8_t l_String_Slice_beq(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_Lean_Elab_printImportSrcs(lean_object*, lean_object*);
lean_object* l_Lean_Elab_printImports(lean_object*, lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*);
lean_object* lean_get_stdin();
lean_object* l_IO_FS_Stream_readBinToEnd(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_IO_FS_Stream_lines(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Server_Watchdog_watchdogMain(lean_object*);
lean_object* l_Lean_Server_FileWorker_workerMain(lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_getBuildDir();
lean_object* l_Lean_getLibDir(lean_object*);
lean_object* lean_decode_lossy_utf8(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_decodeLossyUTF8___boxed(lean_object*);
uint32_t lean_eval_main(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_runMain___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_init_llvm();
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initLLVM___boxed(lean_object*);
lean_object* lean_emit_llvm(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_emitLLVM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_internal_has_address_sanitizer(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_hasAddressSanitizer___boxed(lean_object*);
uint8_t lean_internal_is_multi_thread(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_isMultiThread___boxed(lean_object*);
uint8_t lean_internal_is_debug(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_isDebug___boxed(lean_object*);
lean_object* lean_internal_get_build_type(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getBuildType___boxed(lean_object*);
lean_object* lean_internal_get_default_max_memory(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultMaxMemory___boxed(lean_object*);
lean_object* lean_internal_set_max_memory(size_t);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setMaxMemory___boxed(lean_object*, lean_object*);
lean_object* lean_internal_get_default_max_heartbeat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultMaxHeartbeat___boxed(lean_object*);
lean_object* lean_internal_set_max_heartbeat(size_t);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setMaxHeartbeat___boxed(lean_object*, lean_object*);
uint8_t lean_internal_get_default_verbose(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultVerbose___boxed(lean_object*);
lean_object* lean_internal_set_exit_on_panic(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setExitOnPanic___boxed(lean_object*, lean_object*);
lean_object* lean_internal_set_thread_stack_size(size_t);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setThreadStackSize___boxed(lean_object*, lean_object*);
lean_object* lean_internal_enable_debug(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_enableDebug___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Shell_0__Lean_shortVersionString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shortVersionString___closed__0_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shortVersionString___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Shell_0__Lean_shortVersionString___closed__1;
static const lean_string_object l___private_Lean_Shell_0__Lean_shortVersionString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__2 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shortVersionString___closed__2_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shortVersionString___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__3;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shortVersionString___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__4;
static const lean_string_object l___private_Lean_Shell_0__Lean_shortVersionString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "-pre"};
static const lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__5 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shortVersionString___closed__5_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shortVersionString___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shortVersionString;
static const lean_string_object l___private_Lean_Shell_0__Lean_versionHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean (version "};
static const lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_versionHeader___closed__0_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_versionHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__1 = (const lean_object*)&l___private_Lean_Shell_0__Lean_versionHeader___closed__1_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_versionHeader___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__2;
static const lean_string_object l___private_Lean_Shell_0__Lean_versionHeader___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__3 = (const lean_object*)&l___private_Lean_Shell_0__Lean_versionHeader___closed__3_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_versionHeader___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Shell_0__Lean_versionHeader___closed__4;
static const lean_string_object l___private_Lean_Shell_0__Lean_versionHeader___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ", commit "};
static const lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__5 = (const lean_object*)&l___private_Lean_Shell_0__Lean_versionHeader___closed__5_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_versionHeader___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Shell_0__Lean_versionHeader___closed__6;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_versionHeader___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__7;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_versionHeader___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_versionHeader;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_featuresString___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Shell_0__Lean_featuresString___closed__0;
static const lean_string_object l___private_Lean_Shell_0__Lean_featuresString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l___private_Lean_Shell_0__Lean_featuresString___closed__1 = (const lean_object*)&l___private_Lean_Shell_0__Lean_featuresString___closed__1_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_featuresString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "[LLVM]"};
static const lean_object* l___private_Lean_Shell_0__Lean_featuresString___closed__2 = (const lean_object*)&l___private_Lean_Shell_0__Lean_featuresString___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_featuresString;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 77, .m_capacity = 77, .m_length = 76, .m_data = "      -D name=value      set a configuration option (see set_option command)"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__0_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "      --plugin=file[=fn] load and initialize Lean shared library for registering linters etc."};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__1 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__1_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "      --load-dynlib=file load shared library to make its symbols available to the interpreter"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__2 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__2_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 89, .m_capacity = 89, .m_length = 88, .m_data = "      --setup=file       JSON file with module setup data (supersedes the file's header)"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__3 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__3_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 83, .m_data = "      --json             report Lean output (e.g., messages) as JSON (one per line)"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__4 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__4_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "  -E, --error=kind       report Lean messages of kind as errors"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__5 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__5_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "      --deps             just print dependencies of a Lean input"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__6 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__6_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "      --src-deps         just print dependency sources of a Lean input"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__7 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__7_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "      --print-prefix     print the installation prefix for Lean and exit"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__8 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__8_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 97, .m_capacity = 97, .m_length = 96, .m_data = "      --print-libdir     print the installation directory for Lean's built-in libraries and exit"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__9 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__9_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 92, .m_capacity = 92, .m_length = 91, .m_data = "      --profile          display elaboration/type checking time for each definition/theorem"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__10 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__10_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "      --stats            display environment statistics"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__11 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__11_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 112, .m_capacity = 112, .m_length = 111, .m_data = "      --incr-save=file   EXPERIMENTAL: save a full incremental snapshot of post-elaboration state at end of run"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__12 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__12_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "      --incr-load=file   EXPERIMENTAL: reuse a snapshot saved by `--incr-(header-)save` at start of run"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__13 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__13_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "      --incr-header-save=file"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__14 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__14_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 108, .m_capacity = 108, .m_length = 107, .m_data = "                         EXPERIMENTAL: like `--incr-save`, but save only the header (state after importing)"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__15 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__15_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_displayHelp___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Shell_0__Lean_displayHelp___closed__16;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "      --debug=tag        enable assertions with the given tag"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__17 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__17_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Miscellaneous"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__18 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__18_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "  -h, --help             display this message"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__19 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__19_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "      --features         display features compiler provides (eg. LLVM support)"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__20 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__20_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "  -v, --version          display version information"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__21 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__21_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "  -V, --short-version    display short version number"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__22 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__22_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "  -g, --githash          display the git commit hash number used to build this binary"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__23 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__23_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 99, .m_capacity = 99, .m_length = 98, .m_data = "      --run <file>       call the 'main' definition in the given file with the remaining arguments"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__24 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__24_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "  -o, --o=oname          create olean file"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__25 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__25_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "  -i, --i=iname          create ilean file"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__26 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__26_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "  -c, --c=fname          name of the C output file"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__27 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__27_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "  -b, --bc=fname         name of the LLVM bitcode file"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__28 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__28_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "      --stdin            take input from stdin"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__29 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__29_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "  -R, --root=dir         set package root directory from which the module name\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__30 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__30_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "                         of the input file is calculated\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__31 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__31_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "                         (default: current working directory)\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__32 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__32_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "  -t, --trust=num        trust level (default: max) 0 means do not trust any macro,\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__33 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__33_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "                         and type check all imported modules\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__34 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__34_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "  -q, --quiet            do not print verbose messages"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__35 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__35_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "  -M, --memory=num       maximum amount of memory that should be used by Lean"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__36 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__36_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "                         (in megabytes)"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__37 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__37_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "  -T, --timeout=num      maximum number of memory allocations per task"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__38 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__38_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "                         this is a deterministic way of interrupting long running tasks"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__39 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__39_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_displayHelp___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Shell_0__Lean_displayHelp___closed__40;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "  -j, --threads=num      number of threads used to process lean files"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__41 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__41_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "  -s, --tstack=num       thread stack size in Kb"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__42 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__42_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "      --server           start lean in server mode"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__43 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__43_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "      --worker           start lean in server-worker mode"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__44 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__44_value;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHelp(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHelp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "max_memory"};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(227, 81, 94, 214, 186, 212, 139, 105)}};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_initFn___closed__5_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__5_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__5_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Shell_0__Lean_initFn___closed__6_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__6_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__6_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_initFn___closed__7_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__5_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__6_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__7_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__7_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Shell_0__Lean_initFn___closed__8_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Shell"};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__8_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__8_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_initFn___closed__9_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__7_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__8_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(32, 69, 169, 154, 100, 37, 235, 16)}};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__9_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__9_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_initFn___closed__10_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__9_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(89, 66, 50, 199, 34, 209, 110, 139)}};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__10_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__10_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_initFn___closed__11_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__10_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__6_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(60, 66, 221, 81, 125, 65, 65, 89)}};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__11_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__11_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Shell_0__Lean_initFn___closed__12_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "maxMemory"};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__12_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__12_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_initFn___closed__13_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__11_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__12_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(28, 55, 113, 152, 101, 101, 83, 88)}};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__13_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__13_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_maxMemory;
static const lean_string_object l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "timeout"};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(108, 201, 121, 146, 245, 42, 97, 81)}};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__11_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 41, 251, 70, 36, 12, 36, 182)}};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_timeout;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "verbose"};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(107, 17, 151, 162, 143, 207, 214, 14)}};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__11_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 79, 210, 200, 161, 113, 65, 201)}};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_verbose;
lean_object* lean_internal_get_option_overrides(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getOptionOverrides___boxed(lean_object*);
uint32_t lean_internal_get_believer_trust_level(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getBelieverTrustLevel___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1;
LEAN_EXPORT uint32_t l___private_Lean_Shell_0__Lean_defaultTrustLevel;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0;
LEAN_EXPORT uint32_t l___private_Lean_Shell_0__Lean_defaultNumThreads;
static const lean_array_object l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___redArg();
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0;
LEAN_EXPORT lean_object* lean_shell_options_mk(lean_object*);
LEAN_EXPORT uint8_t lean_shell_options_get_run(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getRun___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_shell_options_get_profiler(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getProfiler___boxed(lean_object*);
LEAN_EXPORT uint32_t lean_shell_options_get_num_threads(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getNumThreads___boxed(lean_object*);
static const lean_string_object l___private_Lean_Shell_0__Lean_checkOptArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "argument missing for option '-"};
static const lean_object* l___private_Lean_Shell_0__Lean_checkOptArg___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_checkOptArg___closed__0_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_checkOptArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lean_Shell_0__Lean_checkOptArg___closed__1 = (const lean_object*)&l___private_Lean_Shell_0__Lean_checkOptArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_checkOptArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_checkOptArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Shell_0__Lean_setConfigOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "invalid -D parameter, argument must contain '='"};
static const lean_object* l___private_Lean_Shell_0__Lean_setConfigOption___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_setConfigOption___closed__0_value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_setConfigOption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_Lean_Shell_0__Lean_setConfigOption___closed__0_value)}};
static const lean_object* l___private_Lean_Shell_0__Lean_setConfigOption___closed__1 = (const lean_object*)&l___private_Lean_Shell_0__Lean_setConfigOption___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_setConfigOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_setConfigOption___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "error: "};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "error: expected numeric argument for option '-"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__0_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "'\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "error: argument value for '-"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__0_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "' is too large\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__1 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Unknown command line option\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__0_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "H"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Z"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Y"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "E"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "u"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "l"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-l"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "p"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-p"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "B"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "D"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-D"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "t"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "error: argument value for '-t' is too large\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-t"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "error: expected numeric argument for option '-t'\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "T"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-T"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "error: expected numeric argument for option '-T'\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "M"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-M"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "error: expected numeric argument for option '-M'\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "R"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-R"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "i"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "o"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "error: argument value for '-s' is too large\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-s"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "error: expected numeric argument for option '-s'\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "c"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "j"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "error: argument value for '-j' is too large\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__35 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__35_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-j"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__36 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__36_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "error: expected numeric argument for option '-j'\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__37 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__37_value;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
LEAN_EXPORT lean_object* lean_shell_options_process(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "tmp"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "#lang"};
static const lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0 = (const lean_object*)&l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__0_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed(lean_object**);
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "C code generation"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__1;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__2;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__3_value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__4_value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__5 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__5_value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__6 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__6_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__7;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__8;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Shell_0__Lean_shellMain___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__0_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Shell_0__Lean_shellMain___closed__1;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__2;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "LLVM code generation"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__3 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__3_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Expected exactly one file name"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__4 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__4_value;
static const lean_array_object l___private_Lean_Shell_0__Lean_shellMain___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__5 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__5_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_stdin"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__6 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__6_value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_shellMain___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__6_value),LEAN_SCALAR_PTR_LITERAL(37, 142, 62, 167, 41, 238, 22, 79)}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__7 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__7_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "lean4"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__8 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__8_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__9;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__10;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unknown language '"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__11 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__11_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "<stdin>"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__12 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__12_value;
LEAN_EXPORT lean_object* lean_shell_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_decodeLossyUTF8___boxed(lean_object* v_a_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lean_decode_lossy_utf8(v_a_2_);
lean_dec_ref(v_a_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_runMain___boxed(lean_object* v_env_8_, lean_object* v_opts_9_, lean_object* v_args_10_, lean_object* v_a_00___x40___internal___hyg_11_){
_start:
{
uint32_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = lean_eval_main(v_env_8_, v_opts_9_, v_args_10_);
lean_dec(v_args_10_);
lean_dec_ref(v_opts_9_);
lean_dec_ref(v_env_8_);
v_r_13_ = lean_box_uint32(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initLLVM___boxed(lean_object* v_a_00___x40___internal___hyg_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lean_init_llvm();
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_emitLLVM___boxed(lean_object* v_env_21_, lean_object* v_modName_22_, lean_object* v_filepath_23_, lean_object* v_a_00___x40___internal___hyg_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lean_emit_llvm(v_env_21_, v_modName_22_, v_filepath_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_hasAddressSanitizer___boxed(lean_object* v_x_00___x40_Lean_Shell_2339721992____hygCtx___hyg_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = lean_internal_has_address_sanitizer(v_x_00___x40_Lean_Shell_2339721992____hygCtx___hyg_27_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_isMultiThread___boxed(lean_object* v_x_00___x40_Lean_Shell_3295292909____hygCtx___hyg_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = lean_internal_is_multi_thread(v_x_00___x40_Lean_Shell_3295292909____hygCtx___hyg_31_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_isDebug___boxed(lean_object* v_x_00___x40_Lean_Shell_97005966____hygCtx___hyg_35_){
_start:
{
uint8_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = lean_internal_is_debug(v_x_00___x40_Lean_Shell_97005966____hygCtx___hyg_35_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getBuildType___boxed(lean_object* v_x_00___x40_Lean_Shell_1721435280____hygCtx___hyg_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lean_internal_get_build_type(v_x_00___x40_Lean_Shell_1721435280____hygCtx___hyg_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultMaxMemory___boxed(lean_object* v_x_00___x40_Lean_Shell_1091001955____hygCtx___hyg_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lean_internal_get_default_max_memory(v_x_00___x40_Lean_Shell_1091001955____hygCtx___hyg_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setMaxMemory___boxed(lean_object* v_max_46_, lean_object* v_a_00___x40___internal___hyg_47_){
_start:
{
size_t v_max_boxed_48_; lean_object* v_res_49_; 
v_max_boxed_48_ = lean_unbox_usize(v_max_46_);
lean_dec(v_max_46_);
v_res_49_ = lean_internal_set_max_memory(v_max_boxed_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultMaxHeartbeat___boxed(lean_object* v_x_00___x40_Lean_Shell_2736094960____hygCtx___hyg_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = lean_internal_get_default_max_heartbeat(v_x_00___x40_Lean_Shell_2736094960____hygCtx___hyg_51_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setMaxHeartbeat___boxed(lean_object* v_max_55_, lean_object* v_a_00___x40___internal___hyg_56_){
_start:
{
size_t v_max_boxed_57_; lean_object* v_res_58_; 
v_max_boxed_57_ = lean_unbox_usize(v_max_55_);
lean_dec(v_max_55_);
v_res_58_ = lean_internal_set_max_heartbeat(v_max_boxed_57_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultVerbose___boxed(lean_object* v_x_00___x40_Lean_Shell_28281146____hygCtx___hyg_60_){
_start:
{
uint8_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = lean_internal_get_default_verbose(v_x_00___x40_Lean_Shell_28281146____hygCtx___hyg_60_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setExitOnPanic___boxed(lean_object* v_exit_65_, lean_object* v_a_00___x40___internal___hyg_66_){
_start:
{
uint8_t v_exit_boxed_67_; lean_object* v_res_68_; 
v_exit_boxed_67_ = lean_unbox(v_exit_65_);
v_res_68_ = lean_internal_set_exit_on_panic(v_exit_boxed_67_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setThreadStackSize___boxed(lean_object* v_sz_71_, lean_object* v_a_00___x40___internal___hyg_72_){
_start:
{
size_t v_sz_boxed_73_; lean_object* v_res_74_; 
v_sz_boxed_73_ = lean_unbox_usize(v_sz_71_);
lean_dec(v_sz_71_);
v_res_74_ = lean_internal_set_thread_stack_size(v_sz_boxed_73_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_enableDebug___boxed(lean_object* v_tag_77_, lean_object* v_a_00___x40___internal___hyg_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = lean_internal_enable_debug(v_tag_77_);
lean_dec_ref(v_tag_77_);
return v_res_79_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__1(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_81_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_82_ = l_Lean_version_specialDesc;
v___x_83_ = lean_string_dec_eq(v___x_82_, v___x_81_);
return v___x_83_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__3(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__2));
v___x_86_ = l_Lean_versionStringCore;
v___x_87_ = lean_string_append(v___x_86_, v___x_85_);
return v___x_87_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__4(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = l_Lean_version_specialDesc;
v___x_89_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shortVersionString___closed__3, &l___private_Lean_Shell_0__Lean_shortVersionString___closed__3_once, _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__3);
v___x_90_ = lean_string_append(v___x_89_, v___x_88_);
return v___x_90_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__6(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__5));
v___x_93_ = l_Lean_versionStringCore;
v___x_94_ = lean_string_append(v___x_93_, v___x_92_);
return v___x_94_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString(void){
_start:
{
uint8_t v___x_95_; 
v___x_95_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_shortVersionString___closed__1, &l___private_Lean_Shell_0__Lean_shortVersionString___closed__1_once, _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__1);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; 
v___x_96_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shortVersionString___closed__4, &l___private_Lean_Shell_0__Lean_shortVersionString___closed__4_once, _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__4);
return v___x_96_;
}
else
{
uint8_t v___x_97_; 
v___x_97_ = l_Lean_version_isRelease;
if (v___x_97_ == 0)
{
lean_object* v___x_98_; 
v___x_98_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shortVersionString___closed__6, &l___private_Lean_Shell_0__Lean_shortVersionString___closed__6_once, _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__6);
return v___x_98_;
}
else
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_versionStringCore;
return v___x_99_;
}
}
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__2(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_box(0);
v___x_103_ = lean_internal_get_build_type(v___x_102_);
return v___x_103_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__4(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_105_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_106_ = l_Lean_githash;
v___x_107_ = lean_string_dec_eq(v___x_106_, v___x_105_);
return v___x_107_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__6(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_109_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_110_ = l_System_Platform_target;
v___x_111_ = lean_string_dec_eq(v___x_110_, v___x_109_);
return v___x_111_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__7(void){
_start:
{
lean_object* v___x_112_; lean_object* v_ver_113_; lean_object* v___x_114_; 
v___x_112_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__1));
v_ver_113_ = l___private_Lean_Shell_0__Lean_shortVersionString;
v___x_114_ = lean_string_append(v_ver_113_, v___x_112_);
return v___x_114_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__8(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v_ver_117_; 
v___x_115_ = l_System_Platform_target;
v___x_116_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__7, &l___private_Lean_Shell_0__Lean_versionHeader___closed__7_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__7);
v_ver_117_ = lean_string_append(v___x_116_, v___x_115_);
return v_ver_117_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader(void){
_start:
{
lean_object* v_ver_119_; lean_object* v_ver_129_; lean_object* v_ver_135_; uint8_t v___x_136_; 
v_ver_135_ = l___private_Lean_Shell_0__Lean_shortVersionString;
v___x_136_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__6, &l___private_Lean_Shell_0__Lean_versionHeader___closed__6_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__6);
if (v___x_136_ == 0)
{
lean_object* v_ver_137_; 
v_ver_137_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__8, &l___private_Lean_Shell_0__Lean_versionHeader___closed__8_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__8);
v_ver_129_ = v_ver_137_;
goto v___jp_128_;
}
else
{
v_ver_129_ = v_ver_135_;
goto v___jp_128_;
}
v___jp_118_:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_120_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__0));
v___x_121_ = lean_string_append(v___x_120_, v_ver_119_);
lean_dec_ref(v_ver_119_);
v___x_122_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__1));
v___x_123_ = lean_string_append(v___x_121_, v___x_122_);
v___x_124_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__2, &l___private_Lean_Shell_0__Lean_versionHeader___closed__2_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__2);
v___x_125_ = lean_string_append(v___x_123_, v___x_124_);
v___x_126_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__3));
v___x_127_ = lean_string_append(v___x_125_, v___x_126_);
return v___x_127_;
}
v___jp_128_:
{
lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_130_ = l_Lean_githash;
v___x_131_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__4, &l___private_Lean_Shell_0__Lean_versionHeader___closed__4_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__4);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v_ver_134_; 
v___x_132_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__5));
lean_inc_ref(v_ver_129_);
v___x_133_ = lean_string_append(v_ver_129_, v___x_132_);
v_ver_134_ = lean_string_append(v___x_133_, v___x_130_);
v_ver_119_ = v_ver_134_;
goto v___jp_118_;
}
else
{
lean_inc_ref(v_ver_129_);
v_ver_119_ = v_ver_129_;
goto v___jp_118_;
}
}
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_featuresString___closed__0(void){
_start:
{
lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_138_ = lean_box(0);
v___x_139_ = lean_internal_has_llvm_backend(v___x_138_);
return v___x_139_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_featuresString(void){
_start:
{
uint8_t v___x_142_; 
v___x_142_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_featuresString___closed__0, &l___private_Lean_Shell_0__Lean_featuresString___closed__0_once, _init_l___private_Lean_Shell_0__Lean_featuresString___closed__0);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; 
v___x_143_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_featuresString___closed__1));
return v___x_143_;
}
else
{
lean_object* v___x_144_; 
v___x_144_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_featuresString___closed__2));
return v___x_144_;
}
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__16(void){
_start:
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = lean_box(0);
v___x_162_ = lean_internal_is_debug(v___x_161_);
return v___x_162_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__40(void){
_start:
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = lean_box(0);
v___x_187_ = lean_internal_is_multi_thread(v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHelp(uint8_t v_useStderr_192_){
_start:
{
lean_object* v___y_195_; lean_object* v___y_199_; lean_object* v_out_234_; 
if (v_useStderr_192_ == 0)
{
lean_object* v___x_290_; 
v___x_290_ = lean_get_stdout();
v_out_234_ = v___x_290_;
goto v___jp_233_;
}
else
{
lean_object* v___x_291_; 
v___x_291_ = lean_get_stderr();
v_out_234_ = v___x_291_;
goto v___jp_233_;
}
v___jp_194_:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__0));
v___x_197_ = l_IO_FS_Stream_putStrLn(v___y_195_, v___x_196_);
return v___x_197_;
}
v___jp_198_:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__1));
lean_inc_ref(v___y_199_);
v___x_201_ = l_IO_FS_Stream_putStrLn(v___y_199_, v___x_200_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v___x_202_; lean_object* v___x_203_; 
lean_dec_ref_known(v___x_201_, 1);
v___x_202_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__2));
lean_inc_ref(v___y_199_);
v___x_203_ = l_IO_FS_Stream_putStrLn(v___y_199_, v___x_202_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_dec_ref_known(v___x_203_, 1);
v___x_204_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__3));
lean_inc_ref(v___y_199_);
v___x_205_ = l_IO_FS_Stream_putStrLn(v___y_199_, v___x_204_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec_ref_known(v___x_205_, 1);
v___x_206_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__4));
lean_inc_ref(v___y_199_);
v___x_207_ = l_IO_FS_Stream_putStrLn(v___y_199_, v___x_206_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; 
lean_dec_ref_known(v___x_207_, 1);
v___x_208_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__5));
lean_inc_ref(v___y_199_);
v___x_209_ = l_IO_FS_Stream_putStrLn(v___y_199_, v___x_208_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; 
lean_dec_ref_known(v___x_209_, 1);
v___x_210_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__6));
lean_inc_ref(v___y_199_);
v___x_211_ = l_IO_FS_Stream_putStrLn(v___y_199_, v___x_210_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec_ref_known(v___x_211_, 1);
v___x_212_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__7));
lean_inc_ref(v___y_199_);
v___x_213_ = l_IO_FS_Stream_putStrLn(v___y_199_, v___x_212_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec_ref_known(v___x_213_, 1);
v___x_214_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__8));
lean_inc_ref(v___y_199_);
v___x_215_ = l_IO_FS_Stream_putStrLn(v___y_199_, v___x_214_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; 
lean_dec_ref_known(v___x_215_, 1);
v___x_216_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__9));
lean_inc_ref(v___y_199_);
v___x_217_ = l_IO_FS_Stream_putStrLn(v___y_199_, v___x_216_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; 
lean_dec_ref_known(v___x_217_, 1);
v___x_218_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__10));
lean_inc_ref(v___y_199_);
v___x_219_ = l_IO_FS_Stream_putStrLn(v___y_199_, v___x_218_);
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v___x_220_; lean_object* v___x_221_; 
lean_dec_ref_known(v___x_219_, 1);
v___x_220_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__11));
lean_inc_ref(v___y_199_);
v___x_221_ = l_IO_FS_Stream_putStrLn(v___y_199_, v___x_220_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v___x_222_; lean_object* v___x_223_; 
lean_dec_ref_known(v___x_221_, 1);
v___x_222_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__12));
lean_inc_ref(v___y_199_);
v___x_223_ = l_IO_FS_Stream_putStrLn(v___y_199_, v___x_222_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; 
lean_dec_ref_known(v___x_223_, 1);
v___x_224_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__13));
lean_inc_ref(v___y_199_);
v___x_225_ = l_IO_FS_Stream_putStrLn(v___y_199_, v___x_224_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; 
lean_dec_ref_known(v___x_225_, 1);
v___x_226_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__14));
lean_inc_ref(v___y_199_);
v___x_227_ = l_IO_FS_Stream_putStrLn(v___y_199_, v___x_226_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_dec_ref_known(v___x_227_, 1);
v___x_228_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__15));
lean_inc_ref(v___y_199_);
v___x_229_ = l_IO_FS_Stream_putStrLn(v___y_199_, v___x_228_);
if (lean_obj_tag(v___x_229_) == 0)
{
uint8_t v___x_230_; 
lean_dec_ref_known(v___x_229_, 1);
v___x_230_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__16, &l___private_Lean_Shell_0__Lean_displayHelp___closed__16_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__16);
if (v___x_230_ == 0)
{
v___y_195_ = v___y_199_;
goto v___jp_194_;
}
else
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__17));
lean_inc_ref(v___y_199_);
v___x_232_ = l_IO_FS_Stream_putStrLn(v___y_199_, v___x_231_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_dec_ref_known(v___x_232_, 1);
v___y_195_ = v___y_199_;
goto v___jp_194_;
}
else
{
lean_dec_ref(v___y_199_);
return v___x_232_;
}
}
}
else
{
lean_dec_ref(v___y_199_);
return v___x_229_;
}
}
else
{
lean_dec_ref(v___y_199_);
return v___x_227_;
}
}
else
{
lean_dec_ref(v___y_199_);
return v___x_225_;
}
}
else
{
lean_dec_ref(v___y_199_);
return v___x_223_;
}
}
else
{
lean_dec_ref(v___y_199_);
return v___x_221_;
}
}
else
{
lean_dec_ref(v___y_199_);
return v___x_219_;
}
}
else
{
lean_dec_ref(v___y_199_);
return v___x_217_;
}
}
else
{
lean_dec_ref(v___y_199_);
return v___x_215_;
}
}
else
{
lean_dec_ref(v___y_199_);
return v___x_213_;
}
}
else
{
lean_dec_ref(v___y_199_);
return v___x_211_;
}
}
else
{
lean_dec_ref(v___y_199_);
return v___x_209_;
}
}
else
{
lean_dec_ref(v___y_199_);
return v___x_207_;
}
}
else
{
lean_dec_ref(v___y_199_);
return v___x_205_;
}
}
else
{
lean_dec_ref(v___y_199_);
return v___x_203_;
}
}
else
{
lean_dec_ref(v___y_199_);
return v___x_201_;
}
}
v___jp_233_:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = l___private_Lean_Shell_0__Lean_versionHeader;
lean_inc_ref(v_out_234_);
v___x_236_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_235_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec_ref_known(v___x_236_, 1);
v___x_237_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__18));
lean_inc_ref(v_out_234_);
v___x_238_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_237_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
lean_dec_ref_known(v___x_238_, 1);
v___x_239_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__19));
lean_inc_ref(v_out_234_);
v___x_240_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_239_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v___x_241_; lean_object* v___x_242_; 
lean_dec_ref_known(v___x_240_, 1);
v___x_241_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__20));
lean_inc_ref(v_out_234_);
v___x_242_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_241_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec_ref_known(v___x_242_, 1);
v___x_243_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__21));
lean_inc_ref(v_out_234_);
v___x_244_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_243_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v___x_245_; lean_object* v___x_246_; 
lean_dec_ref_known(v___x_244_, 1);
v___x_245_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__22));
lean_inc_ref(v_out_234_);
v___x_246_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_245_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec_ref_known(v___x_246_, 1);
v___x_247_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__23));
lean_inc_ref(v_out_234_);
v___x_248_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_247_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec_ref_known(v___x_248_, 1);
v___x_249_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__24));
lean_inc_ref(v_out_234_);
v___x_250_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_249_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec_ref_known(v___x_250_, 1);
v___x_251_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__25));
lean_inc_ref(v_out_234_);
v___x_252_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_251_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec_ref_known(v___x_252_, 1);
v___x_253_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__26));
lean_inc_ref(v_out_234_);
v___x_254_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_253_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec_ref_known(v___x_254_, 1);
v___x_255_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__27));
lean_inc_ref(v_out_234_);
v___x_256_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_255_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec_ref_known(v___x_256_, 1);
v___x_257_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__28));
lean_inc_ref(v_out_234_);
v___x_258_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_257_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec_ref_known(v___x_258_, 1);
v___x_259_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__29));
lean_inc_ref(v_out_234_);
v___x_260_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_259_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; 
lean_dec_ref_known(v___x_260_, 1);
v___x_261_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__30));
lean_inc_ref(v_out_234_);
v___x_262_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_261_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec_ref_known(v___x_262_, 1);
v___x_263_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__31));
lean_inc_ref(v_out_234_);
v___x_264_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_263_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec_ref_known(v___x_264_, 1);
v___x_265_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__32));
lean_inc_ref(v_out_234_);
v___x_266_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_265_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec_ref_known(v___x_266_, 1);
v___x_267_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__33));
lean_inc_ref(v_out_234_);
v___x_268_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_267_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; 
lean_dec_ref_known(v___x_268_, 1);
v___x_269_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__34));
lean_inc_ref(v_out_234_);
v___x_270_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_269_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec_ref_known(v___x_270_, 1);
v___x_271_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__35));
lean_inc_ref(v_out_234_);
v___x_272_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_271_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; 
lean_dec_ref_known(v___x_272_, 1);
v___x_273_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__36));
lean_inc_ref(v_out_234_);
v___x_274_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_273_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; 
lean_dec_ref_known(v___x_274_, 1);
v___x_275_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__37));
lean_inc_ref(v_out_234_);
v___x_276_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_275_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; 
lean_dec_ref_known(v___x_276_, 1);
v___x_277_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__38));
lean_inc_ref(v_out_234_);
v___x_278_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_277_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; 
lean_dec_ref_known(v___x_278_, 1);
v___x_279_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__39));
lean_inc_ref(v_out_234_);
v___x_280_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_279_);
if (lean_obj_tag(v___x_280_) == 0)
{
uint8_t v___x_281_; 
lean_dec_ref_known(v___x_280_, 1);
v___x_281_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__40, &l___private_Lean_Shell_0__Lean_displayHelp___closed__40_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__40);
if (v___x_281_ == 0)
{
v___y_199_ = v_out_234_;
goto v___jp_198_;
}
else
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__41));
lean_inc_ref(v_out_234_);
v___x_283_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_282_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; 
lean_dec_ref_known(v___x_283_, 1);
v___x_284_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__42));
lean_inc_ref(v_out_234_);
v___x_285_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_284_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec_ref_known(v___x_285_, 1);
v___x_286_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__43));
lean_inc_ref(v_out_234_);
v___x_287_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_286_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v___x_288_; lean_object* v___x_289_; 
lean_dec_ref_known(v___x_287_, 1);
v___x_288_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__44));
lean_inc_ref(v_out_234_);
v___x_289_ = l_IO_FS_Stream_putStrLn(v_out_234_, v___x_288_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_dec_ref_known(v___x_289_, 1);
v___y_199_ = v_out_234_;
goto v___jp_198_;
}
else
{
lean_dec_ref(v_out_234_);
return v___x_289_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_287_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_285_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_283_;
}
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_280_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_278_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_276_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_274_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_272_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_270_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_268_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_266_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_264_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_262_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_260_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_258_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_256_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_254_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_252_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_250_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_248_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_246_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_244_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_242_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_240_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_238_;
}
}
else
{
lean_dec_ref(v_out_234_);
return v___x_236_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHelp___boxed(lean_object* v_useStderr_292_, lean_object* v_a_293_){
_start:
{
uint8_t v_useStderr_boxed_294_; lean_object* v_res_295_; 
v_useStderr_boxed_294_ = lean_unbox(v_useStderr_292_);
v_res_295_ = l___private_Lean_Shell_0__Lean_displayHelp(v_useStderr_boxed_294_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(uint8_t v_x_296_){
_start:
{
switch(v_x_296_)
{
case 0:
{
lean_object* v___x_297_; 
v___x_297_ = lean_unsigned_to_nat(0u);
return v___x_297_;
}
case 1:
{
lean_object* v___x_298_; 
v___x_298_ = lean_unsigned_to_nat(1u);
return v___x_298_;
}
default: 
{
lean_object* v___x_299_; 
v___x_299_ = lean_unsigned_to_nat(2u);
return v___x_299_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx___boxed(lean_object* v_x_300_){
_start:
{
uint8_t v_x_boxed_301_; lean_object* v_res_302_; 
v_x_boxed_301_ = lean_unbox(v_x_300_);
v_res_302_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(v_x_boxed_301_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg(lean_object* v_k_303_){
_start:
{
lean_inc(v_k_303_);
return v_k_303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg___boxed(lean_object* v_k_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg(v_k_304_);
lean_dec(v_k_304_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim(lean_object* v_motive_306_, lean_object* v_ctorIdx_307_, uint8_t v_t_308_, lean_object* v_h_309_, lean_object* v_k_310_){
_start:
{
lean_inc(v_k_310_);
return v_k_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___boxed(lean_object* v_motive_311_, lean_object* v_ctorIdx_312_, lean_object* v_t_313_, lean_object* v_h_314_, lean_object* v_k_315_){
_start:
{
uint8_t v_t_boxed_316_; lean_object* v_res_317_; 
v_t_boxed_316_ = lean_unbox(v_t_313_);
v_res_317_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim(v_motive_311_, v_ctorIdx_312_, v_t_boxed_316_, v_h_314_, v_k_315_);
lean_dec(v_k_315_);
lean_dec(v_ctorIdx_312_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg(lean_object* v_frontend_318_){
_start:
{
lean_inc(v_frontend_318_);
return v_frontend_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg___boxed(lean_object* v_frontend_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg(v_frontend_319_);
lean_dec(v_frontend_319_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim(lean_object* v_motive_321_, uint8_t v_t_322_, lean_object* v_h_323_, lean_object* v_frontend_324_){
_start:
{
lean_inc(v_frontend_324_);
return v_frontend_324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___boxed(lean_object* v_motive_325_, lean_object* v_t_326_, lean_object* v_h_327_, lean_object* v_frontend_328_){
_start:
{
uint8_t v_t_boxed_329_; lean_object* v_res_330_; 
v_t_boxed_329_ = lean_unbox(v_t_326_);
v_res_330_ = l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim(v_motive_325_, v_t_boxed_329_, v_h_327_, v_frontend_328_);
lean_dec(v_frontend_328_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg(lean_object* v_watchdog_331_){
_start:
{
lean_inc(v_watchdog_331_);
return v_watchdog_331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg___boxed(lean_object* v_watchdog_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg(v_watchdog_332_);
lean_dec(v_watchdog_332_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim(lean_object* v_motive_334_, uint8_t v_t_335_, lean_object* v_h_336_, lean_object* v_watchdog_337_){
_start:
{
lean_inc(v_watchdog_337_);
return v_watchdog_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___boxed(lean_object* v_motive_338_, lean_object* v_t_339_, lean_object* v_h_340_, lean_object* v_watchdog_341_){
_start:
{
uint8_t v_t_boxed_342_; lean_object* v_res_343_; 
v_t_boxed_342_ = lean_unbox(v_t_339_);
v_res_343_ = l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim(v_motive_338_, v_t_boxed_342_, v_h_340_, v_watchdog_341_);
lean_dec(v_watchdog_341_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg(lean_object* v_worker_344_){
_start:
{
lean_inc(v_worker_344_);
return v_worker_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg___boxed(lean_object* v_worker_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg(v_worker_345_);
lean_dec(v_worker_345_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim(lean_object* v_motive_347_, uint8_t v_t_348_, lean_object* v_h_349_, lean_object* v_worker_350_){
_start:
{
lean_inc(v_worker_350_);
return v_worker_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___boxed(lean_object* v_motive_351_, lean_object* v_t_352_, lean_object* v_h_353_, lean_object* v_worker_354_){
_start:
{
uint8_t v_t_boxed_355_; lean_object* v_res_356_; 
v_t_boxed_355_ = lean_unbox(v_t_352_);
v_res_356_ = l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim(v_motive_351_, v_t_boxed_355_, v_h_353_, v_worker_354_);
lean_dec(v_worker_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(lean_object* v_name_357_, lean_object* v_decl_358_, lean_object* v_ref_359_){
_start:
{
lean_object* v_defValue_361_; lean_object* v_descr_362_; lean_object* v_deprecation_x3f_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_defValue_361_ = lean_ctor_get(v_decl_358_, 0);
v_descr_362_ = lean_ctor_get(v_decl_358_, 1);
v_deprecation_x3f_363_ = lean_ctor_get(v_decl_358_, 2);
lean_inc(v_defValue_361_);
v___x_364_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_364_, 0, v_defValue_361_);
lean_inc(v_deprecation_x3f_363_);
lean_inc_ref(v_descr_362_);
lean_inc_n(v_name_357_, 2);
v___x_365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_365_, 0, v_name_357_);
lean_ctor_set(v___x_365_, 1, v_ref_359_);
lean_ctor_set(v___x_365_, 2, v___x_364_);
lean_ctor_set(v___x_365_, 3, v_descr_362_);
lean_ctor_set(v___x_365_, 4, v_deprecation_x3f_363_);
v___x_366_ = lean_register_option(v_name_357_, v___x_365_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_374_; 
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_374_ == 0)
{
lean_object* v_unused_375_; 
v_unused_375_ = lean_ctor_get(v___x_366_, 0);
lean_dec(v_unused_375_);
v___x_368_ = v___x_366_;
v_isShared_369_ = v_isSharedCheck_374_;
goto v_resetjp_367_;
}
else
{
lean_dec(v___x_366_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_374_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_372_; 
lean_inc(v_defValue_361_);
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v_name_357_);
lean_ctor_set(v___x_370_, 1, v_defValue_361_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_370_);
v___x_372_ = v___x_368_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec(v_name_357_);
v_a_376_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_366_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_366_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0___boxed(lean_object* v_name_384_, lean_object* v_decl_385_, lean_object* v_ref_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v_name_384_, v_decl_385_, v_ref_386_);
lean_dec_ref(v_decl_385_);
return v_res_388_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_box(0);
v___x_393_ = lean_internal_get_default_max_memory(v___x_392_);
return v___x_393_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_394_ = lean_box(0);
v___x_395_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_396_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
v___x_397_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set(v___x_397_, 1, v___x_395_);
lean_ctor_set(v___x_397_, 2, v___x_394_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_421_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_));
v___x_422_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
v___x_423_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__13_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_));
v___x_424_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v___x_421_, v___x_422_, v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2____boxed(lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
return v_res_426_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_box(0);
v___x_431_ = lean_internal_get_default_max_heartbeat(v___x_430_);
return v___x_431_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_432_ = lean_box(0);
v___x_433_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_434_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
v___x_435_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v___x_433_);
lean_ctor_set(v___x_435_, 2, v___x_432_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_440_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_));
v___x_441_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
v___x_442_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_));
v___x_443_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v___x_440_, v___x_441_, v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2____boxed(lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_();
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(lean_object* v_name_446_, lean_object* v_decl_447_, lean_object* v_ref_448_){
_start:
{
lean_object* v_defValue_450_; lean_object* v_descr_451_; lean_object* v_deprecation_x3f_452_; lean_object* v___x_453_; uint8_t v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v_defValue_450_ = lean_ctor_get(v_decl_447_, 0);
v_descr_451_ = lean_ctor_get(v_decl_447_, 1);
v_deprecation_x3f_452_ = lean_ctor_get(v_decl_447_, 2);
v___x_453_ = lean_alloc_ctor(1, 0, 1);
v___x_454_ = lean_unbox(v_defValue_450_);
lean_ctor_set_uint8(v___x_453_, 0, v___x_454_);
lean_inc(v_deprecation_x3f_452_);
lean_inc_ref(v_descr_451_);
lean_inc_n(v_name_446_, 2);
v___x_455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_455_, 0, v_name_446_);
lean_ctor_set(v___x_455_, 1, v_ref_448_);
lean_ctor_set(v___x_455_, 2, v___x_453_);
lean_ctor_set(v___x_455_, 3, v_descr_451_);
lean_ctor_set(v___x_455_, 4, v_deprecation_x3f_452_);
v___x_456_ = lean_register_option(v_name_446_, v___x_455_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_464_; 
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; 
v_unused_465_ = lean_ctor_get(v___x_456_, 0);
lean_dec(v_unused_465_);
v___x_458_ = v___x_456_;
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
else
{
lean_dec(v___x_456_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; lean_object* v___x_462_; 
lean_inc(v_defValue_450_);
v___x_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_460_, 0, v_name_446_);
lean_ctor_set(v___x_460_, 1, v_defValue_450_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v___x_460_);
v___x_462_ = v___x_458_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_dec(v_name_446_);
v_a_466_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_456_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_456_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0___boxed(lean_object* v_name_474_, lean_object* v_decl_475_, lean_object* v_ref_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(v_name_474_, v_decl_475_, v_ref_476_);
lean_dec_ref(v_decl_475_);
return v_res_478_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = lean_box(0);
v___x_483_ = lean_internal_get_default_verbose(v___x_482_);
return v___x_483_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_484_ = lean_box(0);
v___x_485_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_486_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_);
v___x_487_ = lean_box(v___x_486_);
v___x_488_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v___x_485_);
lean_ctor_set(v___x_488_, 2, v___x_484_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_493_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_));
v___x_494_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_);
v___x_495_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_));
v___x_496_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(v___x_493_, v___x_494_, v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2____boxed(lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_();
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getOptionOverrides___boxed(lean_object* v_x_00___x40_Lean_Shell_1930944040____hygCtx___hyg_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = lean_internal_get_option_overrides(v_x_00___x40_Lean_Shell_1930944040____hygCtx___hyg_500_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getBelieverTrustLevel___boxed(lean_object* v_x_00___x40_Lean_Shell_1075205639____hygCtx___hyg_503_){
_start:
{
uint32_t v_res_504_; lean_object* v_r_505_; 
v_res_504_ = lean_internal_get_believer_trust_level(v_x_00___x40_Lean_Shell_1075205639____hygCtx___hyg_503_);
v_r_505_ = lean_box_uint32(v_res_504_);
return v_r_505_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0(void){
_start:
{
lean_object* v___x_506_; uint32_t v___x_507_; 
v___x_506_ = lean_box(0);
v___x_507_ = lean_internal_get_believer_trust_level(v___x_506_);
return v___x_507_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1(void){
_start:
{
uint32_t v___x_508_; uint32_t v___x_509_; uint32_t v___x_510_; 
v___x_508_ = 1;
v___x_509_ = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0, &l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0_once, _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0);
v___x_510_ = lean_uint32_add(v___x_509_, v___x_508_);
return v___x_510_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel(void){
_start:
{
uint32_t v___x_511_; 
v___x_511_ = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1, &l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1_once, _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1);
return v___x_511_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0(void){
_start:
{
lean_object* v___x_512_; uint32_t v___x_513_; 
v___x_512_ = lean_box(0);
v___x_513_ = lean_internal_get_hardware_concurrency(v___x_512_);
return v___x_513_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultNumThreads(void){
_start:
{
uint8_t v___x_514_; 
v___x_514_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__40, &l___private_Lean_Shell_0__Lean_displayHelp___closed__40_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__40);
if (v___x_514_ == 0)
{
uint32_t v___x_515_; 
v___x_515_ = 0;
return v___x_515_;
}
else
{
uint32_t v___x_516_; 
v___x_516_ = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0, &l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0_once, _init_l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0);
return v___x_516_;
}
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__1(void){
_start:
{
lean_object* v___x_519_; uint32_t v___x_520_; uint32_t v___x_521_; uint8_t v___x_522_; uint8_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_519_ = lean_box(0);
v___x_520_ = l___private_Lean_Shell_0__Lean_defaultNumThreads;
v___x_521_ = l___private_Lean_Shell_0__Lean_defaultTrustLevel;
v___x_522_ = 0;
v___x_523_ = 0;
v___x_524_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__0));
v___x_525_ = l_Lean_Options_empty;
v___x_526_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v___x_526_, 0, v___x_525_);
lean_ctor_set(v___x_526_, 1, v___x_524_);
lean_ctor_set(v___x_526_, 2, v___x_525_);
lean_ctor_set(v___x_526_, 3, v___x_519_);
lean_ctor_set(v___x_526_, 4, v___x_519_);
lean_ctor_set(v___x_526_, 5, v___x_519_);
lean_ctor_set(v___x_526_, 6, v___x_519_);
lean_ctor_set(v___x_526_, 7, v___x_519_);
lean_ctor_set(v___x_526_, 8, v___x_519_);
lean_ctor_set(v___x_526_, 9, v___x_524_);
lean_ctor_set(v___x_526_, 10, v___x_519_);
lean_ctor_set(v___x_526_, 11, v___x_519_);
lean_ctor_set(v___x_526_, 12, v___x_519_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*13 + 8, v___x_523_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*13 + 9, v___x_522_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*13 + 10, v___x_522_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*13 + 11, v___x_522_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*13 + 12, v___x_522_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*13 + 13, v___x_522_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*13 + 14, v___x_522_);
lean_ctor_set_uint32(v___x_526_, sizeof(void*)*13, v___x_521_);
lean_ctor_set_uint32(v___x_526_, sizeof(void*)*13 + 4, v___x_520_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*13 + 15, v___x_522_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*13 + 16, v___x_522_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*13 + 17, v___x_522_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___redArg(){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__1, &l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__1_once, _init_l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__1);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___boxed(lean_object* v___dummy_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l___private_Lean_Shell_0__Lean_mkShellOptions___redArg();
return v_res_530_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0(void){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l___private_Lean_Shell_0__Lean_mkShellOptions___redArg();
return v___x_531_;
}
}
LEAN_EXPORT lean_object* lean_shell_options_mk(lean_object* v_x_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0, &l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0_once, _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0);
return v___x_533_;
}
}
LEAN_EXPORT uint8_t lean_shell_options_get_run(lean_object* v_opts_534_){
_start:
{
uint8_t v_run_535_; 
v_run_535_ = lean_ctor_get_uint8(v_opts_534_, sizeof(void*)*13 + 17);
lean_dec_ref(v_opts_534_);
return v_run_535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getRun___boxed(lean_object* v_opts_536_){
_start:
{
uint8_t v_res_537_; lean_object* v_r_538_; 
v_res_537_ = lean_shell_options_get_run(v_opts_536_);
v_r_538_ = lean_box(v_res_537_);
return v_r_538_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(lean_object* v_opts_539_, lean_object* v_opt_540_){
_start:
{
lean_object* v_name_541_; lean_object* v_defValue_542_; lean_object* v_map_543_; lean_object* v___x_544_; 
v_name_541_ = lean_ctor_get(v_opt_540_, 0);
v_defValue_542_ = lean_ctor_get(v_opt_540_, 1);
v_map_543_ = lean_ctor_get(v_opts_539_, 0);
v___x_544_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_543_, v_name_541_);
if (lean_obj_tag(v___x_544_) == 0)
{
uint8_t v___x_545_; 
v___x_545_ = lean_unbox(v_defValue_542_);
return v___x_545_;
}
else
{
lean_object* v_val_546_; 
v_val_546_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_val_546_);
lean_dec_ref_known(v___x_544_, 1);
if (lean_obj_tag(v_val_546_) == 1)
{
uint8_t v_v_547_; 
v_v_547_ = lean_ctor_get_uint8(v_val_546_, 0);
lean_dec_ref_known(v_val_546_, 0);
return v_v_547_;
}
else
{
uint8_t v___x_548_; 
lean_dec(v_val_546_);
v___x_548_ = lean_unbox(v_defValue_542_);
return v___x_548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0___boxed(lean_object* v_opts_549_, lean_object* v_opt_550_){
_start:
{
uint8_t v_res_551_; lean_object* v_r_552_; 
v_res_551_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v_opts_549_, v_opt_550_);
lean_dec_ref(v_opt_550_);
lean_dec_ref(v_opts_549_);
v_r_552_ = lean_box(v_res_551_);
return v_r_552_;
}
}
LEAN_EXPORT uint8_t lean_shell_options_get_profiler(lean_object* v_opts_553_){
_start:
{
lean_object* v_leanOpts_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v_leanOpts_554_ = lean_ctor_get(v_opts_553_, 0);
lean_inc_ref(v_leanOpts_554_);
lean_dec_ref(v_opts_553_);
v___x_555_ = l_Lean_profiler;
v___x_556_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v_leanOpts_554_, v___x_555_);
lean_dec_ref(v_leanOpts_554_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getProfiler___boxed(lean_object* v_opts_557_){
_start:
{
uint8_t v_res_558_; lean_object* v_r_559_; 
v_res_558_ = lean_shell_options_get_profiler(v_opts_557_);
v_r_559_ = lean_box(v_res_558_);
return v_r_559_;
}
}
LEAN_EXPORT uint32_t lean_shell_options_get_num_threads(lean_object* v_opts_560_){
_start:
{
uint32_t v_numThreads_561_; 
v_numThreads_561_ = lean_ctor_get_uint32(v_opts_560_, sizeof(void*)*13 + 4);
lean_dec_ref(v_opts_560_);
return v_numThreads_561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getNumThreads___boxed(lean_object* v_opts_562_){
_start:
{
uint32_t v_res_563_; lean_object* v_r_564_; 
v_res_563_ = lean_shell_options_get_num_threads(v_opts_562_);
v_r_564_ = lean_box_uint32(v_res_563_);
return v_r_564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_checkOptArg(lean_object* v_optName_567_, lean_object* v_optArg_x3f_568_){
_start:
{
if (lean_obj_tag(v_optArg_x3f_568_) == 1)
{
lean_object* v_val_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
v_val_570_ = lean_ctor_get(v_optArg_x3f_568_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v_optArg_x3f_568_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v_optArg_x3f_568_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_val_570_);
lean_dec(v_optArg_x3f_568_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set_tag(v___x_572_, 0);
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_val_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec(v_optArg_x3f_568_);
v___x_578_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__0));
v___x_579_ = lean_string_append(v___x_578_, v_optName_567_);
v___x_580_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__1));
v___x_581_ = lean_string_append(v___x_579_, v___x_580_);
v___x_582_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
v___x_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
return v___x_583_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_checkOptArg___boxed(lean_object* v_optName_584_, lean_object* v_optArg_x3f_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l___private_Lean_Shell_0__Lean_checkOptArg(v_optName_584_, v_optArg_x3f_585_);
lean_dec_ref(v_optName_584_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0(lean_object* v_o_591_, lean_object* v_k_592_, lean_object* v_v_593_){
_start:
{
lean_object* v_map_594_; uint8_t v_hasTrace_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_609_; 
v_map_594_ = lean_ctor_get(v_o_591_, 0);
v_hasTrace_595_ = lean_ctor_get_uint8(v_o_591_, sizeof(void*)*1);
v_isSharedCheck_609_ = !lean_is_exclusive(v_o_591_);
if (v_isSharedCheck_609_ == 0)
{
v___x_597_ = v_o_591_;
v_isShared_598_ = v_isSharedCheck_609_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_map_594_);
lean_dec(v_o_591_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_609_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_599_, 0, v_v_593_);
lean_inc(v_k_592_);
v___x_600_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_592_, v___x_599_, v_map_594_);
if (v_hasTrace_595_ == 0)
{
lean_object* v___x_601_; uint8_t v___x_602_; lean_object* v___x_604_; 
v___x_601_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_602_ = l_Lean_Name_isPrefixOf(v___x_601_, v_k_592_);
lean_dec(v_k_592_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_600_);
v___x_604_ = v___x_597_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_600_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_ctor_set_uint8(v___x_604_, sizeof(void*)*1, v___x_602_);
return v___x_604_;
}
}
else
{
lean_object* v___x_607_; 
lean_dec(v_k_592_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_600_);
v___x_607_ = v___x_597_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_600_);
lean_ctor_set_uint8(v_reuseFailAlloc_608_, sizeof(void*)*1, v_hasTrace_595_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(lean_object* v___x_610_, lean_object* v_arg_611_, lean_object* v_a_612_, lean_object* v_b_613_){
_start:
{
uint8_t v_decide_614_; 
v_decide_614_ = lean_nat_dec_eq(v_a_612_, v___x_610_);
if (v_decide_614_ == 0)
{
uint32_t v___x_615_; uint32_t v___x_616_; uint8_t v___x_617_; 
v___x_615_ = lean_string_utf8_get_fast(v_arg_611_, v_a_612_);
v___x_616_ = 61;
v___x_617_ = lean_uint32_dec_eq(v___x_615_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_box(0);
v___x_619_ = lean_string_utf8_next_fast(v_arg_611_, v_a_612_);
lean_dec(v_a_612_);
v_a_612_ = v___x_619_;
v_b_613_ = v___x_618_;
goto _start;
}
else
{
lean_object* v___x_621_; 
v___x_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_621_, 0, v_a_612_);
return v___x_621_;
}
}
else
{
lean_dec(v_a_612_);
lean_inc(v_b_613_);
return v_b_613_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg___boxed(lean_object* v___x_622_, lean_object* v_arg_623_, lean_object* v_a_624_, lean_object* v_b_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_622_, v_arg_623_, v_a_624_, v_b_625_);
lean_dec(v_b_625_);
lean_dec_ref(v_arg_623_);
lean_dec(v___x_622_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_setConfigOption(lean_object* v_opts_630_, lean_object* v_arg_631_){
_start:
{
lean_object* v___y_634_; lean_object* v_searcher_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v_searcher_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = lean_string_utf8_byte_size(v_arg_631_);
v___x_667_ = lean_box(0);
v___x_668_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_666_, v_arg_631_, v_searcher_665_, v___x_667_);
if (lean_obj_tag(v___x_668_) == 0)
{
v___y_634_ = v___x_666_;
goto v___jp_633_;
}
else
{
lean_object* v_val_669_; 
v_val_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_val_669_);
lean_dec_ref_known(v___x_668_, 1);
v___y_634_ = v_val_669_;
goto v___jp_633_;
}
v___jp_633_:
{
lean_object* v___x_635_; uint8_t v_decide_636_; 
v___x_635_ = lean_string_utf8_byte_size(v_arg_631_);
v_decide_636_ = lean_nat_dec_eq(v___y_634_, v___x_635_);
if (v_decide_636_ == 0)
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v_name_639_; lean_object* v___x_640_; lean_object* v_val_641_; lean_object* v___x_642_; 
v___x_637_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_634_);
lean_inc_ref(v_arg_631_);
v___x_638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_638_, 0, v_arg_631_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
lean_ctor_set(v___x_638_, 2, v___y_634_);
v_name_639_ = l_String_Slice_toName(v___x_638_);
lean_dec_ref_known(v___x_638_, 3);
v___x_640_ = lean_string_utf8_next_fast(v_arg_631_, v___y_634_);
lean_dec(v___y_634_);
v_val_641_ = lean_string_utf8_extract_fast(v_arg_631_, v___x_640_, v___x_635_);
lean_dec_ref(v_arg_631_);
v___x_642_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_654_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_654_ == 0)
{
v___x_645_ = v___x_642_;
v_isShared_646_ = v_isSharedCheck_654_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_642_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_654_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; 
v___x_647_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_643_, v_name_639_);
lean_dec(v_a_643_);
if (lean_obj_tag(v___x_647_) == 1)
{
lean_object* v_val_648_; lean_object* v___x_649_; 
lean_del_object(v___x_645_);
v_val_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_val_648_);
lean_dec_ref_known(v___x_647_, 1);
v___x_649_ = l_Lean_Language_Lean_setOption(v_opts_630_, v_val_648_, v_name_639_, v_val_641_);
return v___x_649_;
}
else
{
lean_object* v___x_650_; lean_object* v___x_652_; 
lean_dec(v___x_647_);
v___x_650_ = l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0(v_opts_630_, v_name_639_, v_val_641_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v___x_650_);
v___x_652_ = v___x_645_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_dec_ref(v_val_641_);
lean_dec(v_name_639_);
lean_dec_ref(v_opts_630_);
v_a_655_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_642_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_642_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
else
{
lean_object* v___x_663_; lean_object* v___x_664_; 
lean_dec(v___y_634_);
lean_dec_ref(v_arg_631_);
lean_dec_ref(v_opts_630_);
v___x_663_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_setConfigOption___closed__1));
v___x_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
return v___x_664_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_setConfigOption___boxed(lean_object* v_opts_670_, lean_object* v_arg_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_opts_670_, v_arg_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(lean_object* v___x_674_, lean_object* v___x_675_, lean_object* v_arg_676_, lean_object* v_inst_677_, lean_object* v_R_678_, lean_object* v_a_679_, lean_object* v_b_680_, lean_object* v_c_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_674_, v_arg_676_, v_a_679_, v_b_680_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___boxed(lean_object* v___x_683_, lean_object* v___x_684_, lean_object* v_arg_685_, lean_object* v_inst_686_, lean_object* v_R_687_, lean_object* v_a_688_, lean_object* v_b_689_, lean_object* v_c_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(v___x_683_, v___x_684_, v_arg_685_, v_inst_686_, v_R_687_, v_a_688_, v_b_689_, v_c_690_);
lean_dec(v_b_689_);
lean_dec_ref(v_arg_685_);
lean_dec_ref(v___x_684_);
lean_dec(v___x_683_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(lean_object* v_msg_693_){
_start:
{
lean_object* v___f_695_; lean_object* v___x_696_; 
v___f_695_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_696_ = l_IO_eprint___redArg(v___f_695_, v_msg_693_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_696_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_696_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
else
{
lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_712_; 
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_712_ == 0)
{
lean_object* v_unused_713_; 
v_unused_713_ = lean_ctor_get(v___x_696_, 0);
lean_dec(v_unused_713_);
v___x_706_ = v___x_696_;
v_isShared_707_ = v_isSharedCheck_712_;
goto v_resetjp_705_;
}
else
{
lean_dec(v___x_696_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_712_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_708_ = lean_box(0);
if (v_isShared_707_ == 0)
{
lean_ctor_set_tag(v___x_706_, 0);
lean_ctor_set(v___x_706_, 0, v___x_708_);
v___x_710_ = v___x_706_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___boxed(lean_object* v_msg_714_, lean_object* v_a_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(v_msg_714_);
return v_res_716_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_719_; lean_object* v___x_720_; 
v___x_719_ = 1;
v___x_720_ = lean_box_uint32(v___x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(lean_object* v_x_721_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = lean_apply_1(v_x_721_, lean_box(0));
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_730_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_744_; lean_object* v___f_745_; lean_object* v___x_746_; 
v_a_739_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_730_, 1);
v___x_744_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___f_745_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_746_ = l_IO_eprint___redArg(v___f_745_, v___x_744_);
lean_dec_ref(v___x_746_);
goto v___jp_740_;
v___jp_740_:
{
lean_object* v___x_741_; lean_object* v___f_742_; lean_object* v___x_743_; 
v___x_741_ = lean_io_error_to_string(v_a_739_);
v___f_742_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_743_ = l_IO_eprint___redArg(v___f_742_, v___x_741_);
lean_dec_ref(v___x_743_);
goto v___jp_726_;
}
}
v___jp_723_:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
v___jp_726_:
{
lean_object* v___x_727_; lean_object* v___f_728_; lean_object* v___x_729_; 
v___x_727_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___f_728_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_729_ = l_IO_eprint___redArg(v___f_728_, v___x_727_);
lean_dec_ref(v___x_729_);
goto v___jp_723_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed(lean_object* v_x_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(v_x_747_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(lean_object* v_00_u03b1_750_, lean_object* v_x_751_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = lean_apply_1(v_x_751_, lean_box(0));
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_774_; lean_object* v___f_775_; lean_object* v___x_776_; 
v_a_769_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_760_, 1);
v___x_774_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___f_775_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_776_ = l_IO_eprint___redArg(v___f_775_, v___x_774_);
lean_dec_ref(v___x_776_);
goto v___jp_770_;
v___jp_770_:
{
lean_object* v___x_771_; lean_object* v___f_772_; lean_object* v___x_773_; 
v___x_771_ = lean_io_error_to_string(v_a_769_);
v___f_772_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_773_ = l_IO_eprint___redArg(v___f_772_, v___x_771_);
lean_dec_ref(v___x_773_);
goto v___jp_756_;
}
}
v___jp_753_:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
return v___x_755_;
}
v___jp_756_:
{
lean_object* v___x_757_; lean_object* v___f_758_; lean_object* v___x_759_; 
v___x_757_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___f_758_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_759_ = l_IO_eprint___redArg(v___f_758_, v___x_757_);
lean_dec_ref(v___x_759_);
goto v___jp_753_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___boxed(lean_object* v_00_u03b1_777_, lean_object* v_x_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(v_00_u03b1_777_, v_x_778_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(lean_object* v_opt_783_){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___f_792_; lean_object* v___x_793_; 
v___x_788_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__0));
v___x_789_ = lean_string_append(v___x_788_, v_opt_783_);
v___x_790_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
v___x_791_ = lean_string_append(v___x_789_, v___x_790_);
v___f_792_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_793_ = l_IO_eprint___redArg(v___f_792_, v___x_791_);
lean_dec_ref(v___x_793_);
goto v___jp_785_;
v___jp_785_:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
return v___x_787_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___boxed(lean_object* v_opt_794_, lean_object* v_a_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(v_opt_794_);
lean_dec_ref(v_opt_794_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(lean_object* v_opt_799_){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___f_808_; lean_object* v___x_809_; 
v___x_804_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__0));
v___x_805_ = lean_string_append(v___x_804_, v_opt_799_);
v___x_806_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__1));
v___x_807_ = lean_string_append(v___x_805_, v___x_806_);
v___f_808_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_809_ = l_IO_eprint___redArg(v___f_808_, v___x_807_);
lean_dec_ref(v___x_809_);
goto v___jp_801_;
v___jp_801_:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
return v___x_803_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___boxed(lean_object* v_opt_810_, lean_object* v_a_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(v_opt_810_);
lean_dec_ref(v_opt_810_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(lean_object* v_s_813_){
_start:
{
lean_object* v___x_815_; lean_object* v_putStr_816_; lean_object* v___x_817_; 
v___x_815_ = lean_get_stderr();
v_putStr_816_ = lean_ctor_get(v___x_815_, 4);
lean_inc_ref(v_putStr_816_);
lean_dec_ref(v___x_815_);
v___x_817_ = lean_apply_2(v_putStr_816_, v_s_813_, lean_box(0));
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0___boxed(lean_object* v_s_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v_s_818_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(lean_object* v_s_821_){
_start:
{
lean_object* v___x_823_; lean_object* v_putStr_824_; lean_object* v___x_825_; 
v___x_823_ = lean_get_stdout();
v_putStr_824_ = lean_ctor_get(v___x_823_, 4);
lean_inc_ref(v_putStr_824_);
lean_dec_ref(v___x_823_);
v___x_825_ = lean_apply_2(v_putStr_824_, v_s_821_, lean_box(0));
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5___boxed(lean_object* v_s_826_, lean_object* v_a_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v_s_826_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(lean_object* v_s_829_){
_start:
{
uint32_t v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = 10;
v___x_832_ = lean_string_push(v_s_829_, v___x_831_);
v___x_833_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3___boxed(lean_object* v_s_834_, lean_object* v_a_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v_s_834_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(lean_object* v_o_837_, lean_object* v_k_838_, uint8_t v_v_839_){
_start:
{
lean_object* v_map_840_; uint8_t v_hasTrace_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_855_; 
v_map_840_ = lean_ctor_get(v_o_837_, 0);
v_hasTrace_841_ = lean_ctor_get_uint8(v_o_837_, sizeof(void*)*1);
v_isSharedCheck_855_ = !lean_is_exclusive(v_o_837_);
if (v_isSharedCheck_855_ == 0)
{
v___x_843_ = v_o_837_;
v_isShared_844_ = v_isSharedCheck_855_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_map_840_);
lean_dec(v_o_837_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_855_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_845_, 0, v_v_839_);
lean_inc(v_k_838_);
v___x_846_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_838_, v___x_845_, v_map_840_);
if (v_hasTrace_841_ == 0)
{
lean_object* v___x_847_; uint8_t v___x_848_; lean_object* v___x_850_; 
v___x_847_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_848_ = l_Lean_Name_isPrefixOf(v___x_847_, v_k_838_);
lean_dec(v_k_838_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_846_);
v___x_850_ = v___x_843_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_846_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
lean_ctor_set_uint8(v___x_850_, sizeof(void*)*1, v___x_848_);
return v___x_850_;
}
}
else
{
lean_object* v___x_853_; 
lean_dec(v_k_838_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_846_);
v___x_853_ = v___x_843_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_846_);
lean_ctor_set_uint8(v_reuseFailAlloc_854_, sizeof(void*)*1, v_hasTrace_841_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1___boxed(lean_object* v_o_856_, lean_object* v_k_857_, lean_object* v_v_858_){
_start:
{
uint8_t v_v_boxed_859_; lean_object* v_res_860_; 
v_v_boxed_859_ = lean_unbox(v_v_858_);
v_res_860_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(v_o_856_, v_k_857_, v_v_boxed_859_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(lean_object* v_opts_861_, lean_object* v_opt_862_, uint8_t v_val_863_){
_start:
{
lean_object* v_name_864_; lean_object* v___x_865_; 
v_name_864_ = lean_ctor_get(v_opt_862_, 0);
lean_inc(v_name_864_);
lean_dec_ref(v_opt_862_);
v___x_865_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(v_opts_861_, v_name_864_, v_val_863_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1___boxed(lean_object* v_opts_866_, lean_object* v_opt_867_, lean_object* v_val_868_){
_start:
{
uint8_t v_val_boxed_869_; lean_object* v_res_870_; 
v_val_boxed_869_ = lean_unbox(v_val_868_);
v_res_870_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_opts_866_, v_opt_867_, v_val_boxed_869_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__3(lean_object* v_o_871_, lean_object* v_k_872_, lean_object* v_v_873_){
_start:
{
lean_object* v_map_874_; uint8_t v_hasTrace_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_889_; 
v_map_874_ = lean_ctor_get(v_o_871_, 0);
v_hasTrace_875_ = lean_ctor_get_uint8(v_o_871_, sizeof(void*)*1);
v_isSharedCheck_889_ = !lean_is_exclusive(v_o_871_);
if (v_isSharedCheck_889_ == 0)
{
v___x_877_ = v_o_871_;
v_isShared_878_ = v_isSharedCheck_889_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_map_874_);
lean_dec(v_o_871_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_889_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_879_, 0, v_v_873_);
lean_inc(v_k_872_);
v___x_880_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_872_, v___x_879_, v_map_874_);
if (v_hasTrace_875_ == 0)
{
lean_object* v___x_881_; uint8_t v___x_882_; lean_object* v___x_884_; 
v___x_881_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_882_ = l_Lean_Name_isPrefixOf(v___x_881_, v_k_872_);
lean_dec(v_k_872_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_880_);
v___x_884_ = v___x_877_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_880_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*1, v___x_882_);
return v___x_884_;
}
}
else
{
lean_object* v___x_887_; 
lean_dec(v_k_872_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_880_);
v___x_887_ = v___x_877_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_880_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, sizeof(void*)*1, v_hasTrace_875_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(lean_object* v_opts_890_, lean_object* v_opt_891_, lean_object* v_val_892_){
_start:
{
lean_object* v_name_893_; lean_object* v___x_894_; 
v_name_893_ = lean_ctor_get(v_opt_891_, 0);
lean_inc(v_name_893_);
lean_dec_ref(v_opt_891_);
v___x_894_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__3(v_opts_890_, v_name_893_, v_val_892_);
return v___x_894_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_923_ = l_System_Platform_numBits;
v___x_924_ = lean_unsigned_to_nat(2u);
v___x_925_ = lean_nat_pow(v___x_924_, v___x_923_);
return v___x_925_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1(void){
_start:
{
uint32_t v___x_935_; lean_object* v___x_936_; 
v___x_935_ = 0;
v___x_936_ = lean_box_uint32(v___x_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* lean_shell_options_process(lean_object* v_opts_937_, uint32_t v_opt_938_, lean_object* v_optArg_x3f_939_){
_start:
{
lean_object* v___y_1047_; lean_object* v___y_1105_; uint32_t v___x_1159_; uint8_t v___x_1160_; 
v___x_1159_ = 101;
v___x_1160_ = lean_uint32_dec_eq(v_opt_938_, v___x_1159_);
if (v___x_1160_ == 0)
{
uint32_t v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = 106;
v___x_1162_ = lean_uint32_dec_eq(v_opt_938_, v___x_1161_);
if (v___x_1162_ == 0)
{
uint32_t v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = 118;
v___x_1164_ = lean_uint32_dec_eq(v_opt_938_, v___x_1163_);
if (v___x_1164_ == 0)
{
uint32_t v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = 86;
v___x_1166_ = lean_uint32_dec_eq(v_opt_938_, v___x_1165_);
if (v___x_1166_ == 0)
{
uint32_t v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = 103;
v___x_1168_ = lean_uint32_dec_eq(v_opt_938_, v___x_1167_);
if (v___x_1168_ == 0)
{
uint32_t v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = 104;
v___x_1170_ = lean_uint32_dec_eq(v_opt_938_, v___x_1169_);
if (v___x_1170_ == 0)
{
uint32_t v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = 102;
v___x_1172_ = lean_uint32_dec_eq(v_opt_938_, v___x_1171_);
if (v___x_1172_ == 0)
{
uint32_t v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = 99;
v___x_1174_ = lean_uint32_dec_eq(v_opt_938_, v___x_1173_);
if (v___x_1174_ == 0)
{
uint32_t v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = 98;
v___x_1176_ = lean_uint32_dec_eq(v_opt_938_, v___x_1175_);
if (v___x_1176_ == 0)
{
uint32_t v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = 115;
v___x_1178_ = lean_uint32_dec_eq(v_opt_938_, v___x_1177_);
if (v___x_1178_ == 0)
{
uint32_t v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = 73;
v___x_1180_ = lean_uint32_dec_eq(v_opt_938_, v___x_1179_);
if (v___x_1180_ == 0)
{
uint32_t v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = 114;
v___x_1182_ = lean_uint32_dec_eq(v_opt_938_, v___x_1181_);
if (v___x_1182_ == 0)
{
uint32_t v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = 111;
v___x_1184_ = lean_uint32_dec_eq(v_opt_938_, v___x_1183_);
if (v___x_1184_ == 0)
{
uint32_t v___x_1185_; uint8_t v___x_1186_; 
v___x_1185_ = 105;
v___x_1186_ = lean_uint32_dec_eq(v_opt_938_, v___x_1185_);
if (v___x_1186_ == 0)
{
uint32_t v___x_1187_; uint8_t v___x_1188_; 
v___x_1187_ = 82;
v___x_1188_ = lean_uint32_dec_eq(v_opt_938_, v___x_1187_);
if (v___x_1188_ == 0)
{
uint32_t v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = 77;
v___x_1190_ = lean_uint32_dec_eq(v_opt_938_, v___x_1189_);
if (v___x_1190_ == 0)
{
uint32_t v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = 84;
v___x_1192_ = lean_uint32_dec_eq(v_opt_938_, v___x_1191_);
if (v___x_1192_ == 0)
{
uint32_t v___x_1193_; uint8_t v___x_1194_; 
v___x_1193_ = 116;
v___x_1194_ = lean_uint32_dec_eq(v_opt_938_, v___x_1193_);
if (v___x_1194_ == 0)
{
uint32_t v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = 113;
v___x_1196_ = lean_uint32_dec_eq(v_opt_938_, v___x_1195_);
if (v___x_1196_ == 0)
{
uint32_t v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = 100;
v___x_1198_ = lean_uint32_dec_eq(v_opt_938_, v___x_1197_);
if (v___x_1198_ == 0)
{
uint32_t v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = 79;
v___x_1200_ = lean_uint32_dec_eq(v_opt_938_, v___x_1199_);
if (v___x_1200_ == 0)
{
uint32_t v___x_1201_; uint8_t v___x_1202_; 
v___x_1201_ = 78;
v___x_1202_ = lean_uint32_dec_eq(v_opt_938_, v___x_1201_);
if (v___x_1202_ == 0)
{
uint32_t v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = 74;
v___x_1204_ = lean_uint32_dec_eq(v_opt_938_, v___x_1203_);
if (v___x_1204_ == 0)
{
uint32_t v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = 97;
v___x_1206_ = lean_uint32_dec_eq(v_opt_938_, v___x_1205_);
if (v___x_1206_ == 0)
{
uint32_t v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = 120;
v___x_1208_ = lean_uint32_dec_eq(v_opt_938_, v___x_1207_);
if (v___x_1208_ == 0)
{
uint32_t v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = 76;
v___x_1210_ = lean_uint32_dec_eq(v_opt_938_, v___x_1209_);
if (v___x_1210_ == 0)
{
uint32_t v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = 68;
v___x_1212_ = lean_uint32_dec_eq(v_opt_938_, v___x_1211_);
if (v___x_1212_ == 0)
{
uint32_t v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = 83;
v___x_1214_ = lean_uint32_dec_eq(v_opt_938_, v___x_1213_);
if (v___x_1214_ == 0)
{
uint32_t v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = 87;
v___x_1216_ = lean_uint32_dec_eq(v_opt_938_, v___x_1215_);
if (v___x_1216_ == 0)
{
uint32_t v___x_1217_; uint8_t v___x_1218_; 
v___x_1217_ = 80;
v___x_1218_ = lean_uint32_dec_eq(v_opt_938_, v___x_1217_);
if (v___x_1218_ == 0)
{
uint32_t v___x_1219_; uint8_t v___x_1220_; 
v___x_1219_ = 66;
v___x_1220_ = lean_uint32_dec_eq(v_opt_938_, v___x_1219_);
if (v___x_1220_ == 0)
{
uint32_t v___x_1221_; uint8_t v___x_1222_; 
v___x_1221_ = 112;
v___x_1222_ = lean_uint32_dec_eq(v_opt_938_, v___x_1221_);
if (v___x_1222_ == 0)
{
uint32_t v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = 108;
v___x_1224_ = lean_uint32_dec_eq(v_opt_938_, v___x_1223_);
if (v___x_1224_ == 0)
{
uint32_t v___x_1225_; uint8_t v___x_1226_; 
v___x_1225_ = 117;
v___x_1226_ = lean_uint32_dec_eq(v_opt_938_, v___x_1225_);
if (v___x_1226_ == 0)
{
uint32_t v___x_1227_; uint8_t v___x_1228_; 
v___x_1227_ = 69;
v___x_1228_ = lean_uint32_dec_eq(v_opt_938_, v___x_1227_);
if (v___x_1228_ == 0)
{
uint32_t v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = 89;
v___x_1230_ = lean_uint32_dec_eq(v_opt_938_, v___x_1229_);
if (v___x_1230_ == 0)
{
uint32_t v___x_1231_; uint8_t v___x_1232_; 
v___x_1231_ = 90;
v___x_1232_ = lean_uint32_dec_eq(v_opt_938_, v___x_1231_);
if (v___x_1232_ == 0)
{
uint32_t v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = 72;
v___x_1234_ = lean_uint32_dec_eq(v_opt_938_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_dec(v_optArg_x3f_939_);
lean_dec_ref(v_opts_937_);
goto v___jp_1065_;
}
else
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1));
v___x_1236_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1235_, v_optArg_x3f_939_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1277_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1239_ = v___x_1236_;
v_isShared_1240_ = v_isSharedCheck_1277_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1236_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1277_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v_leanOpts_1241_; lean_object* v_forwardedArgs_1242_; uint8_t v_component_1243_; uint8_t v_printPrefix_1244_; uint8_t v_printLibDir_1245_; uint8_t v_useStdin_1246_; uint8_t v_onlyDeps_1247_; uint8_t v_onlySrcDeps_1248_; uint8_t v_depsJson_1249_; lean_object* v_opts_1250_; uint32_t v_trustLevel_1251_; uint32_t v_numThreads_1252_; lean_object* v_rootDir_x3f_1253_; lean_object* v_setupFileName_x3f_1254_; lean_object* v_oleanFileName_x3f_1255_; lean_object* v_ileanFileName_x3f_1256_; lean_object* v_cFileName_x3f_1257_; lean_object* v_bcFileName_x3f_1258_; uint8_t v_jsonOutput_1259_; lean_object* v_errorOnKinds_1260_; uint8_t v_printStats_1261_; uint8_t v_run_1262_; lean_object* v_incrSaveFileName_x3f_1263_; lean_object* v_incrLoadFileName_x3f_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1275_; 
v_leanOpts_1241_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_1242_ = lean_ctor_get(v_opts_937_, 1);
v_component_1243_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_1244_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_1245_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_1246_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_1247_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1248_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_1249_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_1250_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_1251_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_1252_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1253_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_1254_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_1255_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_1256_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_1257_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_1258_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_1259_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_1260_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_1261_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_1262_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1263_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_1264_ = lean_ctor_get(v_opts_937_, 11);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_1275_ == 0)
{
lean_object* v_unused_1276_; 
v_unused_1276_ = lean_ctor_get(v_opts_937_, 12);
lean_dec(v_unused_1276_);
v___x_1266_ = v_opts_937_;
v_isShared_1267_ = v_isSharedCheck_1275_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_incrLoadFileName_x3f_1264_);
lean_inc(v_incrSaveFileName_x3f_1263_);
lean_inc(v_errorOnKinds_1260_);
lean_inc(v_bcFileName_x3f_1258_);
lean_inc(v_cFileName_x3f_1257_);
lean_inc(v_ileanFileName_x3f_1256_);
lean_inc(v_oleanFileName_x3f_1255_);
lean_inc(v_setupFileName_x3f_1254_);
lean_inc(v_rootDir_x3f_1253_);
lean_inc(v_opts_1250_);
lean_inc(v_forwardedArgs_1242_);
lean_inc(v_leanOpts_1241_);
lean_dec(v_opts_937_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1275_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; lean_object* v___x_1270_; 
v___x_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1268_, 0, v_a_1237_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 12, v___x_1268_);
v___x_1270_ = v___x_1266_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_leanOpts_1241_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_forwardedArgs_1242_);
lean_ctor_set(v_reuseFailAlloc_1274_, 2, v_opts_1250_);
lean_ctor_set(v_reuseFailAlloc_1274_, 3, v_rootDir_x3f_1253_);
lean_ctor_set(v_reuseFailAlloc_1274_, 4, v_setupFileName_x3f_1254_);
lean_ctor_set(v_reuseFailAlloc_1274_, 5, v_oleanFileName_x3f_1255_);
lean_ctor_set(v_reuseFailAlloc_1274_, 6, v_ileanFileName_x3f_1256_);
lean_ctor_set(v_reuseFailAlloc_1274_, 7, v_cFileName_x3f_1257_);
lean_ctor_set(v_reuseFailAlloc_1274_, 8, v_bcFileName_x3f_1258_);
lean_ctor_set(v_reuseFailAlloc_1274_, 9, v_errorOnKinds_1260_);
lean_ctor_set(v_reuseFailAlloc_1274_, 10, v_incrSaveFileName_x3f_1263_);
lean_ctor_set(v_reuseFailAlloc_1274_, 11, v_incrLoadFileName_x3f_1264_);
lean_ctor_set(v_reuseFailAlloc_1274_, 12, v___x_1268_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*13 + 8, v_component_1243_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*13 + 9, v_printPrefix_1244_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*13 + 10, v_printLibDir_1245_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*13 + 11, v_useStdin_1246_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*13 + 12, v_onlyDeps_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*13 + 13, v_onlySrcDeps_1248_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*13 + 14, v_depsJson_1249_);
lean_ctor_set_uint32(v_reuseFailAlloc_1274_, sizeof(void*)*13, v_trustLevel_1251_);
lean_ctor_set_uint32(v_reuseFailAlloc_1274_, sizeof(void*)*13 + 4, v_numThreads_1252_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*13 + 15, v_jsonOutput_1259_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*13 + 16, v_printStats_1261_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*13 + 17, v_run_1262_);
v___x_1270_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1272_; 
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v___x_1270_);
v___x_1272_ = v___x_1239_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1270_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
lean_dec_ref(v_opts_937_);
v_a_1278_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1278_);
lean_dec_ref_known(v___x_1236_, 1);
v___x_1282_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1283_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1282_);
lean_dec_ref(v___x_1283_);
goto v___jp_1279_;
v___jp_1279_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = lean_io_error_to_string(v_a_1278_);
v___x_1281_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1280_);
lean_dec_ref(v___x_1281_);
goto v___jp_1037_;
}
}
}
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2));
v___x_1285_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1284_, v_optArg_x3f_939_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1326_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1288_ = v___x_1285_;
v_isShared_1289_ = v_isSharedCheck_1326_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1285_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1326_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v_leanOpts_1290_; lean_object* v_forwardedArgs_1291_; uint8_t v_component_1292_; uint8_t v_printPrefix_1293_; uint8_t v_printLibDir_1294_; uint8_t v_useStdin_1295_; uint8_t v_onlyDeps_1296_; uint8_t v_onlySrcDeps_1297_; uint8_t v_depsJson_1298_; lean_object* v_opts_1299_; uint32_t v_trustLevel_1300_; uint32_t v_numThreads_1301_; lean_object* v_rootDir_x3f_1302_; lean_object* v_setupFileName_x3f_1303_; lean_object* v_oleanFileName_x3f_1304_; lean_object* v_ileanFileName_x3f_1305_; lean_object* v_cFileName_x3f_1306_; lean_object* v_bcFileName_x3f_1307_; uint8_t v_jsonOutput_1308_; lean_object* v_errorOnKinds_1309_; uint8_t v_printStats_1310_; uint8_t v_run_1311_; lean_object* v_incrSaveFileName_x3f_1312_; lean_object* v_incrHeaderSaveFileName_x3f_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1324_; 
v_leanOpts_1290_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_1291_ = lean_ctor_get(v_opts_937_, 1);
v_component_1292_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_1293_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_1294_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_1295_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_1296_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1297_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_1298_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_1299_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_1300_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_1301_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1302_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_1303_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_1304_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_1305_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_1306_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_1307_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_1308_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_1309_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_1310_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_1311_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1312_ = lean_ctor_get(v_opts_937_, 10);
v_incrHeaderSaveFileName_x3f_1313_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_1324_ == 0)
{
lean_object* v_unused_1325_; 
v_unused_1325_ = lean_ctor_get(v_opts_937_, 11);
lean_dec(v_unused_1325_);
v___x_1315_ = v_opts_937_;
v_isShared_1316_ = v_isSharedCheck_1324_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1313_);
lean_inc(v_incrSaveFileName_x3f_1312_);
lean_inc(v_errorOnKinds_1309_);
lean_inc(v_bcFileName_x3f_1307_);
lean_inc(v_cFileName_x3f_1306_);
lean_inc(v_ileanFileName_x3f_1305_);
lean_inc(v_oleanFileName_x3f_1304_);
lean_inc(v_setupFileName_x3f_1303_);
lean_inc(v_rootDir_x3f_1302_);
lean_inc(v_opts_1299_);
lean_inc(v_forwardedArgs_1291_);
lean_inc(v_leanOpts_1290_);
lean_dec(v_opts_937_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1324_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1317_, 0, v_a_1286_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 11, v___x_1317_);
v___x_1319_ = v___x_1315_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_leanOpts_1290_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_forwardedArgs_1291_);
lean_ctor_set(v_reuseFailAlloc_1323_, 2, v_opts_1299_);
lean_ctor_set(v_reuseFailAlloc_1323_, 3, v_rootDir_x3f_1302_);
lean_ctor_set(v_reuseFailAlloc_1323_, 4, v_setupFileName_x3f_1303_);
lean_ctor_set(v_reuseFailAlloc_1323_, 5, v_oleanFileName_x3f_1304_);
lean_ctor_set(v_reuseFailAlloc_1323_, 6, v_ileanFileName_x3f_1305_);
lean_ctor_set(v_reuseFailAlloc_1323_, 7, v_cFileName_x3f_1306_);
lean_ctor_set(v_reuseFailAlloc_1323_, 8, v_bcFileName_x3f_1307_);
lean_ctor_set(v_reuseFailAlloc_1323_, 9, v_errorOnKinds_1309_);
lean_ctor_set(v_reuseFailAlloc_1323_, 10, v_incrSaveFileName_x3f_1312_);
lean_ctor_set(v_reuseFailAlloc_1323_, 11, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1323_, 12, v_incrHeaderSaveFileName_x3f_1313_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, sizeof(void*)*13 + 8, v_component_1292_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, sizeof(void*)*13 + 9, v_printPrefix_1293_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, sizeof(void*)*13 + 10, v_printLibDir_1294_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, sizeof(void*)*13 + 11, v_useStdin_1295_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, sizeof(void*)*13 + 12, v_onlyDeps_1296_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, sizeof(void*)*13 + 13, v_onlySrcDeps_1297_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, sizeof(void*)*13 + 14, v_depsJson_1298_);
lean_ctor_set_uint32(v_reuseFailAlloc_1323_, sizeof(void*)*13, v_trustLevel_1300_);
lean_ctor_set_uint32(v_reuseFailAlloc_1323_, sizeof(void*)*13 + 4, v_numThreads_1301_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, sizeof(void*)*13 + 15, v_jsonOutput_1308_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, sizeof(void*)*13 + 16, v_printStats_1310_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, sizeof(void*)*13 + 17, v_run_1311_);
v___x_1319_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1321_; 
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v___x_1319_);
v___x_1321_ = v___x_1288_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_dec_ref(v_opts_937_);
v_a_1327_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1327_);
lean_dec_ref_known(v___x_1285_, 1);
v___x_1331_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1332_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1331_);
lean_dec_ref(v___x_1332_);
goto v___jp_1328_;
v___jp_1328_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = lean_io_error_to_string(v_a_1327_);
v___x_1330_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1329_);
lean_dec_ref(v___x_1330_);
goto v___jp_1071_;
}
}
}
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3));
v___x_1334_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1333_, v_optArg_x3f_939_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1375_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1337_ = v___x_1334_;
v_isShared_1338_ = v_isSharedCheck_1375_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1334_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1375_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v_leanOpts_1339_; lean_object* v_forwardedArgs_1340_; uint8_t v_component_1341_; uint8_t v_printPrefix_1342_; uint8_t v_printLibDir_1343_; uint8_t v_useStdin_1344_; uint8_t v_onlyDeps_1345_; uint8_t v_onlySrcDeps_1346_; uint8_t v_depsJson_1347_; lean_object* v_opts_1348_; uint32_t v_trustLevel_1349_; uint32_t v_numThreads_1350_; lean_object* v_rootDir_x3f_1351_; lean_object* v_setupFileName_x3f_1352_; lean_object* v_oleanFileName_x3f_1353_; lean_object* v_ileanFileName_x3f_1354_; lean_object* v_cFileName_x3f_1355_; lean_object* v_bcFileName_x3f_1356_; uint8_t v_jsonOutput_1357_; lean_object* v_errorOnKinds_1358_; uint8_t v_printStats_1359_; uint8_t v_run_1360_; lean_object* v_incrLoadFileName_x3f_1361_; lean_object* v_incrHeaderSaveFileName_x3f_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1373_; 
v_leanOpts_1339_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_1340_ = lean_ctor_get(v_opts_937_, 1);
v_component_1341_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_1342_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_1343_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_1344_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_1345_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1346_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_1347_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_1348_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_1349_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_1350_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1351_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_1352_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_1353_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_1354_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_1355_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_1356_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_1357_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_1358_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_1359_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_1360_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrLoadFileName_x3f_1361_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_1362_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_1373_ == 0)
{
lean_object* v_unused_1374_; 
v_unused_1374_ = lean_ctor_get(v_opts_937_, 10);
lean_dec(v_unused_1374_);
v___x_1364_ = v_opts_937_;
v_isShared_1365_ = v_isSharedCheck_1373_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1362_);
lean_inc(v_incrLoadFileName_x3f_1361_);
lean_inc(v_errorOnKinds_1358_);
lean_inc(v_bcFileName_x3f_1356_);
lean_inc(v_cFileName_x3f_1355_);
lean_inc(v_ileanFileName_x3f_1354_);
lean_inc(v_oleanFileName_x3f_1353_);
lean_inc(v_setupFileName_x3f_1352_);
lean_inc(v_rootDir_x3f_1351_);
lean_inc(v_opts_1348_);
lean_inc(v_forwardedArgs_1340_);
lean_inc(v_leanOpts_1339_);
lean_dec(v_opts_937_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1373_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1366_, 0, v_a_1335_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 10, v___x_1366_);
v___x_1368_ = v___x_1364_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_leanOpts_1339_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_forwardedArgs_1340_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v_opts_1348_);
lean_ctor_set(v_reuseFailAlloc_1372_, 3, v_rootDir_x3f_1351_);
lean_ctor_set(v_reuseFailAlloc_1372_, 4, v_setupFileName_x3f_1352_);
lean_ctor_set(v_reuseFailAlloc_1372_, 5, v_oleanFileName_x3f_1353_);
lean_ctor_set(v_reuseFailAlloc_1372_, 6, v_ileanFileName_x3f_1354_);
lean_ctor_set(v_reuseFailAlloc_1372_, 7, v_cFileName_x3f_1355_);
lean_ctor_set(v_reuseFailAlloc_1372_, 8, v_bcFileName_x3f_1356_);
lean_ctor_set(v_reuseFailAlloc_1372_, 9, v_errorOnKinds_1358_);
lean_ctor_set(v_reuseFailAlloc_1372_, 10, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1372_, 11, v_incrLoadFileName_x3f_1361_);
lean_ctor_set(v_reuseFailAlloc_1372_, 12, v_incrHeaderSaveFileName_x3f_1362_);
lean_ctor_set_uint8(v_reuseFailAlloc_1372_, sizeof(void*)*13 + 8, v_component_1341_);
lean_ctor_set_uint8(v_reuseFailAlloc_1372_, sizeof(void*)*13 + 9, v_printPrefix_1342_);
lean_ctor_set_uint8(v_reuseFailAlloc_1372_, sizeof(void*)*13 + 10, v_printLibDir_1343_);
lean_ctor_set_uint8(v_reuseFailAlloc_1372_, sizeof(void*)*13 + 11, v_useStdin_1344_);
lean_ctor_set_uint8(v_reuseFailAlloc_1372_, sizeof(void*)*13 + 12, v_onlyDeps_1345_);
lean_ctor_set_uint8(v_reuseFailAlloc_1372_, sizeof(void*)*13 + 13, v_onlySrcDeps_1346_);
lean_ctor_set_uint8(v_reuseFailAlloc_1372_, sizeof(void*)*13 + 14, v_depsJson_1347_);
lean_ctor_set_uint32(v_reuseFailAlloc_1372_, sizeof(void*)*13, v_trustLevel_1349_);
lean_ctor_set_uint32(v_reuseFailAlloc_1372_, sizeof(void*)*13 + 4, v_numThreads_1350_);
lean_ctor_set_uint8(v_reuseFailAlloc_1372_, sizeof(void*)*13 + 15, v_jsonOutput_1357_);
lean_ctor_set_uint8(v_reuseFailAlloc_1372_, sizeof(void*)*13 + 16, v_printStats_1359_);
lean_ctor_set_uint8(v_reuseFailAlloc_1372_, sizeof(void*)*13 + 17, v_run_1360_);
v___x_1368_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1370_; 
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1368_);
v___x_1370_ = v___x_1337_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
lean_dec_ref(v_opts_937_);
v_a_1376_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___x_1334_, 1);
v___x_1380_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1381_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1380_);
lean_dec_ref(v___x_1381_);
goto v___jp_1377_;
v___jp_1377_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_io_error_to_string(v_a_1376_);
v___x_1379_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1378_);
lean_dec_ref(v___x_1379_);
goto v___jp_1031_;
}
}
}
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4));
v___x_1383_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1382_, v_optArg_x3f_939_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1425_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1386_ = v___x_1383_;
v_isShared_1387_ = v_isSharedCheck_1425_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1383_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1425_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v_leanOpts_1388_; lean_object* v_forwardedArgs_1389_; uint8_t v_component_1390_; uint8_t v_printPrefix_1391_; uint8_t v_printLibDir_1392_; uint8_t v_useStdin_1393_; uint8_t v_onlyDeps_1394_; uint8_t v_onlySrcDeps_1395_; uint8_t v_depsJson_1396_; lean_object* v_opts_1397_; uint32_t v_trustLevel_1398_; uint32_t v_numThreads_1399_; lean_object* v_rootDir_x3f_1400_; lean_object* v_setupFileName_x3f_1401_; lean_object* v_oleanFileName_x3f_1402_; lean_object* v_ileanFileName_x3f_1403_; lean_object* v_cFileName_x3f_1404_; lean_object* v_bcFileName_x3f_1405_; uint8_t v_jsonOutput_1406_; lean_object* v_errorOnKinds_1407_; uint8_t v_printStats_1408_; uint8_t v_run_1409_; lean_object* v_incrSaveFileName_x3f_1410_; lean_object* v_incrLoadFileName_x3f_1411_; lean_object* v_incrHeaderSaveFileName_x3f_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1424_; 
v_leanOpts_1388_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_1389_ = lean_ctor_get(v_opts_937_, 1);
v_component_1390_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_1391_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_1392_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_1393_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_1394_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1395_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_1396_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_1397_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_1398_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_1399_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1400_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_1401_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_1402_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_1403_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_1404_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_1405_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_1406_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_1407_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_1408_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_1409_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1410_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_1411_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_1412_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1414_ = v_opts_937_;
v_isShared_1415_ = v_isSharedCheck_1424_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1412_);
lean_inc(v_incrLoadFileName_x3f_1411_);
lean_inc(v_incrSaveFileName_x3f_1410_);
lean_inc(v_errorOnKinds_1407_);
lean_inc(v_bcFileName_x3f_1405_);
lean_inc(v_cFileName_x3f_1404_);
lean_inc(v_ileanFileName_x3f_1403_);
lean_inc(v_oleanFileName_x3f_1402_);
lean_inc(v_setupFileName_x3f_1401_);
lean_inc(v_rootDir_x3f_1400_);
lean_inc(v_opts_1397_);
lean_inc(v_forwardedArgs_1389_);
lean_inc(v_leanOpts_1388_);
lean_dec(v_opts_937_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1424_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1419_; 
v___x_1416_ = l_String_toName(v_a_1384_);
v___x_1417_ = lean_array_push(v_errorOnKinds_1407_, v___x_1416_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 9, v___x_1417_);
v___x_1419_ = v___x_1414_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_leanOpts_1388_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_forwardedArgs_1389_);
lean_ctor_set(v_reuseFailAlloc_1423_, 2, v_opts_1397_);
lean_ctor_set(v_reuseFailAlloc_1423_, 3, v_rootDir_x3f_1400_);
lean_ctor_set(v_reuseFailAlloc_1423_, 4, v_setupFileName_x3f_1401_);
lean_ctor_set(v_reuseFailAlloc_1423_, 5, v_oleanFileName_x3f_1402_);
lean_ctor_set(v_reuseFailAlloc_1423_, 6, v_ileanFileName_x3f_1403_);
lean_ctor_set(v_reuseFailAlloc_1423_, 7, v_cFileName_x3f_1404_);
lean_ctor_set(v_reuseFailAlloc_1423_, 8, v_bcFileName_x3f_1405_);
lean_ctor_set(v_reuseFailAlloc_1423_, 9, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1423_, 10, v_incrSaveFileName_x3f_1410_);
lean_ctor_set(v_reuseFailAlloc_1423_, 11, v_incrLoadFileName_x3f_1411_);
lean_ctor_set(v_reuseFailAlloc_1423_, 12, v_incrHeaderSaveFileName_x3f_1412_);
lean_ctor_set_uint8(v_reuseFailAlloc_1423_, sizeof(void*)*13 + 8, v_component_1390_);
lean_ctor_set_uint8(v_reuseFailAlloc_1423_, sizeof(void*)*13 + 9, v_printPrefix_1391_);
lean_ctor_set_uint8(v_reuseFailAlloc_1423_, sizeof(void*)*13 + 10, v_printLibDir_1392_);
lean_ctor_set_uint8(v_reuseFailAlloc_1423_, sizeof(void*)*13 + 11, v_useStdin_1393_);
lean_ctor_set_uint8(v_reuseFailAlloc_1423_, sizeof(void*)*13 + 12, v_onlyDeps_1394_);
lean_ctor_set_uint8(v_reuseFailAlloc_1423_, sizeof(void*)*13 + 13, v_onlySrcDeps_1395_);
lean_ctor_set_uint8(v_reuseFailAlloc_1423_, sizeof(void*)*13 + 14, v_depsJson_1396_);
lean_ctor_set_uint32(v_reuseFailAlloc_1423_, sizeof(void*)*13, v_trustLevel_1398_);
lean_ctor_set_uint32(v_reuseFailAlloc_1423_, sizeof(void*)*13 + 4, v_numThreads_1399_);
lean_ctor_set_uint8(v_reuseFailAlloc_1423_, sizeof(void*)*13 + 15, v_jsonOutput_1406_);
lean_ctor_set_uint8(v_reuseFailAlloc_1423_, sizeof(void*)*13 + 16, v_printStats_1408_);
lean_ctor_set_uint8(v_reuseFailAlloc_1423_, sizeof(void*)*13 + 17, v_run_1409_);
v___x_1419_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1421_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v___x_1419_);
v___x_1421_ = v___x_1386_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_dec_ref(v_opts_937_);
v_a_1426_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1426_);
lean_dec_ref_known(v___x_1383_, 1);
v___x_1430_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1431_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1430_);
lean_dec_ref(v___x_1431_);
goto v___jp_1427_;
v___jp_1427_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = lean_io_error_to_string(v_a_1426_);
v___x_1429_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1428_);
lean_dec_ref(v___x_1429_);
goto v___jp_1077_;
}
}
}
}
else
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5));
v___x_1433_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1432_, v_optArg_x3f_939_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1474_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1474_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1474_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v_leanOpts_1438_; lean_object* v_forwardedArgs_1439_; uint8_t v_component_1440_; uint8_t v_printPrefix_1441_; uint8_t v_printLibDir_1442_; uint8_t v_useStdin_1443_; uint8_t v_onlyDeps_1444_; uint8_t v_onlySrcDeps_1445_; uint8_t v_depsJson_1446_; lean_object* v_opts_1447_; uint32_t v_trustLevel_1448_; uint32_t v_numThreads_1449_; lean_object* v_rootDir_x3f_1450_; lean_object* v_oleanFileName_x3f_1451_; lean_object* v_ileanFileName_x3f_1452_; lean_object* v_cFileName_x3f_1453_; lean_object* v_bcFileName_x3f_1454_; uint8_t v_jsonOutput_1455_; lean_object* v_errorOnKinds_1456_; uint8_t v_printStats_1457_; uint8_t v_run_1458_; lean_object* v_incrSaveFileName_x3f_1459_; lean_object* v_incrLoadFileName_x3f_1460_; lean_object* v_incrHeaderSaveFileName_x3f_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1472_; 
v_leanOpts_1438_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_1439_ = lean_ctor_get(v_opts_937_, 1);
v_component_1440_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_1441_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_1442_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_1443_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_1444_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1445_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_1446_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_1447_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_1448_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_1449_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1450_ = lean_ctor_get(v_opts_937_, 3);
v_oleanFileName_x3f_1451_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_1452_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_1453_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_1454_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_1455_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_1456_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_1457_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_1458_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1459_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_1460_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_1461_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_1472_ == 0)
{
lean_object* v_unused_1473_; 
v_unused_1473_ = lean_ctor_get(v_opts_937_, 4);
lean_dec(v_unused_1473_);
v___x_1463_ = v_opts_937_;
v_isShared_1464_ = v_isSharedCheck_1472_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1461_);
lean_inc(v_incrLoadFileName_x3f_1460_);
lean_inc(v_incrSaveFileName_x3f_1459_);
lean_inc(v_errorOnKinds_1456_);
lean_inc(v_bcFileName_x3f_1454_);
lean_inc(v_cFileName_x3f_1453_);
lean_inc(v_ileanFileName_x3f_1452_);
lean_inc(v_oleanFileName_x3f_1451_);
lean_inc(v_rootDir_x3f_1450_);
lean_inc(v_opts_1447_);
lean_inc(v_forwardedArgs_1439_);
lean_inc(v_leanOpts_1438_);
lean_dec(v_opts_937_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1472_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1465_; lean_object* v___x_1467_; 
v___x_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1465_, 0, v_a_1434_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 4, v___x_1465_);
v___x_1467_ = v___x_1463_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_leanOpts_1438_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_forwardedArgs_1439_);
lean_ctor_set(v_reuseFailAlloc_1471_, 2, v_opts_1447_);
lean_ctor_set(v_reuseFailAlloc_1471_, 3, v_rootDir_x3f_1450_);
lean_ctor_set(v_reuseFailAlloc_1471_, 4, v___x_1465_);
lean_ctor_set(v_reuseFailAlloc_1471_, 5, v_oleanFileName_x3f_1451_);
lean_ctor_set(v_reuseFailAlloc_1471_, 6, v_ileanFileName_x3f_1452_);
lean_ctor_set(v_reuseFailAlloc_1471_, 7, v_cFileName_x3f_1453_);
lean_ctor_set(v_reuseFailAlloc_1471_, 8, v_bcFileName_x3f_1454_);
lean_ctor_set(v_reuseFailAlloc_1471_, 9, v_errorOnKinds_1456_);
lean_ctor_set(v_reuseFailAlloc_1471_, 10, v_incrSaveFileName_x3f_1459_);
lean_ctor_set(v_reuseFailAlloc_1471_, 11, v_incrLoadFileName_x3f_1460_);
lean_ctor_set(v_reuseFailAlloc_1471_, 12, v_incrHeaderSaveFileName_x3f_1461_);
lean_ctor_set_uint8(v_reuseFailAlloc_1471_, sizeof(void*)*13 + 8, v_component_1440_);
lean_ctor_set_uint8(v_reuseFailAlloc_1471_, sizeof(void*)*13 + 9, v_printPrefix_1441_);
lean_ctor_set_uint8(v_reuseFailAlloc_1471_, sizeof(void*)*13 + 10, v_printLibDir_1442_);
lean_ctor_set_uint8(v_reuseFailAlloc_1471_, sizeof(void*)*13 + 11, v_useStdin_1443_);
lean_ctor_set_uint8(v_reuseFailAlloc_1471_, sizeof(void*)*13 + 12, v_onlyDeps_1444_);
lean_ctor_set_uint8(v_reuseFailAlloc_1471_, sizeof(void*)*13 + 13, v_onlySrcDeps_1445_);
lean_ctor_set_uint8(v_reuseFailAlloc_1471_, sizeof(void*)*13 + 14, v_depsJson_1446_);
lean_ctor_set_uint32(v_reuseFailAlloc_1471_, sizeof(void*)*13, v_trustLevel_1448_);
lean_ctor_set_uint32(v_reuseFailAlloc_1471_, sizeof(void*)*13 + 4, v_numThreads_1449_);
lean_ctor_set_uint8(v_reuseFailAlloc_1471_, sizeof(void*)*13 + 15, v_jsonOutput_1455_);
lean_ctor_set_uint8(v_reuseFailAlloc_1471_, sizeof(void*)*13 + 16, v_printStats_1457_);
lean_ctor_set_uint8(v_reuseFailAlloc_1471_, sizeof(void*)*13 + 17, v_run_1458_);
v___x_1467_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
lean_object* v___x_1469_; 
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1467_);
v___x_1469_ = v___x_1436_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1467_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
lean_dec_ref(v_opts_937_);
v_a_1475_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1475_);
lean_dec_ref_known(v___x_1433_, 1);
v___x_1479_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1480_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1479_);
lean_dec_ref(v___x_1480_);
goto v___jp_1476_;
v___jp_1476_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = lean_io_error_to_string(v_a_1475_);
v___x_1478_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1477_);
lean_dec_ref(v___x_1478_);
goto v___jp_1025_;
}
}
}
}
else
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6));
v___x_1482_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1481_, v_optArg_x3f_939_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1484_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc_n(v_a_1483_, 2);
lean_dec_ref_known(v___x_1482_, 1);
v___x_1484_ = lean_load_dynlib(v_a_1483_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1526_; 
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1526_ == 0)
{
lean_object* v_unused_1527_; 
v_unused_1527_ = lean_ctor_get(v___x_1484_, 0);
lean_dec(v_unused_1527_);
v___x_1486_ = v___x_1484_;
v_isShared_1487_ = v_isSharedCheck_1526_;
goto v_resetjp_1485_;
}
else
{
lean_dec(v___x_1484_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1526_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v_leanOpts_1488_; lean_object* v_forwardedArgs_1489_; uint8_t v_component_1490_; uint8_t v_printPrefix_1491_; uint8_t v_printLibDir_1492_; uint8_t v_useStdin_1493_; uint8_t v_onlyDeps_1494_; uint8_t v_onlySrcDeps_1495_; uint8_t v_depsJson_1496_; lean_object* v_opts_1497_; uint32_t v_trustLevel_1498_; uint32_t v_numThreads_1499_; lean_object* v_rootDir_x3f_1500_; lean_object* v_setupFileName_x3f_1501_; lean_object* v_oleanFileName_x3f_1502_; lean_object* v_ileanFileName_x3f_1503_; lean_object* v_cFileName_x3f_1504_; lean_object* v_bcFileName_x3f_1505_; uint8_t v_jsonOutput_1506_; lean_object* v_errorOnKinds_1507_; uint8_t v_printStats_1508_; uint8_t v_run_1509_; lean_object* v_incrSaveFileName_x3f_1510_; lean_object* v_incrLoadFileName_x3f_1511_; lean_object* v_incrHeaderSaveFileName_x3f_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1525_; 
v_leanOpts_1488_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_1489_ = lean_ctor_get(v_opts_937_, 1);
v_component_1490_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_1491_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_1492_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_1493_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_1494_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1495_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_1496_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_1497_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_1498_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_1499_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1500_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_1501_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_1502_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_1503_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_1504_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_1505_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_1506_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_1507_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_1508_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_1509_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1510_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_1511_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_1512_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_1525_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1514_ = v_opts_937_;
v_isShared_1515_ = v_isSharedCheck_1525_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1512_);
lean_inc(v_incrLoadFileName_x3f_1511_);
lean_inc(v_incrSaveFileName_x3f_1510_);
lean_inc(v_errorOnKinds_1507_);
lean_inc(v_bcFileName_x3f_1505_);
lean_inc(v_cFileName_x3f_1504_);
lean_inc(v_ileanFileName_x3f_1503_);
lean_inc(v_oleanFileName_x3f_1502_);
lean_inc(v_setupFileName_x3f_1501_);
lean_inc(v_rootDir_x3f_1500_);
lean_inc(v_opts_1497_);
lean_inc(v_forwardedArgs_1489_);
lean_inc(v_leanOpts_1488_);
lean_dec(v_opts_937_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1525_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1520_; 
v___x_1516_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7));
v___x_1517_ = lean_string_append(v___x_1516_, v_a_1483_);
lean_dec(v_a_1483_);
v___x_1518_ = lean_array_push(v_forwardedArgs_1489_, v___x_1517_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 1, v___x_1518_);
v___x_1520_ = v___x_1514_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_leanOpts_1488_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v___x_1518_);
lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_opts_1497_);
lean_ctor_set(v_reuseFailAlloc_1524_, 3, v_rootDir_x3f_1500_);
lean_ctor_set(v_reuseFailAlloc_1524_, 4, v_setupFileName_x3f_1501_);
lean_ctor_set(v_reuseFailAlloc_1524_, 5, v_oleanFileName_x3f_1502_);
lean_ctor_set(v_reuseFailAlloc_1524_, 6, v_ileanFileName_x3f_1503_);
lean_ctor_set(v_reuseFailAlloc_1524_, 7, v_cFileName_x3f_1504_);
lean_ctor_set(v_reuseFailAlloc_1524_, 8, v_bcFileName_x3f_1505_);
lean_ctor_set(v_reuseFailAlloc_1524_, 9, v_errorOnKinds_1507_);
lean_ctor_set(v_reuseFailAlloc_1524_, 10, v_incrSaveFileName_x3f_1510_);
lean_ctor_set(v_reuseFailAlloc_1524_, 11, v_incrLoadFileName_x3f_1511_);
lean_ctor_set(v_reuseFailAlloc_1524_, 12, v_incrHeaderSaveFileName_x3f_1512_);
lean_ctor_set_uint8(v_reuseFailAlloc_1524_, sizeof(void*)*13 + 8, v_component_1490_);
lean_ctor_set_uint8(v_reuseFailAlloc_1524_, sizeof(void*)*13 + 9, v_printPrefix_1491_);
lean_ctor_set_uint8(v_reuseFailAlloc_1524_, sizeof(void*)*13 + 10, v_printLibDir_1492_);
lean_ctor_set_uint8(v_reuseFailAlloc_1524_, sizeof(void*)*13 + 11, v_useStdin_1493_);
lean_ctor_set_uint8(v_reuseFailAlloc_1524_, sizeof(void*)*13 + 12, v_onlyDeps_1494_);
lean_ctor_set_uint8(v_reuseFailAlloc_1524_, sizeof(void*)*13 + 13, v_onlySrcDeps_1495_);
lean_ctor_set_uint8(v_reuseFailAlloc_1524_, sizeof(void*)*13 + 14, v_depsJson_1496_);
lean_ctor_set_uint32(v_reuseFailAlloc_1524_, sizeof(void*)*13, v_trustLevel_1498_);
lean_ctor_set_uint32(v_reuseFailAlloc_1524_, sizeof(void*)*13 + 4, v_numThreads_1499_);
lean_ctor_set_uint8(v_reuseFailAlloc_1524_, sizeof(void*)*13 + 15, v_jsonOutput_1506_);
lean_ctor_set_uint8(v_reuseFailAlloc_1524_, sizeof(void*)*13 + 16, v_printStats_1508_);
lean_ctor_set_uint8(v_reuseFailAlloc_1524_, sizeof(void*)*13 + 17, v_run_1509_);
v___x_1520_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
lean_object* v___x_1522_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v___x_1520_);
v___x_1522_ = v___x_1486_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_dec(v_a_1483_);
lean_dec_ref(v_opts_937_);
v_a_1528_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1528_);
lean_dec_ref_known(v___x_1484_, 1);
v___x_1532_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1533_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1532_);
lean_dec_ref(v___x_1533_);
goto v___jp_1529_;
v___jp_1529_:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = lean_io_error_to_string(v_a_1528_);
v___x_1531_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1530_);
lean_dec_ref(v___x_1531_);
goto v___jp_1083_;
}
}
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
lean_dec_ref(v_opts_937_);
v_a_1534_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1482_, 1);
v___x_1538_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1539_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1538_);
lean_dec_ref(v___x_1539_);
goto v___jp_1535_;
v___jp_1535_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = lean_io_error_to_string(v_a_1534_);
v___x_1537_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1536_);
lean_dec_ref(v___x_1537_);
goto v___jp_1089_;
}
}
}
}
else
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8));
v___x_1541_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1540_, v_optArg_x3f_939_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1613_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1544_ = v___x_1541_;
v_isShared_1545_ = v_isSharedCheck_1613_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1541_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1613_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v_fst_1547_; lean_object* v_snd_1548_; lean_object* v___y_1597_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1608_ = lean_unsigned_to_nat(0u);
v___x_1609_ = lean_string_utf8_byte_size(v_a_1542_);
v___x_1610_ = lean_box(0);
v___x_1611_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_1609_, v_a_1542_, v___x_1608_, v___x_1610_);
if (lean_obj_tag(v___x_1611_) == 0)
{
v___y_1597_ = v___x_1609_;
goto v___jp_1596_;
}
else
{
lean_object* v_val_1612_; 
v_val_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_val_1612_);
lean_dec_ref_known(v___x_1611_, 1);
v___y_1597_ = v_val_1612_;
goto v___jp_1596_;
}
v___jp_1546_:
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_load_plugin(v_fst_1547_, v_snd_1548_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1591_; 
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1591_ == 0)
{
lean_object* v_unused_1592_; 
v_unused_1592_ = lean_ctor_get(v___x_1549_, 0);
lean_dec(v_unused_1592_);
v___x_1551_ = v___x_1549_;
v_isShared_1552_ = v_isSharedCheck_1591_;
goto v_resetjp_1550_;
}
else
{
lean_dec(v___x_1549_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1591_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v_leanOpts_1553_; lean_object* v_forwardedArgs_1554_; uint8_t v_component_1555_; uint8_t v_printPrefix_1556_; uint8_t v_printLibDir_1557_; uint8_t v_useStdin_1558_; uint8_t v_onlyDeps_1559_; uint8_t v_onlySrcDeps_1560_; uint8_t v_depsJson_1561_; lean_object* v_opts_1562_; uint32_t v_trustLevel_1563_; uint32_t v_numThreads_1564_; lean_object* v_rootDir_x3f_1565_; lean_object* v_setupFileName_x3f_1566_; lean_object* v_oleanFileName_x3f_1567_; lean_object* v_ileanFileName_x3f_1568_; lean_object* v_cFileName_x3f_1569_; lean_object* v_bcFileName_x3f_1570_; uint8_t v_jsonOutput_1571_; lean_object* v_errorOnKinds_1572_; uint8_t v_printStats_1573_; uint8_t v_run_1574_; lean_object* v_incrSaveFileName_x3f_1575_; lean_object* v_incrLoadFileName_x3f_1576_; lean_object* v_incrHeaderSaveFileName_x3f_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1590_; 
v_leanOpts_1553_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_1554_ = lean_ctor_get(v_opts_937_, 1);
v_component_1555_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_1556_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_1557_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_1558_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_1559_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1560_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_1561_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_1562_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_1563_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_1564_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1565_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_1566_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_1567_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_1568_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_1569_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_1570_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_1571_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_1572_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_1573_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_1574_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1575_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_1576_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_1577_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1579_ = v_opts_937_;
v_isShared_1580_ = v_isSharedCheck_1590_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1577_);
lean_inc(v_incrLoadFileName_x3f_1576_);
lean_inc(v_incrSaveFileName_x3f_1575_);
lean_inc(v_errorOnKinds_1572_);
lean_inc(v_bcFileName_x3f_1570_);
lean_inc(v_cFileName_x3f_1569_);
lean_inc(v_ileanFileName_x3f_1568_);
lean_inc(v_oleanFileName_x3f_1567_);
lean_inc(v_setupFileName_x3f_1566_);
lean_inc(v_rootDir_x3f_1565_);
lean_inc(v_opts_1562_);
lean_inc(v_forwardedArgs_1554_);
lean_inc(v_leanOpts_1553_);
lean_dec(v_opts_937_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1590_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1581_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9));
v___x_1582_ = lean_string_append(v___x_1581_, v_a_1542_);
lean_dec(v_a_1542_);
v___x_1583_ = lean_array_push(v_forwardedArgs_1554_, v___x_1582_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 1, v___x_1583_);
v___x_1585_ = v___x_1579_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_leanOpts_1553_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v___x_1583_);
lean_ctor_set(v_reuseFailAlloc_1589_, 2, v_opts_1562_);
lean_ctor_set(v_reuseFailAlloc_1589_, 3, v_rootDir_x3f_1565_);
lean_ctor_set(v_reuseFailAlloc_1589_, 4, v_setupFileName_x3f_1566_);
lean_ctor_set(v_reuseFailAlloc_1589_, 5, v_oleanFileName_x3f_1567_);
lean_ctor_set(v_reuseFailAlloc_1589_, 6, v_ileanFileName_x3f_1568_);
lean_ctor_set(v_reuseFailAlloc_1589_, 7, v_cFileName_x3f_1569_);
lean_ctor_set(v_reuseFailAlloc_1589_, 8, v_bcFileName_x3f_1570_);
lean_ctor_set(v_reuseFailAlloc_1589_, 9, v_errorOnKinds_1572_);
lean_ctor_set(v_reuseFailAlloc_1589_, 10, v_incrSaveFileName_x3f_1575_);
lean_ctor_set(v_reuseFailAlloc_1589_, 11, v_incrLoadFileName_x3f_1576_);
lean_ctor_set(v_reuseFailAlloc_1589_, 12, v_incrHeaderSaveFileName_x3f_1577_);
lean_ctor_set_uint8(v_reuseFailAlloc_1589_, sizeof(void*)*13 + 8, v_component_1555_);
lean_ctor_set_uint8(v_reuseFailAlloc_1589_, sizeof(void*)*13 + 9, v_printPrefix_1556_);
lean_ctor_set_uint8(v_reuseFailAlloc_1589_, sizeof(void*)*13 + 10, v_printLibDir_1557_);
lean_ctor_set_uint8(v_reuseFailAlloc_1589_, sizeof(void*)*13 + 11, v_useStdin_1558_);
lean_ctor_set_uint8(v_reuseFailAlloc_1589_, sizeof(void*)*13 + 12, v_onlyDeps_1559_);
lean_ctor_set_uint8(v_reuseFailAlloc_1589_, sizeof(void*)*13 + 13, v_onlySrcDeps_1560_);
lean_ctor_set_uint8(v_reuseFailAlloc_1589_, sizeof(void*)*13 + 14, v_depsJson_1561_);
lean_ctor_set_uint32(v_reuseFailAlloc_1589_, sizeof(void*)*13, v_trustLevel_1563_);
lean_ctor_set_uint32(v_reuseFailAlloc_1589_, sizeof(void*)*13 + 4, v_numThreads_1564_);
lean_ctor_set_uint8(v_reuseFailAlloc_1589_, sizeof(void*)*13 + 15, v_jsonOutput_1571_);
lean_ctor_set_uint8(v_reuseFailAlloc_1589_, sizeof(void*)*13 + 16, v_printStats_1573_);
lean_ctor_set_uint8(v_reuseFailAlloc_1589_, sizeof(void*)*13 + 17, v_run_1574_);
v___x_1585_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1587_; 
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1585_);
v___x_1587_ = v___x_1551_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1585_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
lean_dec(v_a_1542_);
lean_dec_ref(v_opts_937_);
v_a_1593_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1593_);
lean_dec_ref_known(v___x_1549_, 1);
v___x_1594_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1595_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1594_);
lean_dec_ref(v___x_1595_);
v___y_1105_ = v_a_1593_;
goto v___jp_1104_;
}
}
v___jp_1596_:
{
lean_object* v___x_1598_; uint8_t v_decide_1599_; 
v___x_1598_ = lean_string_utf8_byte_size(v_a_1542_);
v_decide_1599_ = lean_nat_dec_eq(v___y_1597_, v___x_1598_);
if (v_decide_1599_ == 0)
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1605_; 
v___x_1600_ = lean_unsigned_to_nat(0u);
v___x_1601_ = lean_string_utf8_next_fast(v_a_1542_, v___y_1597_);
v___x_1602_ = lean_string_utf8_extract_fast(v_a_1542_, v___x_1600_, v___y_1597_);
lean_dec(v___y_1597_);
v___x_1603_ = lean_string_utf8_extract_fast(v_a_1542_, v___x_1601_, v___x_1598_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set_tag(v___x_1544_, 1);
lean_ctor_set(v___x_1544_, 0, v___x_1603_);
v___x_1605_ = v___x_1544_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
v_fst_1547_ = v___x_1602_;
v_snd_1548_ = v___x_1605_;
goto v___jp_1546_;
}
}
else
{
lean_object* v___x_1607_; 
lean_dec(v___y_1597_);
lean_del_object(v___x_1544_);
v___x_1607_ = lean_box(0);
lean_inc(v_a_1542_);
v_fst_1547_ = v_a_1542_;
v_snd_1548_ = v___x_1607_;
goto v___jp_1546_;
}
}
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
lean_dec_ref(v_opts_937_);
v_a_1614_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1541_, 1);
v___x_1618_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1619_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1618_);
lean_dec_ref(v___x_1619_);
goto v___jp_1615_;
v___jp_1615_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = lean_io_error_to_string(v_a_1614_);
v___x_1617_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1616_);
lean_dec_ref(v___x_1617_);
goto v___jp_1101_;
}
}
}
}
else
{
uint8_t v___x_1620_; 
v___x_1620_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__16, &l___private_Lean_Shell_0__Lean_displayHelp___closed__16_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__16);
if (v___x_1620_ == 0)
{
lean_dec(v_optArg_x3f_939_);
lean_dec_ref(v_opts_937_);
goto v___jp_1065_;
}
else
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10));
v___x_1622_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1621_, v_optArg_x3f_939_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1631_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1631_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1631_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1629_; 
v___x_1627_ = lean_internal_enable_debug(v_a_1623_);
lean_dec(v_a_1623_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v_opts_937_);
v___x_1629_ = v___x_1625_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_opts_937_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_dec_ref(v_opts_937_);
v_a_1632_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1632_);
lean_dec_ref_known(v___x_1622_, 1);
v___x_1636_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1637_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1636_);
lean_dec_ref(v___x_1637_);
goto v___jp_1633_;
v___jp_1633_:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = lean_io_error_to_string(v_a_1632_);
v___x_1635_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1634_);
lean_dec_ref(v___x_1635_);
goto v___jp_1111_;
}
}
}
}
}
else
{
lean_object* v_leanOpts_1638_; lean_object* v_forwardedArgs_1639_; uint8_t v_component_1640_; uint8_t v_printPrefix_1641_; uint8_t v_printLibDir_1642_; uint8_t v_useStdin_1643_; uint8_t v_onlyDeps_1644_; uint8_t v_onlySrcDeps_1645_; uint8_t v_depsJson_1646_; lean_object* v_opts_1647_; uint32_t v_trustLevel_1648_; uint32_t v_numThreads_1649_; lean_object* v_rootDir_x3f_1650_; lean_object* v_setupFileName_x3f_1651_; lean_object* v_oleanFileName_x3f_1652_; lean_object* v_ileanFileName_x3f_1653_; lean_object* v_cFileName_x3f_1654_; lean_object* v_bcFileName_x3f_1655_; uint8_t v_jsonOutput_1656_; lean_object* v_errorOnKinds_1657_; uint8_t v_printStats_1658_; uint8_t v_run_1659_; lean_object* v_incrSaveFileName_x3f_1660_; lean_object* v_incrLoadFileName_x3f_1661_; lean_object* v_incrHeaderSaveFileName_x3f_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1672_; 
lean_dec(v_optArg_x3f_939_);
v_leanOpts_1638_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_1639_ = lean_ctor_get(v_opts_937_, 1);
v_component_1640_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_1641_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_1642_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_1643_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_1644_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1645_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_1646_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_1647_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_1648_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_1649_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1650_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_1651_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_1652_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_1653_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_1654_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_1655_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_1656_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_1657_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_1658_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_1659_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1660_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_1661_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_1662_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_1672_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1664_ = v_opts_937_;
v_isShared_1665_ = v_isSharedCheck_1672_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1662_);
lean_inc(v_incrLoadFileName_x3f_1661_);
lean_inc(v_incrSaveFileName_x3f_1660_);
lean_inc(v_errorOnKinds_1657_);
lean_inc(v_bcFileName_x3f_1655_);
lean_inc(v_cFileName_x3f_1654_);
lean_inc(v_ileanFileName_x3f_1653_);
lean_inc(v_oleanFileName_x3f_1652_);
lean_inc(v_setupFileName_x3f_1651_);
lean_inc(v_rootDir_x3f_1650_);
lean_inc(v_opts_1647_);
lean_inc(v_forwardedArgs_1639_);
lean_inc(v_leanOpts_1638_);
lean_dec(v_opts_937_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1672_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1669_; 
v___x_1666_ = l_Lean_profiler;
v___x_1667_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_1638_, v___x_1666_, v___x_1218_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1667_);
v___x_1669_ = v___x_1664_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1667_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_forwardedArgs_1639_);
lean_ctor_set(v_reuseFailAlloc_1671_, 2, v_opts_1647_);
lean_ctor_set(v_reuseFailAlloc_1671_, 3, v_rootDir_x3f_1650_);
lean_ctor_set(v_reuseFailAlloc_1671_, 4, v_setupFileName_x3f_1651_);
lean_ctor_set(v_reuseFailAlloc_1671_, 5, v_oleanFileName_x3f_1652_);
lean_ctor_set(v_reuseFailAlloc_1671_, 6, v_ileanFileName_x3f_1653_);
lean_ctor_set(v_reuseFailAlloc_1671_, 7, v_cFileName_x3f_1654_);
lean_ctor_set(v_reuseFailAlloc_1671_, 8, v_bcFileName_x3f_1655_);
lean_ctor_set(v_reuseFailAlloc_1671_, 9, v_errorOnKinds_1657_);
lean_ctor_set(v_reuseFailAlloc_1671_, 10, v_incrSaveFileName_x3f_1660_);
lean_ctor_set(v_reuseFailAlloc_1671_, 11, v_incrLoadFileName_x3f_1661_);
lean_ctor_set(v_reuseFailAlloc_1671_, 12, v_incrHeaderSaveFileName_x3f_1662_);
lean_ctor_set_uint8(v_reuseFailAlloc_1671_, sizeof(void*)*13 + 8, v_component_1640_);
lean_ctor_set_uint8(v_reuseFailAlloc_1671_, sizeof(void*)*13 + 9, v_printPrefix_1641_);
lean_ctor_set_uint8(v_reuseFailAlloc_1671_, sizeof(void*)*13 + 10, v_printLibDir_1642_);
lean_ctor_set_uint8(v_reuseFailAlloc_1671_, sizeof(void*)*13 + 11, v_useStdin_1643_);
lean_ctor_set_uint8(v_reuseFailAlloc_1671_, sizeof(void*)*13 + 12, v_onlyDeps_1644_);
lean_ctor_set_uint8(v_reuseFailAlloc_1671_, sizeof(void*)*13 + 13, v_onlySrcDeps_1645_);
lean_ctor_set_uint8(v_reuseFailAlloc_1671_, sizeof(void*)*13 + 14, v_depsJson_1646_);
lean_ctor_set_uint32(v_reuseFailAlloc_1671_, sizeof(void*)*13, v_trustLevel_1648_);
lean_ctor_set_uint32(v_reuseFailAlloc_1671_, sizeof(void*)*13 + 4, v_numThreads_1649_);
lean_ctor_set_uint8(v_reuseFailAlloc_1671_, sizeof(void*)*13 + 15, v_jsonOutput_1656_);
lean_ctor_set_uint8(v_reuseFailAlloc_1671_, sizeof(void*)*13 + 16, v_printStats_1658_);
lean_ctor_set_uint8(v_reuseFailAlloc_1671_, sizeof(void*)*13 + 17, v_run_1659_);
v___x_1669_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1670_; 
v___x_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
return v___x_1670_;
}
}
}
}
else
{
lean_object* v_leanOpts_1673_; lean_object* v_forwardedArgs_1674_; uint8_t v_printPrefix_1675_; uint8_t v_printLibDir_1676_; uint8_t v_useStdin_1677_; uint8_t v_onlyDeps_1678_; uint8_t v_onlySrcDeps_1679_; uint8_t v_depsJson_1680_; lean_object* v_opts_1681_; uint32_t v_trustLevel_1682_; uint32_t v_numThreads_1683_; lean_object* v_rootDir_x3f_1684_; lean_object* v_setupFileName_x3f_1685_; lean_object* v_oleanFileName_x3f_1686_; lean_object* v_ileanFileName_x3f_1687_; lean_object* v_cFileName_x3f_1688_; lean_object* v_bcFileName_x3f_1689_; uint8_t v_jsonOutput_1690_; lean_object* v_errorOnKinds_1691_; uint8_t v_printStats_1692_; uint8_t v_run_1693_; lean_object* v_incrSaveFileName_x3f_1694_; lean_object* v_incrLoadFileName_x3f_1695_; lean_object* v_incrHeaderSaveFileName_x3f_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1705_; 
lean_dec(v_optArg_x3f_939_);
v_leanOpts_1673_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_1674_ = lean_ctor_get(v_opts_937_, 1);
v_printPrefix_1675_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_1676_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_1677_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_1678_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1679_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_1680_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_1681_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_1682_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_1683_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1684_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_1685_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_1686_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_1687_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_1688_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_1689_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_1690_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_1691_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_1692_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_1693_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1694_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_1695_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_1696_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1698_ = v_opts_937_;
v_isShared_1699_ = v_isSharedCheck_1705_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1696_);
lean_inc(v_incrLoadFileName_x3f_1695_);
lean_inc(v_incrSaveFileName_x3f_1694_);
lean_inc(v_errorOnKinds_1691_);
lean_inc(v_bcFileName_x3f_1689_);
lean_inc(v_cFileName_x3f_1688_);
lean_inc(v_ileanFileName_x3f_1687_);
lean_inc(v_oleanFileName_x3f_1686_);
lean_inc(v_setupFileName_x3f_1685_);
lean_inc(v_rootDir_x3f_1684_);
lean_inc(v_opts_1681_);
lean_inc(v_forwardedArgs_1674_);
lean_inc(v_leanOpts_1673_);
lean_dec(v_opts_937_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1705_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
uint8_t v___x_1700_; lean_object* v___x_1702_; 
v___x_1700_ = 2;
if (v_isShared_1699_ == 0)
{
v___x_1702_ = v___x_1698_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_leanOpts_1673_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v_forwardedArgs_1674_);
lean_ctor_set(v_reuseFailAlloc_1704_, 2, v_opts_1681_);
lean_ctor_set(v_reuseFailAlloc_1704_, 3, v_rootDir_x3f_1684_);
lean_ctor_set(v_reuseFailAlloc_1704_, 4, v_setupFileName_x3f_1685_);
lean_ctor_set(v_reuseFailAlloc_1704_, 5, v_oleanFileName_x3f_1686_);
lean_ctor_set(v_reuseFailAlloc_1704_, 6, v_ileanFileName_x3f_1687_);
lean_ctor_set(v_reuseFailAlloc_1704_, 7, v_cFileName_x3f_1688_);
lean_ctor_set(v_reuseFailAlloc_1704_, 8, v_bcFileName_x3f_1689_);
lean_ctor_set(v_reuseFailAlloc_1704_, 9, v_errorOnKinds_1691_);
lean_ctor_set(v_reuseFailAlloc_1704_, 10, v_incrSaveFileName_x3f_1694_);
lean_ctor_set(v_reuseFailAlloc_1704_, 11, v_incrLoadFileName_x3f_1695_);
lean_ctor_set(v_reuseFailAlloc_1704_, 12, v_incrHeaderSaveFileName_x3f_1696_);
lean_ctor_set_uint8(v_reuseFailAlloc_1704_, sizeof(void*)*13 + 9, v_printPrefix_1675_);
lean_ctor_set_uint8(v_reuseFailAlloc_1704_, sizeof(void*)*13 + 10, v_printLibDir_1676_);
lean_ctor_set_uint8(v_reuseFailAlloc_1704_, sizeof(void*)*13 + 11, v_useStdin_1677_);
lean_ctor_set_uint8(v_reuseFailAlloc_1704_, sizeof(void*)*13 + 12, v_onlyDeps_1678_);
lean_ctor_set_uint8(v_reuseFailAlloc_1704_, sizeof(void*)*13 + 13, v_onlySrcDeps_1679_);
lean_ctor_set_uint8(v_reuseFailAlloc_1704_, sizeof(void*)*13 + 14, v_depsJson_1680_);
lean_ctor_set_uint32(v_reuseFailAlloc_1704_, sizeof(void*)*13, v_trustLevel_1682_);
lean_ctor_set_uint32(v_reuseFailAlloc_1704_, sizeof(void*)*13 + 4, v_numThreads_1683_);
lean_ctor_set_uint8(v_reuseFailAlloc_1704_, sizeof(void*)*13 + 15, v_jsonOutput_1690_);
lean_ctor_set_uint8(v_reuseFailAlloc_1704_, sizeof(void*)*13 + 16, v_printStats_1692_);
lean_ctor_set_uint8(v_reuseFailAlloc_1704_, sizeof(void*)*13 + 17, v_run_1693_);
v___x_1702_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
lean_object* v___x_1703_; 
lean_ctor_set_uint8(v___x_1702_, sizeof(void*)*13 + 8, v___x_1700_);
v___x_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1702_);
return v___x_1703_;
}
}
}
}
else
{
lean_object* v_leanOpts_1706_; lean_object* v_forwardedArgs_1707_; uint8_t v_printPrefix_1708_; uint8_t v_printLibDir_1709_; uint8_t v_useStdin_1710_; uint8_t v_onlyDeps_1711_; uint8_t v_onlySrcDeps_1712_; uint8_t v_depsJson_1713_; lean_object* v_opts_1714_; uint32_t v_trustLevel_1715_; uint32_t v_numThreads_1716_; lean_object* v_rootDir_x3f_1717_; lean_object* v_setupFileName_x3f_1718_; lean_object* v_oleanFileName_x3f_1719_; lean_object* v_ileanFileName_x3f_1720_; lean_object* v_cFileName_x3f_1721_; lean_object* v_bcFileName_x3f_1722_; uint8_t v_jsonOutput_1723_; lean_object* v_errorOnKinds_1724_; uint8_t v_printStats_1725_; uint8_t v_run_1726_; lean_object* v_incrSaveFileName_x3f_1727_; lean_object* v_incrLoadFileName_x3f_1728_; lean_object* v_incrHeaderSaveFileName_x3f_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1738_; 
lean_dec(v_optArg_x3f_939_);
v_leanOpts_1706_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_1707_ = lean_ctor_get(v_opts_937_, 1);
v_printPrefix_1708_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_1709_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_1710_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_1711_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1712_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_1713_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_1714_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_1715_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_1716_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1717_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_1718_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_1719_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_1720_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_1721_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_1722_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_1723_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_1724_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_1725_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_1726_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1727_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_1728_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_1729_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_1738_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1731_ = v_opts_937_;
v_isShared_1732_ = v_isSharedCheck_1738_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1729_);
lean_inc(v_incrLoadFileName_x3f_1728_);
lean_inc(v_incrSaveFileName_x3f_1727_);
lean_inc(v_errorOnKinds_1724_);
lean_inc(v_bcFileName_x3f_1722_);
lean_inc(v_cFileName_x3f_1721_);
lean_inc(v_ileanFileName_x3f_1720_);
lean_inc(v_oleanFileName_x3f_1719_);
lean_inc(v_setupFileName_x3f_1718_);
lean_inc(v_rootDir_x3f_1717_);
lean_inc(v_opts_1714_);
lean_inc(v_forwardedArgs_1707_);
lean_inc(v_leanOpts_1706_);
lean_dec(v_opts_937_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1738_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
uint8_t v___x_1733_; lean_object* v___x_1735_; 
v___x_1733_ = 1;
if (v_isShared_1732_ == 0)
{
v___x_1735_ = v___x_1731_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_leanOpts_1706_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v_forwardedArgs_1707_);
lean_ctor_set(v_reuseFailAlloc_1737_, 2, v_opts_1714_);
lean_ctor_set(v_reuseFailAlloc_1737_, 3, v_rootDir_x3f_1717_);
lean_ctor_set(v_reuseFailAlloc_1737_, 4, v_setupFileName_x3f_1718_);
lean_ctor_set(v_reuseFailAlloc_1737_, 5, v_oleanFileName_x3f_1719_);
lean_ctor_set(v_reuseFailAlloc_1737_, 6, v_ileanFileName_x3f_1720_);
lean_ctor_set(v_reuseFailAlloc_1737_, 7, v_cFileName_x3f_1721_);
lean_ctor_set(v_reuseFailAlloc_1737_, 8, v_bcFileName_x3f_1722_);
lean_ctor_set(v_reuseFailAlloc_1737_, 9, v_errorOnKinds_1724_);
lean_ctor_set(v_reuseFailAlloc_1737_, 10, v_incrSaveFileName_x3f_1727_);
lean_ctor_set(v_reuseFailAlloc_1737_, 11, v_incrLoadFileName_x3f_1728_);
lean_ctor_set(v_reuseFailAlloc_1737_, 12, v_incrHeaderSaveFileName_x3f_1729_);
lean_ctor_set_uint8(v_reuseFailAlloc_1737_, sizeof(void*)*13 + 9, v_printPrefix_1708_);
lean_ctor_set_uint8(v_reuseFailAlloc_1737_, sizeof(void*)*13 + 10, v_printLibDir_1709_);
lean_ctor_set_uint8(v_reuseFailAlloc_1737_, sizeof(void*)*13 + 11, v_useStdin_1710_);
lean_ctor_set_uint8(v_reuseFailAlloc_1737_, sizeof(void*)*13 + 12, v_onlyDeps_1711_);
lean_ctor_set_uint8(v_reuseFailAlloc_1737_, sizeof(void*)*13 + 13, v_onlySrcDeps_1712_);
lean_ctor_set_uint8(v_reuseFailAlloc_1737_, sizeof(void*)*13 + 14, v_depsJson_1713_);
lean_ctor_set_uint32(v_reuseFailAlloc_1737_, sizeof(void*)*13, v_trustLevel_1715_);
lean_ctor_set_uint32(v_reuseFailAlloc_1737_, sizeof(void*)*13 + 4, v_numThreads_1716_);
lean_ctor_set_uint8(v_reuseFailAlloc_1737_, sizeof(void*)*13 + 15, v_jsonOutput_1723_);
lean_ctor_set_uint8(v_reuseFailAlloc_1737_, sizeof(void*)*13 + 16, v_printStats_1725_);
lean_ctor_set_uint8(v_reuseFailAlloc_1737_, sizeof(void*)*13 + 17, v_run_1726_);
v___x_1735_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1736_; 
lean_ctor_set_uint8(v___x_1735_, sizeof(void*)*13 + 8, v___x_1733_);
v___x_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
return v___x_1736_;
}
}
}
}
else
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11));
v___x_1740_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1739_, v_optArg_x3f_939_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v_leanOpts_1742_; lean_object* v_forwardedArgs_1743_; uint8_t v_component_1744_; uint8_t v_printPrefix_1745_; uint8_t v_printLibDir_1746_; uint8_t v_useStdin_1747_; uint8_t v_onlyDeps_1748_; uint8_t v_onlySrcDeps_1749_; uint8_t v_depsJson_1750_; lean_object* v_opts_1751_; uint32_t v_trustLevel_1752_; uint32_t v_numThreads_1753_; lean_object* v_rootDir_x3f_1754_; lean_object* v_setupFileName_x3f_1755_; lean_object* v_oleanFileName_x3f_1756_; lean_object* v_ileanFileName_x3f_1757_; lean_object* v_cFileName_x3f_1758_; lean_object* v_bcFileName_x3f_1759_; uint8_t v_jsonOutput_1760_; lean_object* v_errorOnKinds_1761_; uint8_t v_printStats_1762_; uint8_t v_run_1763_; lean_object* v_incrSaveFileName_x3f_1764_; lean_object* v_incrLoadFileName_x3f_1765_; lean_object* v_incrHeaderSaveFileName_x3f_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1791_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref_known(v___x_1740_, 1);
v_leanOpts_1742_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_1743_ = lean_ctor_get(v_opts_937_, 1);
v_component_1744_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_1745_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_1746_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_1747_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_1748_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1749_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_1750_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_1751_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_1752_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_1753_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1754_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_1755_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_1756_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_1757_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_1758_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_1759_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_1760_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_1761_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_1762_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_1763_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1764_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_1765_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_1766_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1768_ = v_opts_937_;
v_isShared_1769_ = v_isSharedCheck_1791_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1766_);
lean_inc(v_incrLoadFileName_x3f_1765_);
lean_inc(v_incrSaveFileName_x3f_1764_);
lean_inc(v_errorOnKinds_1761_);
lean_inc(v_bcFileName_x3f_1759_);
lean_inc(v_cFileName_x3f_1758_);
lean_inc(v_ileanFileName_x3f_1757_);
lean_inc(v_oleanFileName_x3f_1756_);
lean_inc(v_setupFileName_x3f_1755_);
lean_inc(v_rootDir_x3f_1754_);
lean_inc(v_opts_1751_);
lean_inc(v_forwardedArgs_1743_);
lean_inc(v_leanOpts_1742_);
lean_dec(v_opts_937_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1791_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1770_; 
lean_inc(v_a_1741_);
v___x_1770_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_leanOpts_1742_, v_a_1741_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1784_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1773_ = v___x_1770_;
v_isShared_1774_ = v_isSharedCheck_1784_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1770_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1784_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1779_; 
v___x_1775_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12));
v___x_1776_ = lean_string_append(v___x_1775_, v_a_1741_);
lean_dec(v_a_1741_);
v___x_1777_ = lean_array_push(v_forwardedArgs_1743_, v___x_1776_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 1, v___x_1777_);
lean_ctor_set(v___x_1768_, 0, v_a_1771_);
v___x_1779_ = v___x_1768_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1771_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v___x_1777_);
lean_ctor_set(v_reuseFailAlloc_1783_, 2, v_opts_1751_);
lean_ctor_set(v_reuseFailAlloc_1783_, 3, v_rootDir_x3f_1754_);
lean_ctor_set(v_reuseFailAlloc_1783_, 4, v_setupFileName_x3f_1755_);
lean_ctor_set(v_reuseFailAlloc_1783_, 5, v_oleanFileName_x3f_1756_);
lean_ctor_set(v_reuseFailAlloc_1783_, 6, v_ileanFileName_x3f_1757_);
lean_ctor_set(v_reuseFailAlloc_1783_, 7, v_cFileName_x3f_1758_);
lean_ctor_set(v_reuseFailAlloc_1783_, 8, v_bcFileName_x3f_1759_);
lean_ctor_set(v_reuseFailAlloc_1783_, 9, v_errorOnKinds_1761_);
lean_ctor_set(v_reuseFailAlloc_1783_, 10, v_incrSaveFileName_x3f_1764_);
lean_ctor_set(v_reuseFailAlloc_1783_, 11, v_incrLoadFileName_x3f_1765_);
lean_ctor_set(v_reuseFailAlloc_1783_, 12, v_incrHeaderSaveFileName_x3f_1766_);
lean_ctor_set_uint8(v_reuseFailAlloc_1783_, sizeof(void*)*13 + 8, v_component_1744_);
lean_ctor_set_uint8(v_reuseFailAlloc_1783_, sizeof(void*)*13 + 9, v_printPrefix_1745_);
lean_ctor_set_uint8(v_reuseFailAlloc_1783_, sizeof(void*)*13 + 10, v_printLibDir_1746_);
lean_ctor_set_uint8(v_reuseFailAlloc_1783_, sizeof(void*)*13 + 11, v_useStdin_1747_);
lean_ctor_set_uint8(v_reuseFailAlloc_1783_, sizeof(void*)*13 + 12, v_onlyDeps_1748_);
lean_ctor_set_uint8(v_reuseFailAlloc_1783_, sizeof(void*)*13 + 13, v_onlySrcDeps_1749_);
lean_ctor_set_uint8(v_reuseFailAlloc_1783_, sizeof(void*)*13 + 14, v_depsJson_1750_);
lean_ctor_set_uint32(v_reuseFailAlloc_1783_, sizeof(void*)*13, v_trustLevel_1752_);
lean_ctor_set_uint32(v_reuseFailAlloc_1783_, sizeof(void*)*13 + 4, v_numThreads_1753_);
lean_ctor_set_uint8(v_reuseFailAlloc_1783_, sizeof(void*)*13 + 15, v_jsonOutput_1760_);
lean_ctor_set_uint8(v_reuseFailAlloc_1783_, sizeof(void*)*13 + 16, v_printStats_1762_);
lean_ctor_set_uint8(v_reuseFailAlloc_1783_, sizeof(void*)*13 + 17, v_run_1763_);
v___x_1779_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1781_; 
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1779_);
v___x_1781_ = v___x_1773_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_del_object(v___x_1768_);
lean_dec(v_incrHeaderSaveFileName_x3f_1766_);
lean_dec(v_incrLoadFileName_x3f_1765_);
lean_dec(v_incrSaveFileName_x3f_1764_);
lean_dec_ref(v_errorOnKinds_1761_);
lean_dec(v_bcFileName_x3f_1759_);
lean_dec(v_cFileName_x3f_1758_);
lean_dec(v_ileanFileName_x3f_1757_);
lean_dec(v_oleanFileName_x3f_1756_);
lean_dec(v_setupFileName_x3f_1755_);
lean_dec(v_rootDir_x3f_1754_);
lean_dec_ref(v_opts_1751_);
lean_dec_ref(v_forwardedArgs_1743_);
lean_dec(v_a_1741_);
v_a_1785_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1785_);
lean_dec_ref_known(v___x_1770_, 1);
v___x_1789_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1790_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1789_);
lean_dec_ref(v___x_1790_);
goto v___jp_1786_;
v___jp_1786_:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = lean_io_error_to_string(v_a_1785_);
v___x_1788_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1787_);
lean_dec_ref(v___x_1788_);
goto v___jp_1013_;
}
}
}
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
lean_dec_ref(v_opts_937_);
v_a_1792_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1792_);
lean_dec_ref_known(v___x_1740_, 1);
v___x_1796_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1797_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1796_);
lean_dec_ref(v___x_1797_);
goto v___jp_1793_;
v___jp_1793_:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = lean_io_error_to_string(v_a_1792_);
v___x_1795_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1794_);
lean_dec_ref(v___x_1795_);
goto v___jp_1019_;
}
}
}
}
else
{
lean_object* v_leanOpts_1798_; lean_object* v_forwardedArgs_1799_; uint8_t v_component_1800_; uint8_t v_printPrefix_1801_; uint8_t v_useStdin_1802_; uint8_t v_onlyDeps_1803_; uint8_t v_onlySrcDeps_1804_; uint8_t v_depsJson_1805_; lean_object* v_opts_1806_; uint32_t v_trustLevel_1807_; uint32_t v_numThreads_1808_; lean_object* v_rootDir_x3f_1809_; lean_object* v_setupFileName_x3f_1810_; lean_object* v_oleanFileName_x3f_1811_; lean_object* v_ileanFileName_x3f_1812_; lean_object* v_cFileName_x3f_1813_; lean_object* v_bcFileName_x3f_1814_; uint8_t v_jsonOutput_1815_; lean_object* v_errorOnKinds_1816_; uint8_t v_printStats_1817_; uint8_t v_run_1818_; lean_object* v_incrSaveFileName_x3f_1819_; lean_object* v_incrLoadFileName_x3f_1820_; lean_object* v_incrHeaderSaveFileName_x3f_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1829_; 
lean_dec(v_optArg_x3f_939_);
v_leanOpts_1798_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_1799_ = lean_ctor_get(v_opts_937_, 1);
v_component_1800_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_1801_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_useStdin_1802_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_1803_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1804_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_1805_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_1806_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_1807_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_1808_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1809_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_1810_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_1811_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_1812_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_1813_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_1814_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_1815_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_1816_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_1817_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_1818_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1819_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_1820_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_1821_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_1829_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1823_ = v_opts_937_;
v_isShared_1824_ = v_isSharedCheck_1829_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1821_);
lean_inc(v_incrLoadFileName_x3f_1820_);
lean_inc(v_incrSaveFileName_x3f_1819_);
lean_inc(v_errorOnKinds_1816_);
lean_inc(v_bcFileName_x3f_1814_);
lean_inc(v_cFileName_x3f_1813_);
lean_inc(v_ileanFileName_x3f_1812_);
lean_inc(v_oleanFileName_x3f_1811_);
lean_inc(v_setupFileName_x3f_1810_);
lean_inc(v_rootDir_x3f_1809_);
lean_inc(v_opts_1806_);
lean_inc(v_forwardedArgs_1799_);
lean_inc(v_leanOpts_1798_);
lean_dec(v_opts_937_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1829_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_leanOpts_1798_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_forwardedArgs_1799_);
lean_ctor_set(v_reuseFailAlloc_1828_, 2, v_opts_1806_);
lean_ctor_set(v_reuseFailAlloc_1828_, 3, v_rootDir_x3f_1809_);
lean_ctor_set(v_reuseFailAlloc_1828_, 4, v_setupFileName_x3f_1810_);
lean_ctor_set(v_reuseFailAlloc_1828_, 5, v_oleanFileName_x3f_1811_);
lean_ctor_set(v_reuseFailAlloc_1828_, 6, v_ileanFileName_x3f_1812_);
lean_ctor_set(v_reuseFailAlloc_1828_, 7, v_cFileName_x3f_1813_);
lean_ctor_set(v_reuseFailAlloc_1828_, 8, v_bcFileName_x3f_1814_);
lean_ctor_set(v_reuseFailAlloc_1828_, 9, v_errorOnKinds_1816_);
lean_ctor_set(v_reuseFailAlloc_1828_, 10, v_incrSaveFileName_x3f_1819_);
lean_ctor_set(v_reuseFailAlloc_1828_, 11, v_incrLoadFileName_x3f_1820_);
lean_ctor_set(v_reuseFailAlloc_1828_, 12, v_incrHeaderSaveFileName_x3f_1821_);
lean_ctor_set_uint8(v_reuseFailAlloc_1828_, sizeof(void*)*13 + 8, v_component_1800_);
lean_ctor_set_uint8(v_reuseFailAlloc_1828_, sizeof(void*)*13 + 9, v_printPrefix_1801_);
lean_ctor_set_uint8(v_reuseFailAlloc_1828_, sizeof(void*)*13 + 11, v_useStdin_1802_);
lean_ctor_set_uint8(v_reuseFailAlloc_1828_, sizeof(void*)*13 + 12, v_onlyDeps_1803_);
lean_ctor_set_uint8(v_reuseFailAlloc_1828_, sizeof(void*)*13 + 13, v_onlySrcDeps_1804_);
lean_ctor_set_uint8(v_reuseFailAlloc_1828_, sizeof(void*)*13 + 14, v_depsJson_1805_);
lean_ctor_set_uint32(v_reuseFailAlloc_1828_, sizeof(void*)*13, v_trustLevel_1807_);
lean_ctor_set_uint32(v_reuseFailAlloc_1828_, sizeof(void*)*13 + 4, v_numThreads_1808_);
lean_ctor_set_uint8(v_reuseFailAlloc_1828_, sizeof(void*)*13 + 15, v_jsonOutput_1815_);
lean_ctor_set_uint8(v_reuseFailAlloc_1828_, sizeof(void*)*13 + 16, v_printStats_1817_);
lean_ctor_set_uint8(v_reuseFailAlloc_1828_, sizeof(void*)*13 + 17, v_run_1818_);
v___x_1826_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
lean_object* v___x_1827_; 
lean_ctor_set_uint8(v___x_1826_, sizeof(void*)*13 + 10, v___x_1210_);
v___x_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
return v___x_1827_;
}
}
}
}
else
{
lean_object* v_leanOpts_1830_; lean_object* v_forwardedArgs_1831_; uint8_t v_component_1832_; uint8_t v_printLibDir_1833_; uint8_t v_useStdin_1834_; uint8_t v_onlyDeps_1835_; uint8_t v_onlySrcDeps_1836_; uint8_t v_depsJson_1837_; lean_object* v_opts_1838_; uint32_t v_trustLevel_1839_; uint32_t v_numThreads_1840_; lean_object* v_rootDir_x3f_1841_; lean_object* v_setupFileName_x3f_1842_; lean_object* v_oleanFileName_x3f_1843_; lean_object* v_ileanFileName_x3f_1844_; lean_object* v_cFileName_x3f_1845_; lean_object* v_bcFileName_x3f_1846_; uint8_t v_jsonOutput_1847_; lean_object* v_errorOnKinds_1848_; uint8_t v_printStats_1849_; uint8_t v_run_1850_; lean_object* v_incrSaveFileName_x3f_1851_; lean_object* v_incrLoadFileName_x3f_1852_; lean_object* v_incrHeaderSaveFileName_x3f_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1861_; 
lean_dec(v_optArg_x3f_939_);
v_leanOpts_1830_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_1831_ = lean_ctor_get(v_opts_937_, 1);
v_component_1832_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printLibDir_1833_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_1834_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_1835_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1836_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_1837_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_1838_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_1839_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_1840_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1841_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_1842_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_1843_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_1844_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_1845_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_1846_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_1847_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_1848_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_1849_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_1850_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1851_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_1852_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_1853_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_1861_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1855_ = v_opts_937_;
v_isShared_1856_ = v_isSharedCheck_1861_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1853_);
lean_inc(v_incrLoadFileName_x3f_1852_);
lean_inc(v_incrSaveFileName_x3f_1851_);
lean_inc(v_errorOnKinds_1848_);
lean_inc(v_bcFileName_x3f_1846_);
lean_inc(v_cFileName_x3f_1845_);
lean_inc(v_ileanFileName_x3f_1844_);
lean_inc(v_oleanFileName_x3f_1843_);
lean_inc(v_setupFileName_x3f_1842_);
lean_inc(v_rootDir_x3f_1841_);
lean_inc(v_opts_1838_);
lean_inc(v_forwardedArgs_1831_);
lean_inc(v_leanOpts_1830_);
lean_dec(v_opts_937_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1861_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_leanOpts_1830_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_forwardedArgs_1831_);
lean_ctor_set(v_reuseFailAlloc_1860_, 2, v_opts_1838_);
lean_ctor_set(v_reuseFailAlloc_1860_, 3, v_rootDir_x3f_1841_);
lean_ctor_set(v_reuseFailAlloc_1860_, 4, v_setupFileName_x3f_1842_);
lean_ctor_set(v_reuseFailAlloc_1860_, 5, v_oleanFileName_x3f_1843_);
lean_ctor_set(v_reuseFailAlloc_1860_, 6, v_ileanFileName_x3f_1844_);
lean_ctor_set(v_reuseFailAlloc_1860_, 7, v_cFileName_x3f_1845_);
lean_ctor_set(v_reuseFailAlloc_1860_, 8, v_bcFileName_x3f_1846_);
lean_ctor_set(v_reuseFailAlloc_1860_, 9, v_errorOnKinds_1848_);
lean_ctor_set(v_reuseFailAlloc_1860_, 10, v_incrSaveFileName_x3f_1851_);
lean_ctor_set(v_reuseFailAlloc_1860_, 11, v_incrLoadFileName_x3f_1852_);
lean_ctor_set(v_reuseFailAlloc_1860_, 12, v_incrHeaderSaveFileName_x3f_1853_);
lean_ctor_set_uint8(v_reuseFailAlloc_1860_, sizeof(void*)*13 + 8, v_component_1832_);
lean_ctor_set_uint8(v_reuseFailAlloc_1860_, sizeof(void*)*13 + 10, v_printLibDir_1833_);
lean_ctor_set_uint8(v_reuseFailAlloc_1860_, sizeof(void*)*13 + 11, v_useStdin_1834_);
lean_ctor_set_uint8(v_reuseFailAlloc_1860_, sizeof(void*)*13 + 12, v_onlyDeps_1835_);
lean_ctor_set_uint8(v_reuseFailAlloc_1860_, sizeof(void*)*13 + 13, v_onlySrcDeps_1836_);
lean_ctor_set_uint8(v_reuseFailAlloc_1860_, sizeof(void*)*13 + 14, v_depsJson_1837_);
lean_ctor_set_uint32(v_reuseFailAlloc_1860_, sizeof(void*)*13, v_trustLevel_1839_);
lean_ctor_set_uint32(v_reuseFailAlloc_1860_, sizeof(void*)*13 + 4, v_numThreads_1840_);
lean_ctor_set_uint8(v_reuseFailAlloc_1860_, sizeof(void*)*13 + 15, v_jsonOutput_1847_);
lean_ctor_set_uint8(v_reuseFailAlloc_1860_, sizeof(void*)*13 + 16, v_printStats_1849_);
lean_ctor_set_uint8(v_reuseFailAlloc_1860_, sizeof(void*)*13 + 17, v_run_1850_);
v___x_1858_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1859_; 
lean_ctor_set_uint8(v___x_1858_, sizeof(void*)*13 + 9, v___x_1208_);
v___x_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
return v___x_1859_;
}
}
}
}
else
{
lean_object* v_leanOpts_1862_; lean_object* v_forwardedArgs_1863_; uint8_t v_component_1864_; uint8_t v_printPrefix_1865_; uint8_t v_printLibDir_1866_; uint8_t v_useStdin_1867_; uint8_t v_onlyDeps_1868_; uint8_t v_onlySrcDeps_1869_; uint8_t v_depsJson_1870_; lean_object* v_opts_1871_; uint32_t v_trustLevel_1872_; uint32_t v_numThreads_1873_; lean_object* v_rootDir_x3f_1874_; lean_object* v_setupFileName_x3f_1875_; lean_object* v_oleanFileName_x3f_1876_; lean_object* v_ileanFileName_x3f_1877_; lean_object* v_cFileName_x3f_1878_; lean_object* v_bcFileName_x3f_1879_; uint8_t v_jsonOutput_1880_; lean_object* v_errorOnKinds_1881_; uint8_t v_run_1882_; lean_object* v_incrSaveFileName_x3f_1883_; lean_object* v_incrLoadFileName_x3f_1884_; lean_object* v_incrHeaderSaveFileName_x3f_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1893_; 
lean_dec(v_optArg_x3f_939_);
v_leanOpts_1862_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_1863_ = lean_ctor_get(v_opts_937_, 1);
v_component_1864_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_1865_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_1866_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_1867_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_1868_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1869_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_1870_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_1871_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_1872_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_1873_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1874_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_1875_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_1876_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_1877_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_1878_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_1879_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_1880_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_1881_ = lean_ctor_get(v_opts_937_, 9);
v_run_1882_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1883_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_1884_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_1885_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1887_ = v_opts_937_;
v_isShared_1888_ = v_isSharedCheck_1893_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1885_);
lean_inc(v_incrLoadFileName_x3f_1884_);
lean_inc(v_incrSaveFileName_x3f_1883_);
lean_inc(v_errorOnKinds_1881_);
lean_inc(v_bcFileName_x3f_1879_);
lean_inc(v_cFileName_x3f_1878_);
lean_inc(v_ileanFileName_x3f_1877_);
lean_inc(v_oleanFileName_x3f_1876_);
lean_inc(v_setupFileName_x3f_1875_);
lean_inc(v_rootDir_x3f_1874_);
lean_inc(v_opts_1871_);
lean_inc(v_forwardedArgs_1863_);
lean_inc(v_leanOpts_1862_);
lean_dec(v_opts_937_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1893_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_leanOpts_1862_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_forwardedArgs_1863_);
lean_ctor_set(v_reuseFailAlloc_1892_, 2, v_opts_1871_);
lean_ctor_set(v_reuseFailAlloc_1892_, 3, v_rootDir_x3f_1874_);
lean_ctor_set(v_reuseFailAlloc_1892_, 4, v_setupFileName_x3f_1875_);
lean_ctor_set(v_reuseFailAlloc_1892_, 5, v_oleanFileName_x3f_1876_);
lean_ctor_set(v_reuseFailAlloc_1892_, 6, v_ileanFileName_x3f_1877_);
lean_ctor_set(v_reuseFailAlloc_1892_, 7, v_cFileName_x3f_1878_);
lean_ctor_set(v_reuseFailAlloc_1892_, 8, v_bcFileName_x3f_1879_);
lean_ctor_set(v_reuseFailAlloc_1892_, 9, v_errorOnKinds_1881_);
lean_ctor_set(v_reuseFailAlloc_1892_, 10, v_incrSaveFileName_x3f_1883_);
lean_ctor_set(v_reuseFailAlloc_1892_, 11, v_incrLoadFileName_x3f_1884_);
lean_ctor_set(v_reuseFailAlloc_1892_, 12, v_incrHeaderSaveFileName_x3f_1885_);
lean_ctor_set_uint8(v_reuseFailAlloc_1892_, sizeof(void*)*13 + 8, v_component_1864_);
lean_ctor_set_uint8(v_reuseFailAlloc_1892_, sizeof(void*)*13 + 9, v_printPrefix_1865_);
lean_ctor_set_uint8(v_reuseFailAlloc_1892_, sizeof(void*)*13 + 10, v_printLibDir_1866_);
lean_ctor_set_uint8(v_reuseFailAlloc_1892_, sizeof(void*)*13 + 11, v_useStdin_1867_);
lean_ctor_set_uint8(v_reuseFailAlloc_1892_, sizeof(void*)*13 + 12, v_onlyDeps_1868_);
lean_ctor_set_uint8(v_reuseFailAlloc_1892_, sizeof(void*)*13 + 13, v_onlySrcDeps_1869_);
lean_ctor_set_uint8(v_reuseFailAlloc_1892_, sizeof(void*)*13 + 14, v_depsJson_1870_);
lean_ctor_set_uint32(v_reuseFailAlloc_1892_, sizeof(void*)*13, v_trustLevel_1872_);
lean_ctor_set_uint32(v_reuseFailAlloc_1892_, sizeof(void*)*13 + 4, v_numThreads_1873_);
lean_ctor_set_uint8(v_reuseFailAlloc_1892_, sizeof(void*)*13 + 15, v_jsonOutput_1880_);
lean_ctor_set_uint8(v_reuseFailAlloc_1892_, sizeof(void*)*13 + 17, v_run_1882_);
v___x_1890_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; 
lean_ctor_set_uint8(v___x_1890_, sizeof(void*)*13 + 16, v___x_1206_);
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
return v___x_1891_;
}
}
}
}
else
{
lean_object* v_leanOpts_1894_; lean_object* v_forwardedArgs_1895_; uint8_t v_component_1896_; uint8_t v_printPrefix_1897_; uint8_t v_printLibDir_1898_; uint8_t v_useStdin_1899_; uint8_t v_onlyDeps_1900_; uint8_t v_onlySrcDeps_1901_; uint8_t v_depsJson_1902_; lean_object* v_opts_1903_; uint32_t v_trustLevel_1904_; uint32_t v_numThreads_1905_; lean_object* v_rootDir_x3f_1906_; lean_object* v_setupFileName_x3f_1907_; lean_object* v_oleanFileName_x3f_1908_; lean_object* v_ileanFileName_x3f_1909_; lean_object* v_cFileName_x3f_1910_; lean_object* v_bcFileName_x3f_1911_; lean_object* v_errorOnKinds_1912_; uint8_t v_printStats_1913_; uint8_t v_run_1914_; lean_object* v_incrSaveFileName_x3f_1915_; lean_object* v_incrLoadFileName_x3f_1916_; lean_object* v_incrHeaderSaveFileName_x3f_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1925_; 
lean_dec(v_optArg_x3f_939_);
v_leanOpts_1894_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_1895_ = lean_ctor_get(v_opts_937_, 1);
v_component_1896_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_1897_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_1898_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_1899_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_1900_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1901_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_1902_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_1903_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_1904_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_1905_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1906_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_1907_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_1908_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_1909_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_1910_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_1911_ = lean_ctor_get(v_opts_937_, 8);
v_errorOnKinds_1912_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_1913_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_1914_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1915_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_1916_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_1917_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_1925_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1919_ = v_opts_937_;
v_isShared_1920_ = v_isSharedCheck_1925_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1917_);
lean_inc(v_incrLoadFileName_x3f_1916_);
lean_inc(v_incrSaveFileName_x3f_1915_);
lean_inc(v_errorOnKinds_1912_);
lean_inc(v_bcFileName_x3f_1911_);
lean_inc(v_cFileName_x3f_1910_);
lean_inc(v_ileanFileName_x3f_1909_);
lean_inc(v_oleanFileName_x3f_1908_);
lean_inc(v_setupFileName_x3f_1907_);
lean_inc(v_rootDir_x3f_1906_);
lean_inc(v_opts_1903_);
lean_inc(v_forwardedArgs_1895_);
lean_inc(v_leanOpts_1894_);
lean_dec(v_opts_937_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1925_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_leanOpts_1894_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_forwardedArgs_1895_);
lean_ctor_set(v_reuseFailAlloc_1924_, 2, v_opts_1903_);
lean_ctor_set(v_reuseFailAlloc_1924_, 3, v_rootDir_x3f_1906_);
lean_ctor_set(v_reuseFailAlloc_1924_, 4, v_setupFileName_x3f_1907_);
lean_ctor_set(v_reuseFailAlloc_1924_, 5, v_oleanFileName_x3f_1908_);
lean_ctor_set(v_reuseFailAlloc_1924_, 6, v_ileanFileName_x3f_1909_);
lean_ctor_set(v_reuseFailAlloc_1924_, 7, v_cFileName_x3f_1910_);
lean_ctor_set(v_reuseFailAlloc_1924_, 8, v_bcFileName_x3f_1911_);
lean_ctor_set(v_reuseFailAlloc_1924_, 9, v_errorOnKinds_1912_);
lean_ctor_set(v_reuseFailAlloc_1924_, 10, v_incrSaveFileName_x3f_1915_);
lean_ctor_set(v_reuseFailAlloc_1924_, 11, v_incrLoadFileName_x3f_1916_);
lean_ctor_set(v_reuseFailAlloc_1924_, 12, v_incrHeaderSaveFileName_x3f_1917_);
lean_ctor_set_uint8(v_reuseFailAlloc_1924_, sizeof(void*)*13 + 8, v_component_1896_);
lean_ctor_set_uint8(v_reuseFailAlloc_1924_, sizeof(void*)*13 + 9, v_printPrefix_1897_);
lean_ctor_set_uint8(v_reuseFailAlloc_1924_, sizeof(void*)*13 + 10, v_printLibDir_1898_);
lean_ctor_set_uint8(v_reuseFailAlloc_1924_, sizeof(void*)*13 + 11, v_useStdin_1899_);
lean_ctor_set_uint8(v_reuseFailAlloc_1924_, sizeof(void*)*13 + 12, v_onlyDeps_1900_);
lean_ctor_set_uint8(v_reuseFailAlloc_1924_, sizeof(void*)*13 + 13, v_onlySrcDeps_1901_);
lean_ctor_set_uint8(v_reuseFailAlloc_1924_, sizeof(void*)*13 + 14, v_depsJson_1902_);
lean_ctor_set_uint32(v_reuseFailAlloc_1924_, sizeof(void*)*13, v_trustLevel_1904_);
lean_ctor_set_uint32(v_reuseFailAlloc_1924_, sizeof(void*)*13 + 4, v_numThreads_1905_);
lean_ctor_set_uint8(v_reuseFailAlloc_1924_, sizeof(void*)*13 + 16, v_printStats_1913_);
lean_ctor_set_uint8(v_reuseFailAlloc_1924_, sizeof(void*)*13 + 17, v_run_1914_);
v___x_1922_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
lean_object* v___x_1923_; 
lean_ctor_set_uint8(v___x_1922_, sizeof(void*)*13 + 15, v___x_1204_);
v___x_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
return v___x_1923_;
}
}
}
}
else
{
lean_object* v_leanOpts_1926_; lean_object* v_forwardedArgs_1927_; uint8_t v_component_1928_; uint8_t v_printPrefix_1929_; uint8_t v_printLibDir_1930_; uint8_t v_useStdin_1931_; uint8_t v_onlySrcDeps_1932_; lean_object* v_opts_1933_; uint32_t v_trustLevel_1934_; uint32_t v_numThreads_1935_; lean_object* v_rootDir_x3f_1936_; lean_object* v_setupFileName_x3f_1937_; lean_object* v_oleanFileName_x3f_1938_; lean_object* v_ileanFileName_x3f_1939_; lean_object* v_cFileName_x3f_1940_; lean_object* v_bcFileName_x3f_1941_; uint8_t v_jsonOutput_1942_; lean_object* v_errorOnKinds_1943_; uint8_t v_printStats_1944_; uint8_t v_run_1945_; lean_object* v_incrSaveFileName_x3f_1946_; lean_object* v_incrLoadFileName_x3f_1947_; lean_object* v_incrHeaderSaveFileName_x3f_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1956_; 
lean_dec(v_optArg_x3f_939_);
v_leanOpts_1926_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_1927_ = lean_ctor_get(v_opts_937_, 1);
v_component_1928_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_1929_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_1930_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_1931_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlySrcDeps_1932_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_opts_1933_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_1934_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_1935_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1936_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_1937_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_1938_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_1939_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_1940_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_1941_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_1942_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_1943_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_1944_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_1945_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1946_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_1947_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_1948_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_1956_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1950_ = v_opts_937_;
v_isShared_1951_ = v_isSharedCheck_1956_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1948_);
lean_inc(v_incrLoadFileName_x3f_1947_);
lean_inc(v_incrSaveFileName_x3f_1946_);
lean_inc(v_errorOnKinds_1943_);
lean_inc(v_bcFileName_x3f_1941_);
lean_inc(v_cFileName_x3f_1940_);
lean_inc(v_ileanFileName_x3f_1939_);
lean_inc(v_oleanFileName_x3f_1938_);
lean_inc(v_setupFileName_x3f_1937_);
lean_inc(v_rootDir_x3f_1936_);
lean_inc(v_opts_1933_);
lean_inc(v_forwardedArgs_1927_);
lean_inc(v_leanOpts_1926_);
lean_dec(v_opts_937_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1956_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_leanOpts_1926_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_forwardedArgs_1927_);
lean_ctor_set(v_reuseFailAlloc_1955_, 2, v_opts_1933_);
lean_ctor_set(v_reuseFailAlloc_1955_, 3, v_rootDir_x3f_1936_);
lean_ctor_set(v_reuseFailAlloc_1955_, 4, v_setupFileName_x3f_1937_);
lean_ctor_set(v_reuseFailAlloc_1955_, 5, v_oleanFileName_x3f_1938_);
lean_ctor_set(v_reuseFailAlloc_1955_, 6, v_ileanFileName_x3f_1939_);
lean_ctor_set(v_reuseFailAlloc_1955_, 7, v_cFileName_x3f_1940_);
lean_ctor_set(v_reuseFailAlloc_1955_, 8, v_bcFileName_x3f_1941_);
lean_ctor_set(v_reuseFailAlloc_1955_, 9, v_errorOnKinds_1943_);
lean_ctor_set(v_reuseFailAlloc_1955_, 10, v_incrSaveFileName_x3f_1946_);
lean_ctor_set(v_reuseFailAlloc_1955_, 11, v_incrLoadFileName_x3f_1947_);
lean_ctor_set(v_reuseFailAlloc_1955_, 12, v_incrHeaderSaveFileName_x3f_1948_);
lean_ctor_set_uint8(v_reuseFailAlloc_1955_, sizeof(void*)*13 + 8, v_component_1928_);
lean_ctor_set_uint8(v_reuseFailAlloc_1955_, sizeof(void*)*13 + 9, v_printPrefix_1929_);
lean_ctor_set_uint8(v_reuseFailAlloc_1955_, sizeof(void*)*13 + 10, v_printLibDir_1930_);
lean_ctor_set_uint8(v_reuseFailAlloc_1955_, sizeof(void*)*13 + 11, v_useStdin_1931_);
lean_ctor_set_uint8(v_reuseFailAlloc_1955_, sizeof(void*)*13 + 13, v_onlySrcDeps_1932_);
lean_ctor_set_uint32(v_reuseFailAlloc_1955_, sizeof(void*)*13, v_trustLevel_1934_);
lean_ctor_set_uint32(v_reuseFailAlloc_1955_, sizeof(void*)*13 + 4, v_numThreads_1935_);
lean_ctor_set_uint8(v_reuseFailAlloc_1955_, sizeof(void*)*13 + 15, v_jsonOutput_1942_);
lean_ctor_set_uint8(v_reuseFailAlloc_1955_, sizeof(void*)*13 + 16, v_printStats_1944_);
lean_ctor_set_uint8(v_reuseFailAlloc_1955_, sizeof(void*)*13 + 17, v_run_1945_);
v___x_1953_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
lean_object* v___x_1954_; 
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*13 + 12, v___x_1202_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*13 + 14, v___x_1202_);
v___x_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
return v___x_1954_;
}
}
}
}
else
{
lean_object* v_leanOpts_1957_; lean_object* v_forwardedArgs_1958_; uint8_t v_component_1959_; uint8_t v_printPrefix_1960_; uint8_t v_printLibDir_1961_; uint8_t v_useStdin_1962_; uint8_t v_onlyDeps_1963_; uint8_t v_depsJson_1964_; lean_object* v_opts_1965_; uint32_t v_trustLevel_1966_; uint32_t v_numThreads_1967_; lean_object* v_rootDir_x3f_1968_; lean_object* v_setupFileName_x3f_1969_; lean_object* v_oleanFileName_x3f_1970_; lean_object* v_ileanFileName_x3f_1971_; lean_object* v_cFileName_x3f_1972_; lean_object* v_bcFileName_x3f_1973_; uint8_t v_jsonOutput_1974_; lean_object* v_errorOnKinds_1975_; uint8_t v_printStats_1976_; uint8_t v_run_1977_; lean_object* v_incrSaveFileName_x3f_1978_; lean_object* v_incrLoadFileName_x3f_1979_; lean_object* v_incrHeaderSaveFileName_x3f_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1988_; 
lean_dec(v_optArg_x3f_939_);
v_leanOpts_1957_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_1958_ = lean_ctor_get(v_opts_937_, 1);
v_component_1959_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_1960_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_1961_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_1962_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_1963_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_depsJson_1964_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_1965_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_1966_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_1967_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1968_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_1969_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_1970_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_1971_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_1972_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_1973_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_1974_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_1975_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_1976_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_1977_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1978_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_1979_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_1980_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_1988_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1982_ = v_opts_937_;
v_isShared_1983_ = v_isSharedCheck_1988_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1980_);
lean_inc(v_incrLoadFileName_x3f_1979_);
lean_inc(v_incrSaveFileName_x3f_1978_);
lean_inc(v_errorOnKinds_1975_);
lean_inc(v_bcFileName_x3f_1973_);
lean_inc(v_cFileName_x3f_1972_);
lean_inc(v_ileanFileName_x3f_1971_);
lean_inc(v_oleanFileName_x3f_1970_);
lean_inc(v_setupFileName_x3f_1969_);
lean_inc(v_rootDir_x3f_1968_);
lean_inc(v_opts_1965_);
lean_inc(v_forwardedArgs_1958_);
lean_inc(v_leanOpts_1957_);
lean_dec(v_opts_937_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1988_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_leanOpts_1957_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_forwardedArgs_1958_);
lean_ctor_set(v_reuseFailAlloc_1987_, 2, v_opts_1965_);
lean_ctor_set(v_reuseFailAlloc_1987_, 3, v_rootDir_x3f_1968_);
lean_ctor_set(v_reuseFailAlloc_1987_, 4, v_setupFileName_x3f_1969_);
lean_ctor_set(v_reuseFailAlloc_1987_, 5, v_oleanFileName_x3f_1970_);
lean_ctor_set(v_reuseFailAlloc_1987_, 6, v_ileanFileName_x3f_1971_);
lean_ctor_set(v_reuseFailAlloc_1987_, 7, v_cFileName_x3f_1972_);
lean_ctor_set(v_reuseFailAlloc_1987_, 8, v_bcFileName_x3f_1973_);
lean_ctor_set(v_reuseFailAlloc_1987_, 9, v_errorOnKinds_1975_);
lean_ctor_set(v_reuseFailAlloc_1987_, 10, v_incrSaveFileName_x3f_1978_);
lean_ctor_set(v_reuseFailAlloc_1987_, 11, v_incrLoadFileName_x3f_1979_);
lean_ctor_set(v_reuseFailAlloc_1987_, 12, v_incrHeaderSaveFileName_x3f_1980_);
lean_ctor_set_uint8(v_reuseFailAlloc_1987_, sizeof(void*)*13 + 8, v_component_1959_);
lean_ctor_set_uint8(v_reuseFailAlloc_1987_, sizeof(void*)*13 + 9, v_printPrefix_1960_);
lean_ctor_set_uint8(v_reuseFailAlloc_1987_, sizeof(void*)*13 + 10, v_printLibDir_1961_);
lean_ctor_set_uint8(v_reuseFailAlloc_1987_, sizeof(void*)*13 + 11, v_useStdin_1962_);
lean_ctor_set_uint8(v_reuseFailAlloc_1987_, sizeof(void*)*13 + 12, v_onlyDeps_1963_);
lean_ctor_set_uint8(v_reuseFailAlloc_1987_, sizeof(void*)*13 + 14, v_depsJson_1964_);
lean_ctor_set_uint32(v_reuseFailAlloc_1987_, sizeof(void*)*13, v_trustLevel_1966_);
lean_ctor_set_uint32(v_reuseFailAlloc_1987_, sizeof(void*)*13 + 4, v_numThreads_1967_);
lean_ctor_set_uint8(v_reuseFailAlloc_1987_, sizeof(void*)*13 + 15, v_jsonOutput_1974_);
lean_ctor_set_uint8(v_reuseFailAlloc_1987_, sizeof(void*)*13 + 16, v_printStats_1976_);
lean_ctor_set_uint8(v_reuseFailAlloc_1987_, sizeof(void*)*13 + 17, v_run_1977_);
v___x_1985_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1986_; 
lean_ctor_set_uint8(v___x_1985_, sizeof(void*)*13 + 13, v___x_1200_);
v___x_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1985_);
return v___x_1986_;
}
}
}
}
else
{
lean_object* v_leanOpts_1989_; lean_object* v_forwardedArgs_1990_; uint8_t v_component_1991_; uint8_t v_printPrefix_1992_; uint8_t v_printLibDir_1993_; uint8_t v_useStdin_1994_; uint8_t v_onlySrcDeps_1995_; uint8_t v_depsJson_1996_; lean_object* v_opts_1997_; uint32_t v_trustLevel_1998_; uint32_t v_numThreads_1999_; lean_object* v_rootDir_x3f_2000_; lean_object* v_setupFileName_x3f_2001_; lean_object* v_oleanFileName_x3f_2002_; lean_object* v_ileanFileName_x3f_2003_; lean_object* v_cFileName_x3f_2004_; lean_object* v_bcFileName_x3f_2005_; uint8_t v_jsonOutput_2006_; lean_object* v_errorOnKinds_2007_; uint8_t v_printStats_2008_; uint8_t v_run_2009_; lean_object* v_incrSaveFileName_x3f_2010_; lean_object* v_incrLoadFileName_x3f_2011_; lean_object* v_incrHeaderSaveFileName_x3f_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2020_; 
lean_dec(v_optArg_x3f_939_);
v_leanOpts_1989_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_1990_ = lean_ctor_get(v_opts_937_, 1);
v_component_1991_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_1992_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_1993_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_1994_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlySrcDeps_1995_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_1996_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_1997_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_1998_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_1999_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2000_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_2001_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_2002_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_2003_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_2004_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_2005_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_2006_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_2007_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_2008_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_2009_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2010_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_2011_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_2012_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_2020_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2014_ = v_opts_937_;
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2012_);
lean_inc(v_incrLoadFileName_x3f_2011_);
lean_inc(v_incrSaveFileName_x3f_2010_);
lean_inc(v_errorOnKinds_2007_);
lean_inc(v_bcFileName_x3f_2005_);
lean_inc(v_cFileName_x3f_2004_);
lean_inc(v_ileanFileName_x3f_2003_);
lean_inc(v_oleanFileName_x3f_2002_);
lean_inc(v_setupFileName_x3f_2001_);
lean_inc(v_rootDir_x3f_2000_);
lean_inc(v_opts_1997_);
lean_inc(v_forwardedArgs_1990_);
lean_inc(v_leanOpts_1989_);
lean_dec(v_opts_937_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_leanOpts_1989_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_forwardedArgs_1990_);
lean_ctor_set(v_reuseFailAlloc_2019_, 2, v_opts_1997_);
lean_ctor_set(v_reuseFailAlloc_2019_, 3, v_rootDir_x3f_2000_);
lean_ctor_set(v_reuseFailAlloc_2019_, 4, v_setupFileName_x3f_2001_);
lean_ctor_set(v_reuseFailAlloc_2019_, 5, v_oleanFileName_x3f_2002_);
lean_ctor_set(v_reuseFailAlloc_2019_, 6, v_ileanFileName_x3f_2003_);
lean_ctor_set(v_reuseFailAlloc_2019_, 7, v_cFileName_x3f_2004_);
lean_ctor_set(v_reuseFailAlloc_2019_, 8, v_bcFileName_x3f_2005_);
lean_ctor_set(v_reuseFailAlloc_2019_, 9, v_errorOnKinds_2007_);
lean_ctor_set(v_reuseFailAlloc_2019_, 10, v_incrSaveFileName_x3f_2010_);
lean_ctor_set(v_reuseFailAlloc_2019_, 11, v_incrLoadFileName_x3f_2011_);
lean_ctor_set(v_reuseFailAlloc_2019_, 12, v_incrHeaderSaveFileName_x3f_2012_);
lean_ctor_set_uint8(v_reuseFailAlloc_2019_, sizeof(void*)*13 + 8, v_component_1991_);
lean_ctor_set_uint8(v_reuseFailAlloc_2019_, sizeof(void*)*13 + 9, v_printPrefix_1992_);
lean_ctor_set_uint8(v_reuseFailAlloc_2019_, sizeof(void*)*13 + 10, v_printLibDir_1993_);
lean_ctor_set_uint8(v_reuseFailAlloc_2019_, sizeof(void*)*13 + 11, v_useStdin_1994_);
lean_ctor_set_uint8(v_reuseFailAlloc_2019_, sizeof(void*)*13 + 13, v_onlySrcDeps_1995_);
lean_ctor_set_uint8(v_reuseFailAlloc_2019_, sizeof(void*)*13 + 14, v_depsJson_1996_);
lean_ctor_set_uint32(v_reuseFailAlloc_2019_, sizeof(void*)*13, v_trustLevel_1998_);
lean_ctor_set_uint32(v_reuseFailAlloc_2019_, sizeof(void*)*13 + 4, v_numThreads_1999_);
lean_ctor_set_uint8(v_reuseFailAlloc_2019_, sizeof(void*)*13 + 15, v_jsonOutput_2006_);
lean_ctor_set_uint8(v_reuseFailAlloc_2019_, sizeof(void*)*13 + 16, v_printStats_2008_);
lean_ctor_set_uint8(v_reuseFailAlloc_2019_, sizeof(void*)*13 + 17, v_run_2009_);
v___x_2017_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
lean_object* v___x_2018_; 
lean_ctor_set_uint8(v___x_2017_, sizeof(void*)*13 + 12, v___x_1198_);
v___x_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2017_);
return v___x_2018_;
}
}
}
}
else
{
lean_object* v_leanOpts_2021_; lean_object* v_forwardedArgs_2022_; uint8_t v_component_2023_; uint8_t v_printPrefix_2024_; uint8_t v_printLibDir_2025_; uint8_t v_useStdin_2026_; uint8_t v_onlyDeps_2027_; uint8_t v_onlySrcDeps_2028_; uint8_t v_depsJson_2029_; lean_object* v_opts_2030_; uint32_t v_trustLevel_2031_; uint32_t v_numThreads_2032_; lean_object* v_rootDir_x3f_2033_; lean_object* v_setupFileName_x3f_2034_; lean_object* v_oleanFileName_x3f_2035_; lean_object* v_ileanFileName_x3f_2036_; lean_object* v_cFileName_x3f_2037_; lean_object* v_bcFileName_x3f_2038_; uint8_t v_jsonOutput_2039_; lean_object* v_errorOnKinds_2040_; uint8_t v_printStats_2041_; uint8_t v_run_2042_; lean_object* v_incrSaveFileName_x3f_2043_; lean_object* v_incrLoadFileName_x3f_2044_; lean_object* v_incrHeaderSaveFileName_x3f_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2055_; 
lean_dec(v_optArg_x3f_939_);
v_leanOpts_2021_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_2022_ = lean_ctor_get(v_opts_937_, 1);
v_component_2023_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_2024_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_2025_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_2026_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_2027_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2028_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_2029_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_2030_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_2031_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_2032_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2033_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_2034_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_2035_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_2036_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_2037_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_2038_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_2039_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_2040_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_2041_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_2042_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2043_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_2044_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_2045_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2047_ = v_opts_937_;
v_isShared_2048_ = v_isSharedCheck_2055_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2045_);
lean_inc(v_incrLoadFileName_x3f_2044_);
lean_inc(v_incrSaveFileName_x3f_2043_);
lean_inc(v_errorOnKinds_2040_);
lean_inc(v_bcFileName_x3f_2038_);
lean_inc(v_cFileName_x3f_2037_);
lean_inc(v_ileanFileName_x3f_2036_);
lean_inc(v_oleanFileName_x3f_2035_);
lean_inc(v_setupFileName_x3f_2034_);
lean_inc(v_rootDir_x3f_2033_);
lean_inc(v_opts_2030_);
lean_inc(v_forwardedArgs_2022_);
lean_inc(v_leanOpts_2021_);
lean_dec(v_opts_937_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2055_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2052_; 
v___x_2049_ = l___private_Lean_Shell_0__Lean_verbose;
v___x_2050_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_2021_, v___x_2049_, v___x_1194_);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 0, v___x_2050_);
v___x_2052_ = v___x_2047_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2050_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_forwardedArgs_2022_);
lean_ctor_set(v_reuseFailAlloc_2054_, 2, v_opts_2030_);
lean_ctor_set(v_reuseFailAlloc_2054_, 3, v_rootDir_x3f_2033_);
lean_ctor_set(v_reuseFailAlloc_2054_, 4, v_setupFileName_x3f_2034_);
lean_ctor_set(v_reuseFailAlloc_2054_, 5, v_oleanFileName_x3f_2035_);
lean_ctor_set(v_reuseFailAlloc_2054_, 6, v_ileanFileName_x3f_2036_);
lean_ctor_set(v_reuseFailAlloc_2054_, 7, v_cFileName_x3f_2037_);
lean_ctor_set(v_reuseFailAlloc_2054_, 8, v_bcFileName_x3f_2038_);
lean_ctor_set(v_reuseFailAlloc_2054_, 9, v_errorOnKinds_2040_);
lean_ctor_set(v_reuseFailAlloc_2054_, 10, v_incrSaveFileName_x3f_2043_);
lean_ctor_set(v_reuseFailAlloc_2054_, 11, v_incrLoadFileName_x3f_2044_);
lean_ctor_set(v_reuseFailAlloc_2054_, 12, v_incrHeaderSaveFileName_x3f_2045_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*13 + 8, v_component_2023_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*13 + 9, v_printPrefix_2024_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*13 + 10, v_printLibDir_2025_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*13 + 11, v_useStdin_2026_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*13 + 12, v_onlyDeps_2027_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*13 + 13, v_onlySrcDeps_2028_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*13 + 14, v_depsJson_2029_);
lean_ctor_set_uint32(v_reuseFailAlloc_2054_, sizeof(void*)*13, v_trustLevel_2031_);
lean_ctor_set_uint32(v_reuseFailAlloc_2054_, sizeof(void*)*13 + 4, v_numThreads_2032_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*13 + 15, v_jsonOutput_2039_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*13 + 16, v_printStats_2041_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*13 + 17, v_run_2042_);
v___x_2052_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
lean_object* v___x_2053_; 
v___x_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
return v___x_2053_;
}
}
}
}
else
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13));
v___x_2057_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2056_, v_optArg_x3f_939_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2111_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2111_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2111_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2062_ = lean_unsigned_to_nat(0u);
v___x_2063_ = lean_string_utf8_byte_size(v_a_2058_);
lean_inc(v_a_2058_);
v___x_2064_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2064_, 0, v_a_2058_);
lean_ctor_set(v___x_2064_, 1, v___x_2062_);
lean_ctor_set(v___x_2064_, 2, v___x_2063_);
v___x_2065_ = l_String_Slice_toNat_x3f(v___x_2064_);
lean_dec_ref_known(v___x_2064_, 3);
if (lean_obj_tag(v___x_2065_) == 1)
{
lean_object* v_val_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; 
v_val_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_val_2066_);
lean_dec_ref_known(v___x_2065_, 1);
v___x_2067_ = lean_cstr_to_nat("4294967296");
v___x_2068_ = lean_nat_dec_lt(v_val_2066_, v___x_2067_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
lean_dec(v_val_2066_);
lean_del_object(v___x_2060_);
lean_dec(v_a_2058_);
lean_dec_ref(v_opts_937_);
v___x_2069_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14));
v___x_2070_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2069_);
lean_dec_ref(v___x_2070_);
goto v___jp_1001_;
}
else
{
lean_object* v_leanOpts_2071_; lean_object* v_forwardedArgs_2072_; uint8_t v_component_2073_; uint8_t v_printPrefix_2074_; uint8_t v_printLibDir_2075_; uint8_t v_useStdin_2076_; uint8_t v_onlyDeps_2077_; uint8_t v_onlySrcDeps_2078_; uint8_t v_depsJson_2079_; lean_object* v_opts_2080_; uint32_t v_numThreads_2081_; lean_object* v_rootDir_x3f_2082_; lean_object* v_setupFileName_x3f_2083_; lean_object* v_oleanFileName_x3f_2084_; lean_object* v_ileanFileName_x3f_2085_; lean_object* v_cFileName_x3f_2086_; lean_object* v_bcFileName_x3f_2087_; uint8_t v_jsonOutput_2088_; lean_object* v_errorOnKinds_2089_; uint8_t v_printStats_2090_; uint8_t v_run_2091_; lean_object* v_incrSaveFileName_x3f_2092_; lean_object* v_incrLoadFileName_x3f_2093_; lean_object* v_incrHeaderSaveFileName_x3f_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2108_; 
v_leanOpts_2071_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_2072_ = lean_ctor_get(v_opts_937_, 1);
v_component_2073_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_2074_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_2075_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_2076_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_2077_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2078_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_2079_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_2080_ = lean_ctor_get(v_opts_937_, 2);
v_numThreads_2081_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2082_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_2083_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_2084_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_2085_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_2086_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_2087_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_2088_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_2089_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_2090_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_2091_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2092_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_2093_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_2094_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2096_ = v_opts_937_;
v_isShared_2097_ = v_isSharedCheck_2108_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2094_);
lean_inc(v_incrLoadFileName_x3f_2093_);
lean_inc(v_incrSaveFileName_x3f_2092_);
lean_inc(v_errorOnKinds_2089_);
lean_inc(v_bcFileName_x3f_2087_);
lean_inc(v_cFileName_x3f_2086_);
lean_inc(v_ileanFileName_x3f_2085_);
lean_inc(v_oleanFileName_x3f_2084_);
lean_inc(v_setupFileName_x3f_2083_);
lean_inc(v_rootDir_x3f_2082_);
lean_inc(v_opts_2080_);
lean_inc(v_forwardedArgs_2072_);
lean_inc(v_leanOpts_2071_);
lean_dec(v_opts_937_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2108_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
uint32_t v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2103_; 
v___x_2098_ = lean_uint32_of_nat(v_val_2066_);
lean_dec(v_val_2066_);
v___x_2099_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15));
v___x_2100_ = lean_string_append(v___x_2099_, v_a_2058_);
lean_dec(v_a_2058_);
v___x_2101_ = lean_array_push(v_forwardedArgs_2072_, v___x_2100_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 1, v___x_2101_);
v___x_2103_ = v___x_2096_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_leanOpts_2071_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v___x_2101_);
lean_ctor_set(v_reuseFailAlloc_2107_, 2, v_opts_2080_);
lean_ctor_set(v_reuseFailAlloc_2107_, 3, v_rootDir_x3f_2082_);
lean_ctor_set(v_reuseFailAlloc_2107_, 4, v_setupFileName_x3f_2083_);
lean_ctor_set(v_reuseFailAlloc_2107_, 5, v_oleanFileName_x3f_2084_);
lean_ctor_set(v_reuseFailAlloc_2107_, 6, v_ileanFileName_x3f_2085_);
lean_ctor_set(v_reuseFailAlloc_2107_, 7, v_cFileName_x3f_2086_);
lean_ctor_set(v_reuseFailAlloc_2107_, 8, v_bcFileName_x3f_2087_);
lean_ctor_set(v_reuseFailAlloc_2107_, 9, v_errorOnKinds_2089_);
lean_ctor_set(v_reuseFailAlloc_2107_, 10, v_incrSaveFileName_x3f_2092_);
lean_ctor_set(v_reuseFailAlloc_2107_, 11, v_incrLoadFileName_x3f_2093_);
lean_ctor_set(v_reuseFailAlloc_2107_, 12, v_incrHeaderSaveFileName_x3f_2094_);
lean_ctor_set_uint8(v_reuseFailAlloc_2107_, sizeof(void*)*13 + 8, v_component_2073_);
lean_ctor_set_uint8(v_reuseFailAlloc_2107_, sizeof(void*)*13 + 9, v_printPrefix_2074_);
lean_ctor_set_uint8(v_reuseFailAlloc_2107_, sizeof(void*)*13 + 10, v_printLibDir_2075_);
lean_ctor_set_uint8(v_reuseFailAlloc_2107_, sizeof(void*)*13 + 11, v_useStdin_2076_);
lean_ctor_set_uint8(v_reuseFailAlloc_2107_, sizeof(void*)*13 + 12, v_onlyDeps_2077_);
lean_ctor_set_uint8(v_reuseFailAlloc_2107_, sizeof(void*)*13 + 13, v_onlySrcDeps_2078_);
lean_ctor_set_uint8(v_reuseFailAlloc_2107_, sizeof(void*)*13 + 14, v_depsJson_2079_);
lean_ctor_set_uint32(v_reuseFailAlloc_2107_, sizeof(void*)*13 + 4, v_numThreads_2081_);
lean_ctor_set_uint8(v_reuseFailAlloc_2107_, sizeof(void*)*13 + 15, v_jsonOutput_2088_);
lean_ctor_set_uint8(v_reuseFailAlloc_2107_, sizeof(void*)*13 + 16, v_printStats_2090_);
lean_ctor_set_uint8(v_reuseFailAlloc_2107_, sizeof(void*)*13 + 17, v_run_2091_);
v___x_2103_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
lean_object* v___x_2105_; 
lean_ctor_set_uint32(v___x_2103_, sizeof(void*)*13, v___x_2098_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 0, v___x_2103_);
v___x_2105_ = v___x_2060_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
}
else
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
lean_dec(v___x_2065_);
lean_del_object(v___x_2060_);
lean_dec(v_a_2058_);
lean_dec_ref(v_opts_937_);
v___x_2109_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16));
v___x_2110_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2109_);
lean_dec_ref(v___x_2110_);
goto v___jp_998_;
}
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
lean_dec_ref(v_opts_937_);
v_a_2112_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2112_);
lean_dec_ref_known(v___x_2057_, 1);
v___x_2116_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2117_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2116_);
lean_dec_ref(v___x_2117_);
goto v___jp_2113_;
v___jp_2113_:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = lean_io_error_to_string(v_a_2112_);
v___x_2115_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2114_);
lean_dec_ref(v___x_2115_);
goto v___jp_1007_;
}
}
}
}
else
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17));
v___x_2119_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2118_, v_optArg_x3f_939_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2171_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2122_ = v___x_2119_;
v_isShared_2123_ = v_isSharedCheck_2171_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2119_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2171_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2124_ = lean_unsigned_to_nat(0u);
v___x_2125_ = lean_string_utf8_byte_size(v_a_2120_);
lean_inc(v_a_2120_);
v___x_2126_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2126_, 0, v_a_2120_);
lean_ctor_set(v___x_2126_, 1, v___x_2124_);
lean_ctor_set(v___x_2126_, 2, v___x_2125_);
v___x_2127_ = l_String_Slice_toNat_x3f(v___x_2126_);
lean_dec_ref_known(v___x_2126_, 3);
if (lean_obj_tag(v___x_2127_) == 1)
{
lean_object* v_val_2128_; lean_object* v_leanOpts_2129_; lean_object* v_forwardedArgs_2130_; uint8_t v_component_2131_; uint8_t v_printPrefix_2132_; uint8_t v_printLibDir_2133_; uint8_t v_useStdin_2134_; uint8_t v_onlyDeps_2135_; uint8_t v_onlySrcDeps_2136_; uint8_t v_depsJson_2137_; lean_object* v_opts_2138_; uint32_t v_trustLevel_2139_; uint32_t v_numThreads_2140_; lean_object* v_rootDir_x3f_2141_; lean_object* v_setupFileName_x3f_2142_; lean_object* v_oleanFileName_x3f_2143_; lean_object* v_ileanFileName_x3f_2144_; lean_object* v_cFileName_x3f_2145_; lean_object* v_bcFileName_x3f_2146_; uint8_t v_jsonOutput_2147_; lean_object* v_errorOnKinds_2148_; uint8_t v_printStats_2149_; uint8_t v_run_2150_; lean_object* v_incrSaveFileName_x3f_2151_; lean_object* v_incrLoadFileName_x3f_2152_; lean_object* v_incrHeaderSaveFileName_x3f_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2168_; 
v_val_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_val_2128_);
lean_dec_ref_known(v___x_2127_, 1);
v_leanOpts_2129_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_2130_ = lean_ctor_get(v_opts_937_, 1);
v_component_2131_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_2132_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_2133_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_2134_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_2135_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2136_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_2137_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_2138_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_2139_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_2140_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2141_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_2142_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_2143_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_2144_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_2145_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_2146_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_2147_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_2148_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_2149_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_2150_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2151_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_2152_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_2153_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2155_ = v_opts_937_;
v_isShared_2156_ = v_isSharedCheck_2168_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2153_);
lean_inc(v_incrLoadFileName_x3f_2152_);
lean_inc(v_incrSaveFileName_x3f_2151_);
lean_inc(v_errorOnKinds_2148_);
lean_inc(v_bcFileName_x3f_2146_);
lean_inc(v_cFileName_x3f_2145_);
lean_inc(v_ileanFileName_x3f_2144_);
lean_inc(v_oleanFileName_x3f_2143_);
lean_inc(v_setupFileName_x3f_2142_);
lean_inc(v_rootDir_x3f_2141_);
lean_inc(v_opts_2138_);
lean_inc(v_forwardedArgs_2130_);
lean_inc(v_leanOpts_2129_);
lean_dec(v_opts_937_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2168_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2163_; 
v___x_2157_ = l___private_Lean_Shell_0__Lean_timeout;
v___x_2158_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_2129_, v___x_2157_, v_val_2128_);
v___x_2159_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18));
v___x_2160_ = lean_string_append(v___x_2159_, v_a_2120_);
lean_dec(v_a_2120_);
v___x_2161_ = lean_array_push(v_forwardedArgs_2130_, v___x_2160_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 1, v___x_2161_);
lean_ctor_set(v___x_2155_, 0, v___x_2158_);
v___x_2163_ = v___x_2155_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v___x_2161_);
lean_ctor_set(v_reuseFailAlloc_2167_, 2, v_opts_2138_);
lean_ctor_set(v_reuseFailAlloc_2167_, 3, v_rootDir_x3f_2141_);
lean_ctor_set(v_reuseFailAlloc_2167_, 4, v_setupFileName_x3f_2142_);
lean_ctor_set(v_reuseFailAlloc_2167_, 5, v_oleanFileName_x3f_2143_);
lean_ctor_set(v_reuseFailAlloc_2167_, 6, v_ileanFileName_x3f_2144_);
lean_ctor_set(v_reuseFailAlloc_2167_, 7, v_cFileName_x3f_2145_);
lean_ctor_set(v_reuseFailAlloc_2167_, 8, v_bcFileName_x3f_2146_);
lean_ctor_set(v_reuseFailAlloc_2167_, 9, v_errorOnKinds_2148_);
lean_ctor_set(v_reuseFailAlloc_2167_, 10, v_incrSaveFileName_x3f_2151_);
lean_ctor_set(v_reuseFailAlloc_2167_, 11, v_incrLoadFileName_x3f_2152_);
lean_ctor_set(v_reuseFailAlloc_2167_, 12, v_incrHeaderSaveFileName_x3f_2153_);
lean_ctor_set_uint8(v_reuseFailAlloc_2167_, sizeof(void*)*13 + 8, v_component_2131_);
lean_ctor_set_uint8(v_reuseFailAlloc_2167_, sizeof(void*)*13 + 9, v_printPrefix_2132_);
lean_ctor_set_uint8(v_reuseFailAlloc_2167_, sizeof(void*)*13 + 10, v_printLibDir_2133_);
lean_ctor_set_uint8(v_reuseFailAlloc_2167_, sizeof(void*)*13 + 11, v_useStdin_2134_);
lean_ctor_set_uint8(v_reuseFailAlloc_2167_, sizeof(void*)*13 + 12, v_onlyDeps_2135_);
lean_ctor_set_uint8(v_reuseFailAlloc_2167_, sizeof(void*)*13 + 13, v_onlySrcDeps_2136_);
lean_ctor_set_uint8(v_reuseFailAlloc_2167_, sizeof(void*)*13 + 14, v_depsJson_2137_);
lean_ctor_set_uint32(v_reuseFailAlloc_2167_, sizeof(void*)*13, v_trustLevel_2139_);
lean_ctor_set_uint32(v_reuseFailAlloc_2167_, sizeof(void*)*13 + 4, v_numThreads_2140_);
lean_ctor_set_uint8(v_reuseFailAlloc_2167_, sizeof(void*)*13 + 15, v_jsonOutput_2147_);
lean_ctor_set_uint8(v_reuseFailAlloc_2167_, sizeof(void*)*13 + 16, v_printStats_2149_);
lean_ctor_set_uint8(v_reuseFailAlloc_2167_, sizeof(void*)*13 + 17, v_run_2150_);
v___x_2163_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
lean_object* v___x_2165_; 
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 0, v___x_2163_);
v___x_2165_ = v___x_2122_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
else
{
lean_object* v___x_2169_; lean_object* v___x_2170_; 
lean_dec(v___x_2127_);
lean_del_object(v___x_2122_);
lean_dec(v_a_2120_);
lean_dec_ref(v_opts_937_);
v___x_2169_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19));
v___x_2170_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2169_);
lean_dec_ref(v___x_2170_);
goto v___jp_1114_;
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
lean_dec_ref(v_opts_937_);
v_a_2172_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2172_);
lean_dec_ref_known(v___x_2119_, 1);
v___x_2176_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2177_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2176_);
lean_dec_ref(v___x_2177_);
goto v___jp_2173_;
v___jp_2173_:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = lean_io_error_to_string(v_a_2172_);
v___x_2175_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2174_);
lean_dec_ref(v___x_2175_);
goto v___jp_1120_;
}
}
}
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20));
v___x_2179_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2178_, v_optArg_x3f_939_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2231_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2182_ = v___x_2179_;
v_isShared_2183_ = v_isSharedCheck_2231_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2179_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2231_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2184_ = lean_unsigned_to_nat(0u);
v___x_2185_ = lean_string_utf8_byte_size(v_a_2180_);
lean_inc(v_a_2180_);
v___x_2186_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2186_, 0, v_a_2180_);
lean_ctor_set(v___x_2186_, 1, v___x_2184_);
lean_ctor_set(v___x_2186_, 2, v___x_2185_);
v___x_2187_ = l_String_Slice_toNat_x3f(v___x_2186_);
lean_dec_ref_known(v___x_2186_, 3);
if (lean_obj_tag(v___x_2187_) == 1)
{
lean_object* v_val_2188_; lean_object* v_leanOpts_2189_; lean_object* v_forwardedArgs_2190_; uint8_t v_component_2191_; uint8_t v_printPrefix_2192_; uint8_t v_printLibDir_2193_; uint8_t v_useStdin_2194_; uint8_t v_onlyDeps_2195_; uint8_t v_onlySrcDeps_2196_; uint8_t v_depsJson_2197_; lean_object* v_opts_2198_; uint32_t v_trustLevel_2199_; uint32_t v_numThreads_2200_; lean_object* v_rootDir_x3f_2201_; lean_object* v_setupFileName_x3f_2202_; lean_object* v_oleanFileName_x3f_2203_; lean_object* v_ileanFileName_x3f_2204_; lean_object* v_cFileName_x3f_2205_; lean_object* v_bcFileName_x3f_2206_; uint8_t v_jsonOutput_2207_; lean_object* v_errorOnKinds_2208_; uint8_t v_printStats_2209_; uint8_t v_run_2210_; lean_object* v_incrSaveFileName_x3f_2211_; lean_object* v_incrLoadFileName_x3f_2212_; lean_object* v_incrHeaderSaveFileName_x3f_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2228_; 
v_val_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_val_2188_);
lean_dec_ref_known(v___x_2187_, 1);
v_leanOpts_2189_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_2190_ = lean_ctor_get(v_opts_937_, 1);
v_component_2191_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_2192_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_2193_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_2194_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_2195_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2196_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_2197_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_2198_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_2199_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_2200_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2201_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_2202_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_2203_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_2204_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_2205_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_2206_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_2207_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_2208_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_2209_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_2210_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2211_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_2212_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_2213_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_2228_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2215_ = v_opts_937_;
v_isShared_2216_ = v_isSharedCheck_2228_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2213_);
lean_inc(v_incrLoadFileName_x3f_2212_);
lean_inc(v_incrSaveFileName_x3f_2211_);
lean_inc(v_errorOnKinds_2208_);
lean_inc(v_bcFileName_x3f_2206_);
lean_inc(v_cFileName_x3f_2205_);
lean_inc(v_ileanFileName_x3f_2204_);
lean_inc(v_oleanFileName_x3f_2203_);
lean_inc(v_setupFileName_x3f_2202_);
lean_inc(v_rootDir_x3f_2201_);
lean_inc(v_opts_2198_);
lean_inc(v_forwardedArgs_2190_);
lean_inc(v_leanOpts_2189_);
lean_dec(v_opts_937_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2228_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2223_; 
v___x_2217_ = l___private_Lean_Shell_0__Lean_maxMemory;
v___x_2218_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_2189_, v___x_2217_, v_val_2188_);
v___x_2219_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21));
v___x_2220_ = lean_string_append(v___x_2219_, v_a_2180_);
lean_dec(v_a_2180_);
v___x_2221_ = lean_array_push(v_forwardedArgs_2190_, v___x_2220_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 1, v___x_2221_);
lean_ctor_set(v___x_2215_, 0, v___x_2218_);
v___x_2223_ = v___x_2215_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2218_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v___x_2221_);
lean_ctor_set(v_reuseFailAlloc_2227_, 2, v_opts_2198_);
lean_ctor_set(v_reuseFailAlloc_2227_, 3, v_rootDir_x3f_2201_);
lean_ctor_set(v_reuseFailAlloc_2227_, 4, v_setupFileName_x3f_2202_);
lean_ctor_set(v_reuseFailAlloc_2227_, 5, v_oleanFileName_x3f_2203_);
lean_ctor_set(v_reuseFailAlloc_2227_, 6, v_ileanFileName_x3f_2204_);
lean_ctor_set(v_reuseFailAlloc_2227_, 7, v_cFileName_x3f_2205_);
lean_ctor_set(v_reuseFailAlloc_2227_, 8, v_bcFileName_x3f_2206_);
lean_ctor_set(v_reuseFailAlloc_2227_, 9, v_errorOnKinds_2208_);
lean_ctor_set(v_reuseFailAlloc_2227_, 10, v_incrSaveFileName_x3f_2211_);
lean_ctor_set(v_reuseFailAlloc_2227_, 11, v_incrLoadFileName_x3f_2212_);
lean_ctor_set(v_reuseFailAlloc_2227_, 12, v_incrHeaderSaveFileName_x3f_2213_);
lean_ctor_set_uint8(v_reuseFailAlloc_2227_, sizeof(void*)*13 + 8, v_component_2191_);
lean_ctor_set_uint8(v_reuseFailAlloc_2227_, sizeof(void*)*13 + 9, v_printPrefix_2192_);
lean_ctor_set_uint8(v_reuseFailAlloc_2227_, sizeof(void*)*13 + 10, v_printLibDir_2193_);
lean_ctor_set_uint8(v_reuseFailAlloc_2227_, sizeof(void*)*13 + 11, v_useStdin_2194_);
lean_ctor_set_uint8(v_reuseFailAlloc_2227_, sizeof(void*)*13 + 12, v_onlyDeps_2195_);
lean_ctor_set_uint8(v_reuseFailAlloc_2227_, sizeof(void*)*13 + 13, v_onlySrcDeps_2196_);
lean_ctor_set_uint8(v_reuseFailAlloc_2227_, sizeof(void*)*13 + 14, v_depsJson_2197_);
lean_ctor_set_uint32(v_reuseFailAlloc_2227_, sizeof(void*)*13, v_trustLevel_2199_);
lean_ctor_set_uint32(v_reuseFailAlloc_2227_, sizeof(void*)*13 + 4, v_numThreads_2200_);
lean_ctor_set_uint8(v_reuseFailAlloc_2227_, sizeof(void*)*13 + 15, v_jsonOutput_2207_);
lean_ctor_set_uint8(v_reuseFailAlloc_2227_, sizeof(void*)*13 + 16, v_printStats_2209_);
lean_ctor_set_uint8(v_reuseFailAlloc_2227_, sizeof(void*)*13 + 17, v_run_2210_);
v___x_2223_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
lean_object* v___x_2225_; 
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 0, v___x_2223_);
v___x_2225_ = v___x_2182_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
else
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
lean_dec(v___x_2187_);
lean_del_object(v___x_2182_);
lean_dec(v_a_2180_);
lean_dec_ref(v_opts_937_);
v___x_2229_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22));
v___x_2230_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2229_);
lean_dec_ref(v___x_2230_);
goto v___jp_989_;
}
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
lean_dec_ref(v_opts_937_);
v_a_2232_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2232_);
lean_dec_ref_known(v___x_2179_, 1);
v___x_2236_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2237_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2236_);
lean_dec_ref(v___x_2237_);
goto v___jp_2233_;
v___jp_2233_:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = lean_io_error_to_string(v_a_2232_);
v___x_2235_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2234_);
lean_dec_ref(v___x_2235_);
goto v___jp_995_;
}
}
}
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23));
v___x_2239_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2238_, v_optArg_x3f_939_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2283_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2242_ = v___x_2239_;
v_isShared_2243_ = v_isSharedCheck_2283_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2239_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2283_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v_leanOpts_2244_; lean_object* v_forwardedArgs_2245_; uint8_t v_component_2246_; uint8_t v_printPrefix_2247_; uint8_t v_printLibDir_2248_; uint8_t v_useStdin_2249_; uint8_t v_onlyDeps_2250_; uint8_t v_onlySrcDeps_2251_; uint8_t v_depsJson_2252_; lean_object* v_opts_2253_; uint32_t v_trustLevel_2254_; uint32_t v_numThreads_2255_; lean_object* v_setupFileName_x3f_2256_; lean_object* v_oleanFileName_x3f_2257_; lean_object* v_ileanFileName_x3f_2258_; lean_object* v_cFileName_x3f_2259_; lean_object* v_bcFileName_x3f_2260_; uint8_t v_jsonOutput_2261_; lean_object* v_errorOnKinds_2262_; uint8_t v_printStats_2263_; uint8_t v_run_2264_; lean_object* v_incrSaveFileName_x3f_2265_; lean_object* v_incrLoadFileName_x3f_2266_; lean_object* v_incrHeaderSaveFileName_x3f_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2281_; 
v_leanOpts_2244_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_2245_ = lean_ctor_get(v_opts_937_, 1);
v_component_2246_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_2247_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_2248_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_2249_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_2250_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2251_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_2252_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_2253_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_2254_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_2255_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_setupFileName_x3f_2256_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_2257_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_2258_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_2259_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_2260_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_2261_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_2262_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_2263_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_2264_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2265_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_2266_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_2267_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_2281_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_2281_ == 0)
{
lean_object* v_unused_2282_; 
v_unused_2282_ = lean_ctor_get(v_opts_937_, 3);
lean_dec(v_unused_2282_);
v___x_2269_ = v_opts_937_;
v_isShared_2270_ = v_isSharedCheck_2281_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2267_);
lean_inc(v_incrLoadFileName_x3f_2266_);
lean_inc(v_incrSaveFileName_x3f_2265_);
lean_inc(v_errorOnKinds_2262_);
lean_inc(v_bcFileName_x3f_2260_);
lean_inc(v_cFileName_x3f_2259_);
lean_inc(v_ileanFileName_x3f_2258_);
lean_inc(v_oleanFileName_x3f_2257_);
lean_inc(v_setupFileName_x3f_2256_);
lean_inc(v_opts_2253_);
lean_inc(v_forwardedArgs_2245_);
lean_inc(v_leanOpts_2244_);
lean_dec(v_opts_937_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2281_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2271_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24));
v___x_2272_ = lean_string_append(v___x_2271_, v_a_2240_);
v___x_2273_ = lean_array_push(v_forwardedArgs_2245_, v___x_2272_);
v___x_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2274_, 0, v_a_2240_);
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 3, v___x_2274_);
lean_ctor_set(v___x_2269_, 1, v___x_2273_);
v___x_2276_ = v___x_2269_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_leanOpts_2244_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v___x_2273_);
lean_ctor_set(v_reuseFailAlloc_2280_, 2, v_opts_2253_);
lean_ctor_set(v_reuseFailAlloc_2280_, 3, v___x_2274_);
lean_ctor_set(v_reuseFailAlloc_2280_, 4, v_setupFileName_x3f_2256_);
lean_ctor_set(v_reuseFailAlloc_2280_, 5, v_oleanFileName_x3f_2257_);
lean_ctor_set(v_reuseFailAlloc_2280_, 6, v_ileanFileName_x3f_2258_);
lean_ctor_set(v_reuseFailAlloc_2280_, 7, v_cFileName_x3f_2259_);
lean_ctor_set(v_reuseFailAlloc_2280_, 8, v_bcFileName_x3f_2260_);
lean_ctor_set(v_reuseFailAlloc_2280_, 9, v_errorOnKinds_2262_);
lean_ctor_set(v_reuseFailAlloc_2280_, 10, v_incrSaveFileName_x3f_2265_);
lean_ctor_set(v_reuseFailAlloc_2280_, 11, v_incrLoadFileName_x3f_2266_);
lean_ctor_set(v_reuseFailAlloc_2280_, 12, v_incrHeaderSaveFileName_x3f_2267_);
lean_ctor_set_uint8(v_reuseFailAlloc_2280_, sizeof(void*)*13 + 8, v_component_2246_);
lean_ctor_set_uint8(v_reuseFailAlloc_2280_, sizeof(void*)*13 + 9, v_printPrefix_2247_);
lean_ctor_set_uint8(v_reuseFailAlloc_2280_, sizeof(void*)*13 + 10, v_printLibDir_2248_);
lean_ctor_set_uint8(v_reuseFailAlloc_2280_, sizeof(void*)*13 + 11, v_useStdin_2249_);
lean_ctor_set_uint8(v_reuseFailAlloc_2280_, sizeof(void*)*13 + 12, v_onlyDeps_2250_);
lean_ctor_set_uint8(v_reuseFailAlloc_2280_, sizeof(void*)*13 + 13, v_onlySrcDeps_2251_);
lean_ctor_set_uint8(v_reuseFailAlloc_2280_, sizeof(void*)*13 + 14, v_depsJson_2252_);
lean_ctor_set_uint32(v_reuseFailAlloc_2280_, sizeof(void*)*13, v_trustLevel_2254_);
lean_ctor_set_uint32(v_reuseFailAlloc_2280_, sizeof(void*)*13 + 4, v_numThreads_2255_);
lean_ctor_set_uint8(v_reuseFailAlloc_2280_, sizeof(void*)*13 + 15, v_jsonOutput_2261_);
lean_ctor_set_uint8(v_reuseFailAlloc_2280_, sizeof(void*)*13 + 16, v_printStats_2263_);
lean_ctor_set_uint8(v_reuseFailAlloc_2280_, sizeof(void*)*13 + 17, v_run_2264_);
v___x_2276_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
lean_object* v___x_2278_; 
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 0, v___x_2276_);
v___x_2278_ = v___x_2242_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
lean_dec_ref(v_opts_937_);
v_a_2284_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2284_);
lean_dec_ref_known(v___x_2239_, 1);
v___x_2288_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2289_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2288_);
lean_dec_ref(v___x_2289_);
goto v___jp_2285_;
v___jp_2285_:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = lean_io_error_to_string(v_a_2284_);
v___x_2287_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2286_);
lean_dec_ref(v___x_2287_);
goto v___jp_1126_;
}
}
}
}
else
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25));
v___x_2291_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2290_, v_optArg_x3f_939_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2332_; 
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2294_ = v___x_2291_;
v_isShared_2295_ = v_isSharedCheck_2332_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2291_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2332_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v_leanOpts_2296_; lean_object* v_forwardedArgs_2297_; uint8_t v_component_2298_; uint8_t v_printPrefix_2299_; uint8_t v_printLibDir_2300_; uint8_t v_useStdin_2301_; uint8_t v_onlyDeps_2302_; uint8_t v_onlySrcDeps_2303_; uint8_t v_depsJson_2304_; lean_object* v_opts_2305_; uint32_t v_trustLevel_2306_; uint32_t v_numThreads_2307_; lean_object* v_rootDir_x3f_2308_; lean_object* v_setupFileName_x3f_2309_; lean_object* v_oleanFileName_x3f_2310_; lean_object* v_cFileName_x3f_2311_; lean_object* v_bcFileName_x3f_2312_; uint8_t v_jsonOutput_2313_; lean_object* v_errorOnKinds_2314_; uint8_t v_printStats_2315_; uint8_t v_run_2316_; lean_object* v_incrSaveFileName_x3f_2317_; lean_object* v_incrLoadFileName_x3f_2318_; lean_object* v_incrHeaderSaveFileName_x3f_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2330_; 
v_leanOpts_2296_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_2297_ = lean_ctor_get(v_opts_937_, 1);
v_component_2298_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_2299_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_2300_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_2301_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_2302_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2303_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_2304_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_2305_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_2306_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_2307_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2308_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_2309_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_2310_ = lean_ctor_get(v_opts_937_, 5);
v_cFileName_x3f_2311_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_2312_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_2313_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_2314_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_2315_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_2316_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2317_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_2318_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_2319_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_2330_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_2330_ == 0)
{
lean_object* v_unused_2331_; 
v_unused_2331_ = lean_ctor_get(v_opts_937_, 6);
lean_dec(v_unused_2331_);
v___x_2321_ = v_opts_937_;
v_isShared_2322_ = v_isSharedCheck_2330_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2319_);
lean_inc(v_incrLoadFileName_x3f_2318_);
lean_inc(v_incrSaveFileName_x3f_2317_);
lean_inc(v_errorOnKinds_2314_);
lean_inc(v_bcFileName_x3f_2312_);
lean_inc(v_cFileName_x3f_2311_);
lean_inc(v_oleanFileName_x3f_2310_);
lean_inc(v_setupFileName_x3f_2309_);
lean_inc(v_rootDir_x3f_2308_);
lean_inc(v_opts_2305_);
lean_inc(v_forwardedArgs_2297_);
lean_inc(v_leanOpts_2296_);
lean_dec(v_opts_937_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2330_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2323_; lean_object* v___x_2325_; 
v___x_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2323_, 0, v_a_2292_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 6, v___x_2323_);
v___x_2325_ = v___x_2321_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_leanOpts_2296_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v_forwardedArgs_2297_);
lean_ctor_set(v_reuseFailAlloc_2329_, 2, v_opts_2305_);
lean_ctor_set(v_reuseFailAlloc_2329_, 3, v_rootDir_x3f_2308_);
lean_ctor_set(v_reuseFailAlloc_2329_, 4, v_setupFileName_x3f_2309_);
lean_ctor_set(v_reuseFailAlloc_2329_, 5, v_oleanFileName_x3f_2310_);
lean_ctor_set(v_reuseFailAlloc_2329_, 6, v___x_2323_);
lean_ctor_set(v_reuseFailAlloc_2329_, 7, v_cFileName_x3f_2311_);
lean_ctor_set(v_reuseFailAlloc_2329_, 8, v_bcFileName_x3f_2312_);
lean_ctor_set(v_reuseFailAlloc_2329_, 9, v_errorOnKinds_2314_);
lean_ctor_set(v_reuseFailAlloc_2329_, 10, v_incrSaveFileName_x3f_2317_);
lean_ctor_set(v_reuseFailAlloc_2329_, 11, v_incrLoadFileName_x3f_2318_);
lean_ctor_set(v_reuseFailAlloc_2329_, 12, v_incrHeaderSaveFileName_x3f_2319_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*13 + 8, v_component_2298_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*13 + 9, v_printPrefix_2299_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*13 + 10, v_printLibDir_2300_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*13 + 11, v_useStdin_2301_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*13 + 12, v_onlyDeps_2302_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*13 + 13, v_onlySrcDeps_2303_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*13 + 14, v_depsJson_2304_);
lean_ctor_set_uint32(v_reuseFailAlloc_2329_, sizeof(void*)*13, v_trustLevel_2306_);
lean_ctor_set_uint32(v_reuseFailAlloc_2329_, sizeof(void*)*13 + 4, v_numThreads_2307_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*13 + 15, v_jsonOutput_2313_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*13 + 16, v_printStats_2315_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*13 + 17, v_run_2316_);
v___x_2325_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
lean_object* v___x_2327_; 
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 0, v___x_2325_);
v___x_2327_ = v___x_2294_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
lean_dec_ref(v_opts_937_);
v_a_2333_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2291_, 1);
v___x_2337_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2338_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2337_);
lean_dec_ref(v___x_2338_);
goto v___jp_2334_;
v___jp_2334_:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = lean_io_error_to_string(v_a_2333_);
v___x_2336_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2335_);
lean_dec_ref(v___x_2336_);
goto v___jp_986_;
}
}
}
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26));
v___x_2340_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2339_, v_optArg_x3f_939_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2381_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2343_ = v___x_2340_;
v_isShared_2344_ = v_isSharedCheck_2381_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2340_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2381_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v_leanOpts_2345_; lean_object* v_forwardedArgs_2346_; uint8_t v_component_2347_; uint8_t v_printPrefix_2348_; uint8_t v_printLibDir_2349_; uint8_t v_useStdin_2350_; uint8_t v_onlyDeps_2351_; uint8_t v_onlySrcDeps_2352_; uint8_t v_depsJson_2353_; lean_object* v_opts_2354_; uint32_t v_trustLevel_2355_; uint32_t v_numThreads_2356_; lean_object* v_rootDir_x3f_2357_; lean_object* v_setupFileName_x3f_2358_; lean_object* v_ileanFileName_x3f_2359_; lean_object* v_cFileName_x3f_2360_; lean_object* v_bcFileName_x3f_2361_; uint8_t v_jsonOutput_2362_; lean_object* v_errorOnKinds_2363_; uint8_t v_printStats_2364_; uint8_t v_run_2365_; lean_object* v_incrSaveFileName_x3f_2366_; lean_object* v_incrLoadFileName_x3f_2367_; lean_object* v_incrHeaderSaveFileName_x3f_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2379_; 
v_leanOpts_2345_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_2346_ = lean_ctor_get(v_opts_937_, 1);
v_component_2347_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_2348_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_2349_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_2350_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_2351_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2352_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_2353_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_2354_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_2355_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_2356_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2357_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_2358_ = lean_ctor_get(v_opts_937_, 4);
v_ileanFileName_x3f_2359_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_2360_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_2361_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_2362_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_2363_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_2364_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_2365_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2366_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_2367_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_2368_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_2379_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_2379_ == 0)
{
lean_object* v_unused_2380_; 
v_unused_2380_ = lean_ctor_get(v_opts_937_, 5);
lean_dec(v_unused_2380_);
v___x_2370_ = v_opts_937_;
v_isShared_2371_ = v_isSharedCheck_2379_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2368_);
lean_inc(v_incrLoadFileName_x3f_2367_);
lean_inc(v_incrSaveFileName_x3f_2366_);
lean_inc(v_errorOnKinds_2363_);
lean_inc(v_bcFileName_x3f_2361_);
lean_inc(v_cFileName_x3f_2360_);
lean_inc(v_ileanFileName_x3f_2359_);
lean_inc(v_setupFileName_x3f_2358_);
lean_inc(v_rootDir_x3f_2357_);
lean_inc(v_opts_2354_);
lean_inc(v_forwardedArgs_2346_);
lean_inc(v_leanOpts_2345_);
lean_dec(v_opts_937_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2379_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2372_; lean_object* v___x_2374_; 
v___x_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2372_, 0, v_a_2341_);
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 5, v___x_2372_);
v___x_2374_ = v___x_2370_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_leanOpts_2345_);
lean_ctor_set(v_reuseFailAlloc_2378_, 1, v_forwardedArgs_2346_);
lean_ctor_set(v_reuseFailAlloc_2378_, 2, v_opts_2354_);
lean_ctor_set(v_reuseFailAlloc_2378_, 3, v_rootDir_x3f_2357_);
lean_ctor_set(v_reuseFailAlloc_2378_, 4, v_setupFileName_x3f_2358_);
lean_ctor_set(v_reuseFailAlloc_2378_, 5, v___x_2372_);
lean_ctor_set(v_reuseFailAlloc_2378_, 6, v_ileanFileName_x3f_2359_);
lean_ctor_set(v_reuseFailAlloc_2378_, 7, v_cFileName_x3f_2360_);
lean_ctor_set(v_reuseFailAlloc_2378_, 8, v_bcFileName_x3f_2361_);
lean_ctor_set(v_reuseFailAlloc_2378_, 9, v_errorOnKinds_2363_);
lean_ctor_set(v_reuseFailAlloc_2378_, 10, v_incrSaveFileName_x3f_2366_);
lean_ctor_set(v_reuseFailAlloc_2378_, 11, v_incrLoadFileName_x3f_2367_);
lean_ctor_set(v_reuseFailAlloc_2378_, 12, v_incrHeaderSaveFileName_x3f_2368_);
lean_ctor_set_uint8(v_reuseFailAlloc_2378_, sizeof(void*)*13 + 8, v_component_2347_);
lean_ctor_set_uint8(v_reuseFailAlloc_2378_, sizeof(void*)*13 + 9, v_printPrefix_2348_);
lean_ctor_set_uint8(v_reuseFailAlloc_2378_, sizeof(void*)*13 + 10, v_printLibDir_2349_);
lean_ctor_set_uint8(v_reuseFailAlloc_2378_, sizeof(void*)*13 + 11, v_useStdin_2350_);
lean_ctor_set_uint8(v_reuseFailAlloc_2378_, sizeof(void*)*13 + 12, v_onlyDeps_2351_);
lean_ctor_set_uint8(v_reuseFailAlloc_2378_, sizeof(void*)*13 + 13, v_onlySrcDeps_2352_);
lean_ctor_set_uint8(v_reuseFailAlloc_2378_, sizeof(void*)*13 + 14, v_depsJson_2353_);
lean_ctor_set_uint32(v_reuseFailAlloc_2378_, sizeof(void*)*13, v_trustLevel_2355_);
lean_ctor_set_uint32(v_reuseFailAlloc_2378_, sizeof(void*)*13 + 4, v_numThreads_2356_);
lean_ctor_set_uint8(v_reuseFailAlloc_2378_, sizeof(void*)*13 + 15, v_jsonOutput_2362_);
lean_ctor_set_uint8(v_reuseFailAlloc_2378_, sizeof(void*)*13 + 16, v_printStats_2364_);
lean_ctor_set_uint8(v_reuseFailAlloc_2378_, sizeof(void*)*13 + 17, v_run_2365_);
v___x_2374_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
lean_object* v___x_2376_; 
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v___x_2374_);
v___x_2376_ = v___x_2343_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2374_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
lean_dec_ref(v_opts_937_);
v_a_2382_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2382_);
lean_dec_ref_known(v___x_2340_, 1);
v___x_2386_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2387_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2386_);
lean_dec_ref(v___x_2387_);
goto v___jp_2383_;
v___jp_2383_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2384_ = lean_io_error_to_string(v_a_2382_);
v___x_2385_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2384_);
lean_dec_ref(v___x_2385_);
goto v___jp_1132_;
}
}
}
}
else
{
lean_object* v_leanOpts_2388_; lean_object* v_forwardedArgs_2389_; uint8_t v_component_2390_; uint8_t v_printPrefix_2391_; uint8_t v_printLibDir_2392_; uint8_t v_useStdin_2393_; uint8_t v_onlyDeps_2394_; uint8_t v_onlySrcDeps_2395_; uint8_t v_depsJson_2396_; lean_object* v_opts_2397_; uint32_t v_trustLevel_2398_; uint32_t v_numThreads_2399_; lean_object* v_rootDir_x3f_2400_; lean_object* v_setupFileName_x3f_2401_; lean_object* v_oleanFileName_x3f_2402_; lean_object* v_ileanFileName_x3f_2403_; lean_object* v_cFileName_x3f_2404_; lean_object* v_bcFileName_x3f_2405_; uint8_t v_jsonOutput_2406_; lean_object* v_errorOnKinds_2407_; uint8_t v_printStats_2408_; lean_object* v_incrSaveFileName_x3f_2409_; lean_object* v_incrLoadFileName_x3f_2410_; lean_object* v_incrHeaderSaveFileName_x3f_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2421_; 
lean_dec(v_optArg_x3f_939_);
v_leanOpts_2388_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_2389_ = lean_ctor_get(v_opts_937_, 1);
v_component_2390_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_2391_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_2392_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_2393_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_2394_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2395_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_2396_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_2397_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_2398_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_2399_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2400_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_2401_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_2402_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_2403_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_2404_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_2405_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_2406_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_2407_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_2408_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_incrSaveFileName_x3f_2409_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_2410_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_2411_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_2421_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2413_ = v_opts_937_;
v_isShared_2414_ = v_isSharedCheck_2421_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2411_);
lean_inc(v_incrLoadFileName_x3f_2410_);
lean_inc(v_incrSaveFileName_x3f_2409_);
lean_inc(v_errorOnKinds_2407_);
lean_inc(v_bcFileName_x3f_2405_);
lean_inc(v_cFileName_x3f_2404_);
lean_inc(v_ileanFileName_x3f_2403_);
lean_inc(v_oleanFileName_x3f_2402_);
lean_inc(v_setupFileName_x3f_2401_);
lean_inc(v_rootDir_x3f_2400_);
lean_inc(v_opts_2397_);
lean_inc(v_forwardedArgs_2389_);
lean_inc(v_leanOpts_2388_);
lean_dec(v_opts_937_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2421_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2418_; 
v___x_2415_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_2416_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_2388_, v___x_2415_, v___x_1180_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 0, v___x_2416_);
v___x_2418_ = v___x_2413_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2416_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_forwardedArgs_2389_);
lean_ctor_set(v_reuseFailAlloc_2420_, 2, v_opts_2397_);
lean_ctor_set(v_reuseFailAlloc_2420_, 3, v_rootDir_x3f_2400_);
lean_ctor_set(v_reuseFailAlloc_2420_, 4, v_setupFileName_x3f_2401_);
lean_ctor_set(v_reuseFailAlloc_2420_, 5, v_oleanFileName_x3f_2402_);
lean_ctor_set(v_reuseFailAlloc_2420_, 6, v_ileanFileName_x3f_2403_);
lean_ctor_set(v_reuseFailAlloc_2420_, 7, v_cFileName_x3f_2404_);
lean_ctor_set(v_reuseFailAlloc_2420_, 8, v_bcFileName_x3f_2405_);
lean_ctor_set(v_reuseFailAlloc_2420_, 9, v_errorOnKinds_2407_);
lean_ctor_set(v_reuseFailAlloc_2420_, 10, v_incrSaveFileName_x3f_2409_);
lean_ctor_set(v_reuseFailAlloc_2420_, 11, v_incrLoadFileName_x3f_2410_);
lean_ctor_set(v_reuseFailAlloc_2420_, 12, v_incrHeaderSaveFileName_x3f_2411_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, sizeof(void*)*13 + 8, v_component_2390_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, sizeof(void*)*13 + 9, v_printPrefix_2391_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, sizeof(void*)*13 + 10, v_printLibDir_2392_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, sizeof(void*)*13 + 11, v_useStdin_2393_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, sizeof(void*)*13 + 12, v_onlyDeps_2394_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, sizeof(void*)*13 + 13, v_onlySrcDeps_2395_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, sizeof(void*)*13 + 14, v_depsJson_2396_);
lean_ctor_set_uint32(v_reuseFailAlloc_2420_, sizeof(void*)*13, v_trustLevel_2398_);
lean_ctor_set_uint32(v_reuseFailAlloc_2420_, sizeof(void*)*13 + 4, v_numThreads_2399_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, sizeof(void*)*13 + 15, v_jsonOutput_2406_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, sizeof(void*)*13 + 16, v_printStats_2408_);
v___x_2418_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
lean_object* v___x_2419_; 
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*13 + 17, v___x_1182_);
v___x_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
return v___x_2419_;
}
}
}
}
else
{
lean_object* v_leanOpts_2422_; lean_object* v_forwardedArgs_2423_; uint8_t v_component_2424_; uint8_t v_printPrefix_2425_; uint8_t v_printLibDir_2426_; uint8_t v_onlyDeps_2427_; uint8_t v_onlySrcDeps_2428_; uint8_t v_depsJson_2429_; lean_object* v_opts_2430_; uint32_t v_trustLevel_2431_; uint32_t v_numThreads_2432_; lean_object* v_rootDir_x3f_2433_; lean_object* v_setupFileName_x3f_2434_; lean_object* v_oleanFileName_x3f_2435_; lean_object* v_ileanFileName_x3f_2436_; lean_object* v_cFileName_x3f_2437_; lean_object* v_bcFileName_x3f_2438_; uint8_t v_jsonOutput_2439_; lean_object* v_errorOnKinds_2440_; uint8_t v_printStats_2441_; uint8_t v_run_2442_; lean_object* v_incrSaveFileName_x3f_2443_; lean_object* v_incrLoadFileName_x3f_2444_; lean_object* v_incrHeaderSaveFileName_x3f_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2453_; 
lean_dec(v_optArg_x3f_939_);
v_leanOpts_2422_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_2423_ = lean_ctor_get(v_opts_937_, 1);
v_component_2424_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_2425_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_2426_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_onlyDeps_2427_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2428_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_2429_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_2430_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_2431_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_2432_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2433_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_2434_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_2435_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_2436_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_2437_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_2438_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_2439_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_2440_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_2441_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_2442_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2443_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_2444_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_2445_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_2453_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2447_ = v_opts_937_;
v_isShared_2448_ = v_isSharedCheck_2453_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2445_);
lean_inc(v_incrLoadFileName_x3f_2444_);
lean_inc(v_incrSaveFileName_x3f_2443_);
lean_inc(v_errorOnKinds_2440_);
lean_inc(v_bcFileName_x3f_2438_);
lean_inc(v_cFileName_x3f_2437_);
lean_inc(v_ileanFileName_x3f_2436_);
lean_inc(v_oleanFileName_x3f_2435_);
lean_inc(v_setupFileName_x3f_2434_);
lean_inc(v_rootDir_x3f_2433_);
lean_inc(v_opts_2430_);
lean_inc(v_forwardedArgs_2423_);
lean_inc(v_leanOpts_2422_);
lean_dec(v_opts_937_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2453_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2448_ == 0)
{
v___x_2450_ = v___x_2447_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_leanOpts_2422_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_forwardedArgs_2423_);
lean_ctor_set(v_reuseFailAlloc_2452_, 2, v_opts_2430_);
lean_ctor_set(v_reuseFailAlloc_2452_, 3, v_rootDir_x3f_2433_);
lean_ctor_set(v_reuseFailAlloc_2452_, 4, v_setupFileName_x3f_2434_);
lean_ctor_set(v_reuseFailAlloc_2452_, 5, v_oleanFileName_x3f_2435_);
lean_ctor_set(v_reuseFailAlloc_2452_, 6, v_ileanFileName_x3f_2436_);
lean_ctor_set(v_reuseFailAlloc_2452_, 7, v_cFileName_x3f_2437_);
lean_ctor_set(v_reuseFailAlloc_2452_, 8, v_bcFileName_x3f_2438_);
lean_ctor_set(v_reuseFailAlloc_2452_, 9, v_errorOnKinds_2440_);
lean_ctor_set(v_reuseFailAlloc_2452_, 10, v_incrSaveFileName_x3f_2443_);
lean_ctor_set(v_reuseFailAlloc_2452_, 11, v_incrLoadFileName_x3f_2444_);
lean_ctor_set(v_reuseFailAlloc_2452_, 12, v_incrHeaderSaveFileName_x3f_2445_);
lean_ctor_set_uint8(v_reuseFailAlloc_2452_, sizeof(void*)*13 + 8, v_component_2424_);
lean_ctor_set_uint8(v_reuseFailAlloc_2452_, sizeof(void*)*13 + 9, v_printPrefix_2425_);
lean_ctor_set_uint8(v_reuseFailAlloc_2452_, sizeof(void*)*13 + 10, v_printLibDir_2426_);
lean_ctor_set_uint8(v_reuseFailAlloc_2452_, sizeof(void*)*13 + 12, v_onlyDeps_2427_);
lean_ctor_set_uint8(v_reuseFailAlloc_2452_, sizeof(void*)*13 + 13, v_onlySrcDeps_2428_);
lean_ctor_set_uint8(v_reuseFailAlloc_2452_, sizeof(void*)*13 + 14, v_depsJson_2429_);
lean_ctor_set_uint32(v_reuseFailAlloc_2452_, sizeof(void*)*13, v_trustLevel_2431_);
lean_ctor_set_uint32(v_reuseFailAlloc_2452_, sizeof(void*)*13 + 4, v_numThreads_2432_);
lean_ctor_set_uint8(v_reuseFailAlloc_2452_, sizeof(void*)*13 + 15, v_jsonOutput_2439_);
lean_ctor_set_uint8(v_reuseFailAlloc_2452_, sizeof(void*)*13 + 16, v_printStats_2441_);
lean_ctor_set_uint8(v_reuseFailAlloc_2452_, sizeof(void*)*13 + 17, v_run_2442_);
v___x_2450_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
lean_object* v___x_2451_; 
lean_ctor_set_uint8(v___x_2450_, sizeof(void*)*13 + 11, v___x_1180_);
v___x_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2450_);
return v___x_2451_;
}
}
}
}
else
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27));
v___x_2455_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2454_, v_optArg_x3f_939_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2517_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2458_ = v___x_2455_;
v_isShared_2459_ = v_isSharedCheck_2517_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2455_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2517_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2460_ = lean_unsigned_to_nat(0u);
v___x_2461_ = lean_string_utf8_byte_size(v_a_2456_);
lean_inc(v_a_2456_);
v___x_2462_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2462_, 0, v_a_2456_);
lean_ctor_set(v___x_2462_, 1, v___x_2460_);
lean_ctor_set(v___x_2462_, 2, v___x_2461_);
v___x_2463_ = l_String_Slice_toNat_x3f(v___x_2462_);
lean_dec_ref_known(v___x_2462_, 3);
if (lean_obj_tag(v___x_2463_) == 1)
{
lean_object* v_val_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; 
v_val_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_val_2464_);
lean_dec_ref_known(v___x_2463_, 1);
v___x_2465_ = lean_unsigned_to_nat(4u);
v___x_2466_ = lean_unsigned_to_nat(2u);
v___x_2467_ = lean_nat_shiftr(v_val_2464_, v___x_2466_);
lean_dec(v_val_2464_);
v___x_2468_ = lean_nat_mul(v___x_2467_, v___x_2465_);
lean_dec(v___x_2467_);
v___x_2469_ = lean_unsigned_to_nat(1024u);
v___x_2470_ = lean_nat_mul(v___x_2468_, v___x_2469_);
lean_dec(v___x_2468_);
v___x_2471_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28, &l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28_once, _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28);
v___x_2472_ = lean_nat_dec_lt(v___x_2470_, v___x_2471_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
lean_dec(v___x_2470_);
lean_del_object(v___x_2458_);
lean_dec(v_a_2456_);
lean_dec_ref(v_opts_937_);
v___x_2473_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29));
v___x_2474_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2473_);
lean_dec_ref(v___x_2474_);
goto v___jp_974_;
}
else
{
size_t v___x_2475_; lean_object* v___x_2476_; lean_object* v_leanOpts_2477_; lean_object* v_forwardedArgs_2478_; uint8_t v_component_2479_; uint8_t v_printPrefix_2480_; uint8_t v_printLibDir_2481_; uint8_t v_useStdin_2482_; uint8_t v_onlyDeps_2483_; uint8_t v_onlySrcDeps_2484_; uint8_t v_depsJson_2485_; lean_object* v_opts_2486_; uint32_t v_trustLevel_2487_; uint32_t v_numThreads_2488_; lean_object* v_rootDir_x3f_2489_; lean_object* v_setupFileName_x3f_2490_; lean_object* v_oleanFileName_x3f_2491_; lean_object* v_ileanFileName_x3f_2492_; lean_object* v_cFileName_x3f_2493_; lean_object* v_bcFileName_x3f_2494_; uint8_t v_jsonOutput_2495_; lean_object* v_errorOnKinds_2496_; uint8_t v_printStats_2497_; uint8_t v_run_2498_; lean_object* v_incrSaveFileName_x3f_2499_; lean_object* v_incrLoadFileName_x3f_2500_; lean_object* v_incrHeaderSaveFileName_x3f_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2514_; 
v___x_2475_ = lean_usize_of_nat(v___x_2470_);
lean_dec(v___x_2470_);
v___x_2476_ = lean_internal_set_thread_stack_size(v___x_2475_);
v_leanOpts_2477_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_2478_ = lean_ctor_get(v_opts_937_, 1);
v_component_2479_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_2480_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_2481_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_2482_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_2483_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2484_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_2485_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_2486_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_2487_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_2488_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2489_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_2490_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_2491_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_2492_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_2493_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_2494_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_2495_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_2496_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_2497_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_2498_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2499_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_2500_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_2501_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_2514_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2503_ = v_opts_937_;
v_isShared_2504_ = v_isSharedCheck_2514_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2501_);
lean_inc(v_incrLoadFileName_x3f_2500_);
lean_inc(v_incrSaveFileName_x3f_2499_);
lean_inc(v_errorOnKinds_2496_);
lean_inc(v_bcFileName_x3f_2494_);
lean_inc(v_cFileName_x3f_2493_);
lean_inc(v_ileanFileName_x3f_2492_);
lean_inc(v_oleanFileName_x3f_2491_);
lean_inc(v_setupFileName_x3f_2490_);
lean_inc(v_rootDir_x3f_2489_);
lean_inc(v_opts_2486_);
lean_inc(v_forwardedArgs_2478_);
lean_inc(v_leanOpts_2477_);
lean_dec(v_opts_937_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2514_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2509_; 
v___x_2505_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30));
v___x_2506_ = lean_string_append(v___x_2505_, v_a_2456_);
lean_dec(v_a_2456_);
v___x_2507_ = lean_array_push(v_forwardedArgs_2478_, v___x_2506_);
if (v_isShared_2504_ == 0)
{
lean_ctor_set(v___x_2503_, 1, v___x_2507_);
v___x_2509_ = v___x_2503_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_leanOpts_2477_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v___x_2507_);
lean_ctor_set(v_reuseFailAlloc_2513_, 2, v_opts_2486_);
lean_ctor_set(v_reuseFailAlloc_2513_, 3, v_rootDir_x3f_2489_);
lean_ctor_set(v_reuseFailAlloc_2513_, 4, v_setupFileName_x3f_2490_);
lean_ctor_set(v_reuseFailAlloc_2513_, 5, v_oleanFileName_x3f_2491_);
lean_ctor_set(v_reuseFailAlloc_2513_, 6, v_ileanFileName_x3f_2492_);
lean_ctor_set(v_reuseFailAlloc_2513_, 7, v_cFileName_x3f_2493_);
lean_ctor_set(v_reuseFailAlloc_2513_, 8, v_bcFileName_x3f_2494_);
lean_ctor_set(v_reuseFailAlloc_2513_, 9, v_errorOnKinds_2496_);
lean_ctor_set(v_reuseFailAlloc_2513_, 10, v_incrSaveFileName_x3f_2499_);
lean_ctor_set(v_reuseFailAlloc_2513_, 11, v_incrLoadFileName_x3f_2500_);
lean_ctor_set(v_reuseFailAlloc_2513_, 12, v_incrHeaderSaveFileName_x3f_2501_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, sizeof(void*)*13 + 8, v_component_2479_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, sizeof(void*)*13 + 9, v_printPrefix_2480_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, sizeof(void*)*13 + 10, v_printLibDir_2481_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, sizeof(void*)*13 + 11, v_useStdin_2482_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, sizeof(void*)*13 + 12, v_onlyDeps_2483_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, sizeof(void*)*13 + 13, v_onlySrcDeps_2484_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, sizeof(void*)*13 + 14, v_depsJson_2485_);
lean_ctor_set_uint32(v_reuseFailAlloc_2513_, sizeof(void*)*13, v_trustLevel_2487_);
lean_ctor_set_uint32(v_reuseFailAlloc_2513_, sizeof(void*)*13 + 4, v_numThreads_2488_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, sizeof(void*)*13 + 15, v_jsonOutput_2495_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, sizeof(void*)*13 + 16, v_printStats_2497_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, sizeof(void*)*13 + 17, v_run_2498_);
v___x_2509_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
lean_object* v___x_2511_; 
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 0, v___x_2509_);
v___x_2511_ = v___x_2458_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2509_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
}
else
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
lean_dec(v___x_2463_);
lean_del_object(v___x_2458_);
lean_dec(v_a_2456_);
lean_dec_ref(v_opts_937_);
v___x_2515_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31));
v___x_2516_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2515_);
lean_dec_ref(v___x_2516_);
goto v___jp_971_;
}
}
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
lean_dec_ref(v_opts_937_);
v_a_2518_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2518_);
lean_dec_ref_known(v___x_2455_, 1);
v___x_2522_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2523_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2522_);
lean_dec_ref(v___x_2523_);
goto v___jp_2519_;
v___jp_2519_:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = lean_io_error_to_string(v_a_2518_);
v___x_2521_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2520_);
lean_dec_ref(v___x_2521_);
goto v___jp_980_;
}
}
}
}
else
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2524_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32));
v___x_2525_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2524_, v_optArg_x3f_939_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2566_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2528_ = v___x_2525_;
v_isShared_2529_ = v_isSharedCheck_2566_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2525_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2566_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v_leanOpts_2530_; lean_object* v_forwardedArgs_2531_; uint8_t v_component_2532_; uint8_t v_printPrefix_2533_; uint8_t v_printLibDir_2534_; uint8_t v_useStdin_2535_; uint8_t v_onlyDeps_2536_; uint8_t v_onlySrcDeps_2537_; uint8_t v_depsJson_2538_; lean_object* v_opts_2539_; uint32_t v_trustLevel_2540_; uint32_t v_numThreads_2541_; lean_object* v_rootDir_x3f_2542_; lean_object* v_setupFileName_x3f_2543_; lean_object* v_oleanFileName_x3f_2544_; lean_object* v_ileanFileName_x3f_2545_; lean_object* v_cFileName_x3f_2546_; uint8_t v_jsonOutput_2547_; lean_object* v_errorOnKinds_2548_; uint8_t v_printStats_2549_; uint8_t v_run_2550_; lean_object* v_incrSaveFileName_x3f_2551_; lean_object* v_incrLoadFileName_x3f_2552_; lean_object* v_incrHeaderSaveFileName_x3f_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2564_; 
v_leanOpts_2530_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_2531_ = lean_ctor_get(v_opts_937_, 1);
v_component_2532_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_2533_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_2534_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_2535_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_2536_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2537_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_2538_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_2539_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_2540_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_2541_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2542_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_2543_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_2544_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_2545_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_2546_ = lean_ctor_get(v_opts_937_, 7);
v_jsonOutput_2547_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_2548_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_2549_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_2550_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2551_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_2552_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_2553_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_2564_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_2564_ == 0)
{
lean_object* v_unused_2565_; 
v_unused_2565_ = lean_ctor_get(v_opts_937_, 8);
lean_dec(v_unused_2565_);
v___x_2555_ = v_opts_937_;
v_isShared_2556_ = v_isSharedCheck_2564_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2553_);
lean_inc(v_incrLoadFileName_x3f_2552_);
lean_inc(v_incrSaveFileName_x3f_2551_);
lean_inc(v_errorOnKinds_2548_);
lean_inc(v_cFileName_x3f_2546_);
lean_inc(v_ileanFileName_x3f_2545_);
lean_inc(v_oleanFileName_x3f_2544_);
lean_inc(v_setupFileName_x3f_2543_);
lean_inc(v_rootDir_x3f_2542_);
lean_inc(v_opts_2539_);
lean_inc(v_forwardedArgs_2531_);
lean_inc(v_leanOpts_2530_);
lean_dec(v_opts_937_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2564_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2557_; lean_object* v___x_2559_; 
v___x_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2557_, 0, v_a_2526_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 8, v___x_2557_);
v___x_2559_ = v___x_2555_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_leanOpts_2530_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v_forwardedArgs_2531_);
lean_ctor_set(v_reuseFailAlloc_2563_, 2, v_opts_2539_);
lean_ctor_set(v_reuseFailAlloc_2563_, 3, v_rootDir_x3f_2542_);
lean_ctor_set(v_reuseFailAlloc_2563_, 4, v_setupFileName_x3f_2543_);
lean_ctor_set(v_reuseFailAlloc_2563_, 5, v_oleanFileName_x3f_2544_);
lean_ctor_set(v_reuseFailAlloc_2563_, 6, v_ileanFileName_x3f_2545_);
lean_ctor_set(v_reuseFailAlloc_2563_, 7, v_cFileName_x3f_2546_);
lean_ctor_set(v_reuseFailAlloc_2563_, 8, v___x_2557_);
lean_ctor_set(v_reuseFailAlloc_2563_, 9, v_errorOnKinds_2548_);
lean_ctor_set(v_reuseFailAlloc_2563_, 10, v_incrSaveFileName_x3f_2551_);
lean_ctor_set(v_reuseFailAlloc_2563_, 11, v_incrLoadFileName_x3f_2552_);
lean_ctor_set(v_reuseFailAlloc_2563_, 12, v_incrHeaderSaveFileName_x3f_2553_);
lean_ctor_set_uint8(v_reuseFailAlloc_2563_, sizeof(void*)*13 + 8, v_component_2532_);
lean_ctor_set_uint8(v_reuseFailAlloc_2563_, sizeof(void*)*13 + 9, v_printPrefix_2533_);
lean_ctor_set_uint8(v_reuseFailAlloc_2563_, sizeof(void*)*13 + 10, v_printLibDir_2534_);
lean_ctor_set_uint8(v_reuseFailAlloc_2563_, sizeof(void*)*13 + 11, v_useStdin_2535_);
lean_ctor_set_uint8(v_reuseFailAlloc_2563_, sizeof(void*)*13 + 12, v_onlyDeps_2536_);
lean_ctor_set_uint8(v_reuseFailAlloc_2563_, sizeof(void*)*13 + 13, v_onlySrcDeps_2537_);
lean_ctor_set_uint8(v_reuseFailAlloc_2563_, sizeof(void*)*13 + 14, v_depsJson_2538_);
lean_ctor_set_uint32(v_reuseFailAlloc_2563_, sizeof(void*)*13, v_trustLevel_2540_);
lean_ctor_set_uint32(v_reuseFailAlloc_2563_, sizeof(void*)*13 + 4, v_numThreads_2541_);
lean_ctor_set_uint8(v_reuseFailAlloc_2563_, sizeof(void*)*13 + 15, v_jsonOutput_2547_);
lean_ctor_set_uint8(v_reuseFailAlloc_2563_, sizeof(void*)*13 + 16, v_printStats_2549_);
lean_ctor_set_uint8(v_reuseFailAlloc_2563_, sizeof(void*)*13 + 17, v_run_2550_);
v___x_2559_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
lean_object* v___x_2561_; 
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 0, v___x_2559_);
v___x_2561_ = v___x_2528_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2559_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
lean_dec_ref(v_opts_937_);
v_a_2567_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2567_);
lean_dec_ref_known(v___x_2525_, 1);
v___x_2571_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2572_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2571_);
lean_dec_ref(v___x_2572_);
goto v___jp_2568_;
v___jp_2568_:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2569_ = lean_io_error_to_string(v_a_2567_);
v___x_2570_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2569_);
lean_dec_ref(v___x_2570_);
goto v___jp_1138_;
}
}
}
}
else
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2573_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33));
v___x_2574_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2573_, v_optArg_x3f_939_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2615_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2577_ = v___x_2574_;
v_isShared_2578_ = v_isSharedCheck_2615_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2574_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2615_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v_leanOpts_2579_; lean_object* v_forwardedArgs_2580_; uint8_t v_component_2581_; uint8_t v_printPrefix_2582_; uint8_t v_printLibDir_2583_; uint8_t v_useStdin_2584_; uint8_t v_onlyDeps_2585_; uint8_t v_onlySrcDeps_2586_; uint8_t v_depsJson_2587_; lean_object* v_opts_2588_; uint32_t v_trustLevel_2589_; uint32_t v_numThreads_2590_; lean_object* v_rootDir_x3f_2591_; lean_object* v_setupFileName_x3f_2592_; lean_object* v_oleanFileName_x3f_2593_; lean_object* v_ileanFileName_x3f_2594_; lean_object* v_bcFileName_x3f_2595_; uint8_t v_jsonOutput_2596_; lean_object* v_errorOnKinds_2597_; uint8_t v_printStats_2598_; uint8_t v_run_2599_; lean_object* v_incrSaveFileName_x3f_2600_; lean_object* v_incrLoadFileName_x3f_2601_; lean_object* v_incrHeaderSaveFileName_x3f_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2613_; 
v_leanOpts_2579_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_2580_ = lean_ctor_get(v_opts_937_, 1);
v_component_2581_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_2582_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_2583_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_2584_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_2585_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2586_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_2587_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_2588_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_2589_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_numThreads_2590_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2591_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_2592_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_2593_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_2594_ = lean_ctor_get(v_opts_937_, 6);
v_bcFileName_x3f_2595_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_2596_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_2597_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_2598_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_2599_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2600_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_2601_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_2602_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_2613_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_2613_ == 0)
{
lean_object* v_unused_2614_; 
v_unused_2614_ = lean_ctor_get(v_opts_937_, 7);
lean_dec(v_unused_2614_);
v___x_2604_ = v_opts_937_;
v_isShared_2605_ = v_isSharedCheck_2613_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2602_);
lean_inc(v_incrLoadFileName_x3f_2601_);
lean_inc(v_incrSaveFileName_x3f_2600_);
lean_inc(v_errorOnKinds_2597_);
lean_inc(v_bcFileName_x3f_2595_);
lean_inc(v_ileanFileName_x3f_2594_);
lean_inc(v_oleanFileName_x3f_2593_);
lean_inc(v_setupFileName_x3f_2592_);
lean_inc(v_rootDir_x3f_2591_);
lean_inc(v_opts_2588_);
lean_inc(v_forwardedArgs_2580_);
lean_inc(v_leanOpts_2579_);
lean_dec(v_opts_937_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2613_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2606_; lean_object* v___x_2608_; 
v___x_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2606_, 0, v_a_2575_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 7, v___x_2606_);
v___x_2608_ = v___x_2604_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_leanOpts_2579_);
lean_ctor_set(v_reuseFailAlloc_2612_, 1, v_forwardedArgs_2580_);
lean_ctor_set(v_reuseFailAlloc_2612_, 2, v_opts_2588_);
lean_ctor_set(v_reuseFailAlloc_2612_, 3, v_rootDir_x3f_2591_);
lean_ctor_set(v_reuseFailAlloc_2612_, 4, v_setupFileName_x3f_2592_);
lean_ctor_set(v_reuseFailAlloc_2612_, 5, v_oleanFileName_x3f_2593_);
lean_ctor_set(v_reuseFailAlloc_2612_, 6, v_ileanFileName_x3f_2594_);
lean_ctor_set(v_reuseFailAlloc_2612_, 7, v___x_2606_);
lean_ctor_set(v_reuseFailAlloc_2612_, 8, v_bcFileName_x3f_2595_);
lean_ctor_set(v_reuseFailAlloc_2612_, 9, v_errorOnKinds_2597_);
lean_ctor_set(v_reuseFailAlloc_2612_, 10, v_incrSaveFileName_x3f_2600_);
lean_ctor_set(v_reuseFailAlloc_2612_, 11, v_incrLoadFileName_x3f_2601_);
lean_ctor_set(v_reuseFailAlloc_2612_, 12, v_incrHeaderSaveFileName_x3f_2602_);
lean_ctor_set_uint8(v_reuseFailAlloc_2612_, sizeof(void*)*13 + 8, v_component_2581_);
lean_ctor_set_uint8(v_reuseFailAlloc_2612_, sizeof(void*)*13 + 9, v_printPrefix_2582_);
lean_ctor_set_uint8(v_reuseFailAlloc_2612_, sizeof(void*)*13 + 10, v_printLibDir_2583_);
lean_ctor_set_uint8(v_reuseFailAlloc_2612_, sizeof(void*)*13 + 11, v_useStdin_2584_);
lean_ctor_set_uint8(v_reuseFailAlloc_2612_, sizeof(void*)*13 + 12, v_onlyDeps_2585_);
lean_ctor_set_uint8(v_reuseFailAlloc_2612_, sizeof(void*)*13 + 13, v_onlySrcDeps_2586_);
lean_ctor_set_uint8(v_reuseFailAlloc_2612_, sizeof(void*)*13 + 14, v_depsJson_2587_);
lean_ctor_set_uint32(v_reuseFailAlloc_2612_, sizeof(void*)*13, v_trustLevel_2589_);
lean_ctor_set_uint32(v_reuseFailAlloc_2612_, sizeof(void*)*13 + 4, v_numThreads_2590_);
lean_ctor_set_uint8(v_reuseFailAlloc_2612_, sizeof(void*)*13 + 15, v_jsonOutput_2596_);
lean_ctor_set_uint8(v_reuseFailAlloc_2612_, sizeof(void*)*13 + 16, v_printStats_2598_);
lean_ctor_set_uint8(v_reuseFailAlloc_2612_, sizeof(void*)*13 + 17, v_run_2599_);
v___x_2608_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
lean_object* v___x_2610_; 
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2608_);
v___x_2610_ = v___x_2577_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2608_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
lean_dec_ref(v_opts_937_);
v_a_2616_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_a_2616_);
lean_dec_ref_known(v___x_2574_, 1);
v___x_2620_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2621_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2620_);
lean_dec_ref(v___x_2621_);
goto v___jp_2617_;
v___jp_2617_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2618_ = lean_io_error_to_string(v_a_2616_);
v___x_2619_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2618_);
lean_dec_ref(v___x_2619_);
goto v___jp_968_;
}
}
}
}
else
{
lean_object* v___x_2622_; lean_object* v___x_2623_; 
lean_dec(v_optArg_x3f_939_);
lean_dec_ref(v_opts_937_);
v___x_2622_ = l___private_Lean_Shell_0__Lean_featuresString;
v___x_2623_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2622_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2631_; 
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2631_ == 0)
{
lean_object* v_unused_2632_; 
v_unused_2632_ = lean_ctor_get(v___x_2623_, 0);
lean_dec(v_unused_2632_);
v___x_2625_ = v___x_2623_;
v_isShared_2626_ = v_isSharedCheck_2631_;
goto v_resetjp_2624_;
}
else
{
lean_dec(v___x_2623_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2631_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2627_; lean_object* v___x_2629_; 
v___x_2627_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2626_ == 0)
{
lean_ctor_set_tag(v___x_2625_, 1);
lean_ctor_set(v___x_2625_, 0, v___x_2627_);
v___x_2629_ = v___x_2625_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2627_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v_a_2633_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_a_2633_);
lean_dec_ref_known(v___x_2623_, 1);
v___x_2637_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2638_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2637_);
lean_dec_ref(v___x_2638_);
goto v___jp_2634_;
v___jp_2634_:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2635_ = lean_io_error_to_string(v_a_2633_);
v___x_2636_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2635_);
lean_dec_ref(v___x_2636_);
goto v___jp_1144_;
}
}
}
}
else
{
lean_object* v___x_2639_; 
lean_dec(v_optArg_x3f_939_);
lean_dec_ref(v_opts_937_);
v___x_2639_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1168_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2647_; 
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2647_ == 0)
{
lean_object* v_unused_2648_; 
v_unused_2648_ = lean_ctor_get(v___x_2639_, 0);
lean_dec(v_unused_2648_);
v___x_2641_ = v___x_2639_;
v_isShared_2642_ = v_isSharedCheck_2647_;
goto v_resetjp_2640_;
}
else
{
lean_dec(v___x_2639_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2647_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2643_; lean_object* v___x_2645_; 
v___x_2643_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2642_ == 0)
{
lean_ctor_set_tag(v___x_2641_, 1);
lean_ctor_set(v___x_2641_, 0, v___x_2643_);
v___x_2645_ = v___x_2641_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
else
{
lean_object* v_a_2649_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v_a_2649_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_a_2649_);
lean_dec_ref_known(v___x_2639_, 1);
v___x_2653_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2654_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2653_);
lean_dec_ref(v___x_2654_);
goto v___jp_2650_;
v___jp_2650_:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = lean_io_error_to_string(v_a_2649_);
v___x_2652_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2651_);
lean_dec_ref(v___x_2652_);
goto v___jp_962_;
}
}
}
}
else
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
lean_dec(v_optArg_x3f_939_);
lean_dec_ref(v_opts_937_);
v___x_2655_ = l_Lean_githash;
v___x_2656_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2655_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2664_; 
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2664_ == 0)
{
lean_object* v_unused_2665_; 
v_unused_2665_ = lean_ctor_get(v___x_2656_, 0);
lean_dec(v_unused_2665_);
v___x_2658_ = v___x_2656_;
v_isShared_2659_ = v_isSharedCheck_2664_;
goto v_resetjp_2657_;
}
else
{
lean_dec(v___x_2656_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2664_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2660_; lean_object* v___x_2662_; 
v___x_2660_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2659_ == 0)
{
lean_ctor_set_tag(v___x_2658_, 1);
lean_ctor_set(v___x_2658_, 0, v___x_2660_);
v___x_2662_ = v___x_2658_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2660_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
else
{
lean_object* v_a_2666_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v_a_2666_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2666_);
lean_dec_ref_known(v___x_2656_, 1);
v___x_2670_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2671_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2670_);
lean_dec_ref(v___x_2671_);
goto v___jp_2667_;
v___jp_2667_:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2668_ = lean_io_error_to_string(v_a_2666_);
v___x_2669_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2668_);
lean_dec_ref(v___x_2669_);
goto v___jp_1150_;
}
}
}
}
else
{
lean_object* v___x_2672_; lean_object* v___x_2673_; 
lean_dec(v_optArg_x3f_939_);
lean_dec_ref(v_opts_937_);
v___x_2672_ = l___private_Lean_Shell_0__Lean_shortVersionString;
v___x_2673_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2672_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2681_; 
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2681_ == 0)
{
lean_object* v_unused_2682_; 
v_unused_2682_ = lean_ctor_get(v___x_2673_, 0);
lean_dec(v_unused_2682_);
v___x_2675_ = v___x_2673_;
v_isShared_2676_ = v_isSharedCheck_2681_;
goto v_resetjp_2674_;
}
else
{
lean_dec(v___x_2673_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2681_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2677_; lean_object* v___x_2679_; 
v___x_2677_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2676_ == 0)
{
lean_ctor_set_tag(v___x_2675_, 1);
lean_ctor_set(v___x_2675_, 0, v___x_2677_);
v___x_2679_ = v___x_2675_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2677_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v_a_2683_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2673_, 1);
v___x_2687_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2688_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2687_);
lean_dec_ref(v___x_2688_);
goto v___jp_2684_;
v___jp_2684_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2685_ = lean_io_error_to_string(v_a_2683_);
v___x_2686_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2685_);
lean_dec_ref(v___x_2686_);
goto v___jp_956_;
}
}
}
}
else
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
lean_dec(v_optArg_x3f_939_);
lean_dec_ref(v_opts_937_);
v___x_2689_ = l___private_Lean_Shell_0__Lean_versionHeader;
v___x_2690_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2689_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2698_; 
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2698_ == 0)
{
lean_object* v_unused_2699_; 
v_unused_2699_ = lean_ctor_get(v___x_2690_, 0);
lean_dec(v_unused_2699_);
v___x_2692_ = v___x_2690_;
v_isShared_2693_ = v_isSharedCheck_2698_;
goto v_resetjp_2691_;
}
else
{
lean_dec(v___x_2690_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2698_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2694_; lean_object* v___x_2696_; 
v___x_2694_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2693_ == 0)
{
lean_ctor_set_tag(v___x_2692_, 1);
lean_ctor_set(v___x_2692_, 0, v___x_2694_);
v___x_2696_ = v___x_2692_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2694_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v_a_2700_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2700_);
lean_dec_ref_known(v___x_2690_, 1);
v___x_2704_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2705_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2704_);
lean_dec_ref(v___x_2705_);
goto v___jp_2701_;
v___jp_2701_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2702_ = lean_io_error_to_string(v_a_2700_);
v___x_2703_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2702_);
lean_dec_ref(v___x_2703_);
goto v___jp_1156_;
}
}
}
}
else
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34));
v___x_2707_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2706_, v_optArg_x3f_939_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2761_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2710_ = v___x_2707_;
v_isShared_2711_ = v_isSharedCheck_2761_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2707_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2761_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2712_ = lean_unsigned_to_nat(0u);
v___x_2713_ = lean_string_utf8_byte_size(v_a_2708_);
lean_inc(v_a_2708_);
v___x_2714_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2714_, 0, v_a_2708_);
lean_ctor_set(v___x_2714_, 1, v___x_2712_);
lean_ctor_set(v___x_2714_, 2, v___x_2713_);
v___x_2715_ = l_String_Slice_toNat_x3f(v___x_2714_);
lean_dec_ref_known(v___x_2714_, 3);
if (lean_obj_tag(v___x_2715_) == 1)
{
lean_object* v_val_2716_; lean_object* v___x_2717_; uint8_t v___x_2718_; 
v_val_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_val_2716_);
lean_dec_ref_known(v___x_2715_, 1);
v___x_2717_ = lean_cstr_to_nat("4294967296");
v___x_2718_ = lean_nat_dec_lt(v_val_2716_, v___x_2717_);
if (v___x_2718_ == 0)
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
lean_dec(v_val_2716_);
lean_del_object(v___x_2710_);
lean_dec(v_a_2708_);
lean_dec_ref(v_opts_937_);
v___x_2719_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__35));
v___x_2720_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2719_);
lean_dec_ref(v___x_2720_);
goto v___jp_944_;
}
else
{
lean_object* v_leanOpts_2721_; lean_object* v_forwardedArgs_2722_; uint8_t v_component_2723_; uint8_t v_printPrefix_2724_; uint8_t v_printLibDir_2725_; uint8_t v_useStdin_2726_; uint8_t v_onlyDeps_2727_; uint8_t v_onlySrcDeps_2728_; uint8_t v_depsJson_2729_; lean_object* v_opts_2730_; uint32_t v_trustLevel_2731_; lean_object* v_rootDir_x3f_2732_; lean_object* v_setupFileName_x3f_2733_; lean_object* v_oleanFileName_x3f_2734_; lean_object* v_ileanFileName_x3f_2735_; lean_object* v_cFileName_x3f_2736_; lean_object* v_bcFileName_x3f_2737_; uint8_t v_jsonOutput_2738_; lean_object* v_errorOnKinds_2739_; uint8_t v_printStats_2740_; uint8_t v_run_2741_; lean_object* v_incrSaveFileName_x3f_2742_; lean_object* v_incrLoadFileName_x3f_2743_; lean_object* v_incrHeaderSaveFileName_x3f_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2758_; 
v_leanOpts_2721_ = lean_ctor_get(v_opts_937_, 0);
v_forwardedArgs_2722_ = lean_ctor_get(v_opts_937_, 1);
v_component_2723_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 8);
v_printPrefix_2724_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 9);
v_printLibDir_2725_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 10);
v_useStdin_2726_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 11);
v_onlyDeps_2727_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2728_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 13);
v_depsJson_2729_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 14);
v_opts_2730_ = lean_ctor_get(v_opts_937_, 2);
v_trustLevel_2731_ = lean_ctor_get_uint32(v_opts_937_, sizeof(void*)*13);
v_rootDir_x3f_2732_ = lean_ctor_get(v_opts_937_, 3);
v_setupFileName_x3f_2733_ = lean_ctor_get(v_opts_937_, 4);
v_oleanFileName_x3f_2734_ = lean_ctor_get(v_opts_937_, 5);
v_ileanFileName_x3f_2735_ = lean_ctor_get(v_opts_937_, 6);
v_cFileName_x3f_2736_ = lean_ctor_get(v_opts_937_, 7);
v_bcFileName_x3f_2737_ = lean_ctor_get(v_opts_937_, 8);
v_jsonOutput_2738_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 15);
v_errorOnKinds_2739_ = lean_ctor_get(v_opts_937_, 9);
v_printStats_2740_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 16);
v_run_2741_ = lean_ctor_get_uint8(v_opts_937_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2742_ = lean_ctor_get(v_opts_937_, 10);
v_incrLoadFileName_x3f_2743_ = lean_ctor_get(v_opts_937_, 11);
v_incrHeaderSaveFileName_x3f_2744_ = lean_ctor_get(v_opts_937_, 12);
v_isSharedCheck_2758_ = !lean_is_exclusive(v_opts_937_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2746_ = v_opts_937_;
v_isShared_2747_ = v_isSharedCheck_2758_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2744_);
lean_inc(v_incrLoadFileName_x3f_2743_);
lean_inc(v_incrSaveFileName_x3f_2742_);
lean_inc(v_errorOnKinds_2739_);
lean_inc(v_bcFileName_x3f_2737_);
lean_inc(v_cFileName_x3f_2736_);
lean_inc(v_ileanFileName_x3f_2735_);
lean_inc(v_oleanFileName_x3f_2734_);
lean_inc(v_setupFileName_x3f_2733_);
lean_inc(v_rootDir_x3f_2732_);
lean_inc(v_opts_2730_);
lean_inc(v_forwardedArgs_2722_);
lean_inc(v_leanOpts_2721_);
lean_dec(v_opts_937_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2758_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
uint32_t v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2753_; 
v___x_2748_ = lean_uint32_of_nat(v_val_2716_);
lean_dec(v_val_2716_);
v___x_2749_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__36));
v___x_2750_ = lean_string_append(v___x_2749_, v_a_2708_);
lean_dec(v_a_2708_);
v___x_2751_ = lean_array_push(v_forwardedArgs_2722_, v___x_2750_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 1, v___x_2751_);
v___x_2753_ = v___x_2746_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_leanOpts_2721_);
lean_ctor_set(v_reuseFailAlloc_2757_, 1, v___x_2751_);
lean_ctor_set(v_reuseFailAlloc_2757_, 2, v_opts_2730_);
lean_ctor_set(v_reuseFailAlloc_2757_, 3, v_rootDir_x3f_2732_);
lean_ctor_set(v_reuseFailAlloc_2757_, 4, v_setupFileName_x3f_2733_);
lean_ctor_set(v_reuseFailAlloc_2757_, 5, v_oleanFileName_x3f_2734_);
lean_ctor_set(v_reuseFailAlloc_2757_, 6, v_ileanFileName_x3f_2735_);
lean_ctor_set(v_reuseFailAlloc_2757_, 7, v_cFileName_x3f_2736_);
lean_ctor_set(v_reuseFailAlloc_2757_, 8, v_bcFileName_x3f_2737_);
lean_ctor_set(v_reuseFailAlloc_2757_, 9, v_errorOnKinds_2739_);
lean_ctor_set(v_reuseFailAlloc_2757_, 10, v_incrSaveFileName_x3f_2742_);
lean_ctor_set(v_reuseFailAlloc_2757_, 11, v_incrLoadFileName_x3f_2743_);
lean_ctor_set(v_reuseFailAlloc_2757_, 12, v_incrHeaderSaveFileName_x3f_2744_);
lean_ctor_set_uint8(v_reuseFailAlloc_2757_, sizeof(void*)*13 + 8, v_component_2723_);
lean_ctor_set_uint8(v_reuseFailAlloc_2757_, sizeof(void*)*13 + 9, v_printPrefix_2724_);
lean_ctor_set_uint8(v_reuseFailAlloc_2757_, sizeof(void*)*13 + 10, v_printLibDir_2725_);
lean_ctor_set_uint8(v_reuseFailAlloc_2757_, sizeof(void*)*13 + 11, v_useStdin_2726_);
lean_ctor_set_uint8(v_reuseFailAlloc_2757_, sizeof(void*)*13 + 12, v_onlyDeps_2727_);
lean_ctor_set_uint8(v_reuseFailAlloc_2757_, sizeof(void*)*13 + 13, v_onlySrcDeps_2728_);
lean_ctor_set_uint8(v_reuseFailAlloc_2757_, sizeof(void*)*13 + 14, v_depsJson_2729_);
lean_ctor_set_uint32(v_reuseFailAlloc_2757_, sizeof(void*)*13, v_trustLevel_2731_);
lean_ctor_set_uint8(v_reuseFailAlloc_2757_, sizeof(void*)*13 + 15, v_jsonOutput_2738_);
lean_ctor_set_uint8(v_reuseFailAlloc_2757_, sizeof(void*)*13 + 16, v_printStats_2740_);
lean_ctor_set_uint8(v_reuseFailAlloc_2757_, sizeof(void*)*13 + 17, v_run_2741_);
v___x_2753_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
lean_object* v___x_2755_; 
lean_ctor_set_uint32(v___x_2753_, sizeof(void*)*13 + 4, v___x_2748_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 0, v___x_2753_);
v___x_2755_ = v___x_2710_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2753_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
}
else
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
lean_dec(v___x_2715_);
lean_del_object(v___x_2710_);
lean_dec(v_a_2708_);
lean_dec_ref(v_opts_937_);
v___x_2759_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__37));
v___x_2760_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2759_);
lean_dec_ref(v___x_2760_);
goto v___jp_941_;
}
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
lean_dec_ref(v_opts_937_);
v_a_2762_ = lean_ctor_get(v___x_2707_, 0);
lean_inc(v_a_2762_);
lean_dec_ref_known(v___x_2707_, 1);
v___x_2766_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2767_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2766_);
lean_dec_ref(v___x_2767_);
goto v___jp_2763_;
v___jp_2763_:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2764_ = lean_io_error_to_string(v_a_2762_);
v___x_2765_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2764_);
lean_dec_ref(v___x_2765_);
goto v___jp_950_;
}
}
}
}
else
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
lean_dec(v_optArg_x3f_939_);
v___x_2768_ = lean_internal_set_exit_on_panic(v___x_1160_);
v___x_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2769_, 0, v_opts_937_);
return v___x_2769_;
}
v___jp_941_:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
return v___x_943_;
}
v___jp_944_:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
return v___x_946_;
}
v___jp_947_:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
return v___x_949_;
}
v___jp_950_:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_952_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_951_);
lean_dec_ref(v___x_952_);
goto v___jp_947_;
}
v___jp_953_:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
return v___x_955_;
}
v___jp_956_:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_958_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_957_);
lean_dec_ref(v___x_958_);
goto v___jp_953_;
}
v___jp_959_:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
return v___x_961_;
}
v___jp_962_:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_964_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_963_);
lean_dec_ref(v___x_964_);
goto v___jp_959_;
}
v___jp_965_:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
return v___x_967_;
}
v___jp_968_:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_970_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_969_);
lean_dec_ref(v___x_970_);
goto v___jp_965_;
}
v___jp_971_:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
return v___x_973_;
}
v___jp_974_:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
return v___x_976_;
}
v___jp_977_:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
return v___x_979_;
}
v___jp_980_:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_982_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_981_);
lean_dec_ref(v___x_982_);
goto v___jp_977_;
}
v___jp_983_:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
return v___x_985_;
}
v___jp_986_:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_988_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_987_);
lean_dec_ref(v___x_988_);
goto v___jp_983_;
}
v___jp_989_:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
return v___x_991_;
}
v___jp_992_:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
return v___x_994_;
}
v___jp_995_:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_997_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_996_);
lean_dec_ref(v___x_997_);
goto v___jp_992_;
}
v___jp_998_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
return v___x_1000_;
}
v___jp_1001_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
return v___x_1003_;
}
v___jp_1004_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
return v___x_1006_;
}
v___jp_1007_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1009_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1008_);
lean_dec_ref(v___x_1009_);
goto v___jp_1004_;
}
v___jp_1010_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
return v___x_1012_;
}
v___jp_1013_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1015_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1014_);
lean_dec_ref(v___x_1015_);
goto v___jp_1010_;
}
v___jp_1016_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
return v___x_1018_;
}
v___jp_1019_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1021_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1020_);
lean_dec_ref(v___x_1021_);
goto v___jp_1016_;
}
v___jp_1022_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
return v___x_1024_;
}
v___jp_1025_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1027_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1026_);
lean_dec_ref(v___x_1027_);
goto v___jp_1022_;
}
v___jp_1028_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
return v___x_1030_;
}
v___jp_1031_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1033_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1032_);
lean_dec_ref(v___x_1033_);
goto v___jp_1028_;
}
v___jp_1034_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
return v___x_1036_;
}
v___jp_1037_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1039_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1038_);
lean_dec_ref(v___x_1039_);
goto v___jp_1034_;
}
v___jp_1040_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
return v___x_1042_;
}
v___jp_1043_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1045_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1044_);
lean_dec_ref(v___x_1045_);
goto v___jp_1040_;
}
v___jp_1046_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_io_error_to_string(v___y_1047_);
v___x_1049_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1048_);
lean_dec_ref(v___x_1049_);
goto v___jp_1043_;
}
v___jp_1050_:
{
uint8_t v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = 1;
v___x_1052_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1051_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1060_; 
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1060_ == 0)
{
lean_object* v_unused_1061_; 
v_unused_1061_ = lean_ctor_get(v___x_1052_, 0);
lean_dec(v_unused_1061_);
v___x_1054_ = v___x_1052_;
v_isShared_1055_ = v_isSharedCheck_1060_;
goto v_resetjp_1053_;
}
else
{
lean_dec(v___x_1052_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1060_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1058_; 
v___x_1056_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_1055_ == 0)
{
lean_ctor_set_tag(v___x_1054_, 1);
lean_ctor_set(v___x_1054_, 0, v___x_1056_);
v___x_1058_ = v___x_1054_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v_a_1062_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1062_);
lean_dec_ref_known(v___x_1052_, 1);
v___x_1063_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1064_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1063_);
lean_dec_ref(v___x_1064_);
v___y_1047_ = v_a_1062_;
goto v___jp_1046_;
}
}
v___jp_1065_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__0));
v___x_1067_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1066_);
lean_dec_ref(v___x_1067_);
goto v___jp_1050_;
}
v___jp_1068_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
return v___x_1070_;
}
v___jp_1071_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1073_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1072_);
lean_dec_ref(v___x_1073_);
goto v___jp_1068_;
}
v___jp_1074_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
return v___x_1076_;
}
v___jp_1077_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1079_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1078_);
lean_dec_ref(v___x_1079_);
goto v___jp_1074_;
}
v___jp_1080_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
return v___x_1082_;
}
v___jp_1083_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1085_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1084_);
lean_dec_ref(v___x_1085_);
goto v___jp_1080_;
}
v___jp_1086_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
return v___x_1088_;
}
v___jp_1089_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1091_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1090_);
lean_dec_ref(v___x_1091_);
goto v___jp_1086_;
}
v___jp_1092_:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
return v___x_1094_;
}
v___jp_1095_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1097_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1096_);
lean_dec_ref(v___x_1097_);
goto v___jp_1092_;
}
v___jp_1098_:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
return v___x_1100_;
}
v___jp_1101_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1103_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1102_);
lean_dec_ref(v___x_1103_);
goto v___jp_1098_;
}
v___jp_1104_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = lean_io_error_to_string(v___y_1105_);
v___x_1107_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1106_);
lean_dec_ref(v___x_1107_);
goto v___jp_1095_;
}
v___jp_1108_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
return v___x_1110_;
}
v___jp_1111_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1113_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1112_);
lean_dec_ref(v___x_1113_);
goto v___jp_1108_;
}
v___jp_1114_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
return v___x_1116_;
}
v___jp_1117_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
return v___x_1119_;
}
v___jp_1120_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1122_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1121_);
lean_dec_ref(v___x_1122_);
goto v___jp_1117_;
}
v___jp_1123_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
return v___x_1125_;
}
v___jp_1126_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1128_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1127_);
lean_dec_ref(v___x_1128_);
goto v___jp_1123_;
}
v___jp_1129_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
return v___x_1131_;
}
v___jp_1132_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1134_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1133_);
lean_dec_ref(v___x_1134_);
goto v___jp_1129_;
}
v___jp_1135_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
return v___x_1137_;
}
v___jp_1138_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1140_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1139_);
lean_dec_ref(v___x_1140_);
goto v___jp_1135_;
}
v___jp_1141_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
return v___x_1143_;
}
v___jp_1144_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1146_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1145_);
lean_dec_ref(v___x_1146_);
goto v___jp_1141_;
}
v___jp_1147_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
return v___x_1149_;
}
v___jp_1150_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1152_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1151_);
lean_dec_ref(v___x_1152_);
goto v___jp_1147_;
}
v___jp_1153_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
return v___x_1155_;
}
v___jp_1156_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1158_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1157_);
lean_dec_ref(v___x_1158_);
goto v___jp_1153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed(lean_object* v_opts_2770_, lean_object* v_opt_2771_, lean_object* v_optArg_x3f_2772_, lean_object* v_a_2773_){
_start:
{
uint32_t v_opt_boxed_2774_; lean_object* v_res_2775_; 
v_opt_boxed_2774_ = lean_unbox_uint32(v_opt_2771_);
lean_dec(v_opt_2771_);
v_res_2775_ = lean_shell_options_process(v_opts_2770_, v_opt_boxed_2774_, v_optArg_x3f_2772_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically(lean_object* v_name_2777_, lean_object* v_f_2778_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = lean_uv_os_getpid();
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2816_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2783_ = v___x_2780_;
v_isShared_2784_ = v_isSharedCheck_2816_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2780_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2816_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2785_; uint64_t v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v_a_2792_; uint8_t v___x_2806_; lean_object* v___x_2807_; 
v___x_2785_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically___closed__0));
v___x_2786_ = lean_unbox_uint64(v_a_2781_);
lean_dec(v_a_2781_);
v___x_2787_ = lean_uint64_to_nat(v___x_2786_);
v___x_2788_ = l_Nat_reprFast(v___x_2787_);
v___x_2789_ = lean_string_append(v___x_2785_, v___x_2788_);
lean_dec_ref(v___x_2788_);
lean_inc_ref(v_name_2777_);
v___x_2790_ = l_System_FilePath_addExtension(v_name_2777_, v___x_2789_);
lean_dec_ref(v___x_2789_);
v___x_2806_ = 1;
v___x_2807_ = lean_io_prim_handle_mk(v___x_2790_, v___x_2806_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2809_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc_n(v_a_2808_, 2);
lean_dec_ref_known(v___x_2807_, 1);
v___x_2809_ = lean_apply_2(v_f_2778_, v_a_2808_, lean_box(0));
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v___x_2810_; 
lean_dec_ref_known(v___x_2809_, 1);
v___x_2810_ = lean_io_prim_handle_flush(v_a_2808_);
lean_dec(v_a_2808_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v___x_2811_; 
lean_dec_ref_known(v___x_2810_, 1);
v___x_2811_ = lean_io_rename(v___x_2790_, v_name_2777_);
lean_dec_ref(v_name_2777_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_dec_ref(v___x_2790_);
lean_del_object(v___x_2783_);
return v___x_2811_;
}
else
{
lean_object* v_a_2812_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2812_);
lean_dec_ref_known(v___x_2811_, 1);
v_a_2792_ = v_a_2812_;
goto v___jp_2791_;
}
}
else
{
lean_object* v_a_2813_; 
lean_dec_ref(v_name_2777_);
v_a_2813_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2813_);
lean_dec_ref_known(v___x_2810_, 1);
v_a_2792_ = v_a_2813_;
goto v___jp_2791_;
}
}
else
{
lean_object* v_a_2814_; 
lean_dec(v_a_2808_);
lean_dec_ref(v_name_2777_);
v_a_2814_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_a_2814_);
lean_dec_ref_known(v___x_2809_, 1);
v_a_2792_ = v_a_2814_;
goto v___jp_2791_;
}
}
else
{
lean_object* v_a_2815_; 
lean_dec_ref(v_f_2778_);
lean_dec_ref(v_name_2777_);
v_a_2815_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2815_);
lean_dec_ref_known(v___x_2807_, 1);
v_a_2792_ = v_a_2815_;
goto v___jp_2791_;
}
v___jp_2791_:
{
uint8_t v___x_2793_; 
v___x_2793_ = l_System_FilePath_pathExists(v___x_2790_);
if (v___x_2793_ == 0)
{
lean_object* v___x_2795_; 
lean_dec_ref(v___x_2790_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set_tag(v___x_2783_, 1);
lean_ctor_set(v___x_2783_, 0, v_a_2792_);
v___x_2795_ = v___x_2783_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2792_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
else
{
lean_object* v___x_2797_; 
lean_del_object(v___x_2783_);
v___x_2797_ = lean_io_remove_file(v___x_2790_);
lean_dec_ref(v___x_2790_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2804_; 
v_isSharedCheck_2804_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2804_ == 0)
{
lean_object* v_unused_2805_; 
v_unused_2805_ = lean_ctor_get(v___x_2797_, 0);
lean_dec(v_unused_2805_);
v___x_2799_ = v___x_2797_;
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
else
{
lean_dec(v___x_2797_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2802_; 
if (v_isShared_2800_ == 0)
{
lean_ctor_set_tag(v___x_2799_, 1);
lean_ctor_set(v___x_2799_, 0, v_a_2792_);
v___x_2802_ = v___x_2799_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_a_2792_);
v___x_2802_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
return v___x_2802_;
}
}
}
else
{
lean_dec(v_a_2792_);
return v___x_2797_;
}
}
}
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
lean_dec_ref(v_f_2778_);
lean_dec_ref(v_name_2777_);
v_a_2817_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2780_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2780_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically___boxed(lean_object* v_name_2825_, lean_object* v_f_2826_, lean_object* v_a_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically(v_name_2825_, v_f_2826_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object* v_opts_2829_, lean_object* v_opt_2830_){
_start:
{
lean_object* v_name_2831_; lean_object* v_defValue_2832_; lean_object* v_map_2833_; lean_object* v___x_2834_; 
v_name_2831_ = lean_ctor_get(v_opt_2830_, 0);
v_defValue_2832_ = lean_ctor_get(v_opt_2830_, 1);
v_map_2833_ = lean_ctor_get(v_opts_2829_, 0);
v___x_2834_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2833_, v_name_2831_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_inc(v_defValue_2832_);
return v_defValue_2832_;
}
else
{
lean_object* v_val_2835_; 
v_val_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_val_2835_);
lean_dec_ref_known(v___x_2834_, 1);
if (lean_obj_tag(v_val_2835_) == 3)
{
lean_object* v_v_2836_; 
v_v_2836_ = lean_ctor_get(v_val_2835_, 0);
lean_inc(v_v_2836_);
lean_dec_ref_known(v_val_2835_, 1);
return v_v_2836_;
}
else
{
lean_dec(v_val_2835_);
lean_inc(v_defValue_2832_);
return v_defValue_2832_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___boxed(lean_object* v_opts_2837_, lean_object* v_opt_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v_opts_2837_, v_opt_2838_);
lean_dec_ref(v_opt_2838_);
lean_dec_ref(v_opts_2837_);
return v_res_2839_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2841_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2842_ = lean_string_utf8_byte_size(v___x_2841_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(lean_object* v_s_2843_){
_start:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; uint8_t v___x_2847_; 
v___x_2844_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2845_ = lean_string_utf8_byte_size(v_s_2843_);
v___x_2846_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1);
v___x_2847_ = lean_nat_dec_le(v___x_2846_, v___x_2845_);
if (v___x_2847_ == 0)
{
lean_object* v___x_2848_; 
lean_dec_ref(v_s_2843_);
v___x_2848_ = lean_box(0);
return v___x_2848_;
}
else
{
lean_object* v___x_2849_; uint8_t v___x_2850_; 
v___x_2849_ = lean_unsigned_to_nat(0u);
v___x_2850_ = lean_string_memcmp(v_s_2843_, v___x_2844_, v___x_2849_, v___x_2849_, v___x_2846_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; 
lean_dec_ref(v_s_2843_);
v___x_2851_ = lean_box(0);
return v___x_2851_;
}
else
{
lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
lean_inc_ref(v_s_2843_);
v___x_2852_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2852_, 0, v_s_2843_);
lean_ctor_set(v___x_2852_, 1, v___x_2849_);
lean_ctor_set(v___x_2852_, 2, v___x_2845_);
v___x_2853_ = l_String_Slice_pos_x21(v___x_2852_, v___x_2846_);
lean_dec_ref_known(v___x_2852_, 3);
v___x_2854_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2854_, 0, v_s_2843_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
lean_ctor_set(v___x_2854_, 2, v___x_2845_);
v___x_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
return v___x_2855_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(lean_object* v_s_2856_, lean_object* v_pat_2857_){
_start:
{
lean_object* v___x_2858_; 
v___x_2858_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v_s_2856_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___boxed(lean_object* v_s_2859_, lean_object* v_pat_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(v_s_2859_, v_pat_2860_);
lean_dec_ref(v_pat_2860_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object* v_x_2862_, lean_object* v_x_2863_, lean_object* v_v_2864_){
_start:
{
lean_inc_ref(v_v_2864_);
return v_v_2864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object* v_x_2865_, lean_object* v_x_2866_, lean_object* v_v_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l___private_Lean_Shell_0__Lean_shellMain___lam__0(v_x_2865_, v_x_2866_, v_v_2867_);
lean_dec_ref(v_v_2867_);
lean_dec_ref(v_x_2866_);
lean_dec(v_x_2865_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1(lean_object* v___x_2872_, lean_object* v___x_2873_, lean_object* v_fileName_2874_, lean_object* v___x_2875_, lean_object* v___x_2876_, lean_object* v___x_2877_, lean_object* v___x_2878_, lean_object* v___x_2879_, lean_object* v___x_2880_, lean_object* v___x_2881_, lean_object* v___x_2882_, uint8_t v_run_2883_, lean_object* v_mainModuleName_2884_, lean_object* v_out_2885_, uint8_t v___x_2886_, lean_object* v___x_2887_){
_start:
{
lean_object* v_a_2890_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; uint8_t v___x_2898_; lean_object* v___y_2900_; lean_object* v___x_2932_; uint8_t v___y_2934_; lean_object* v_env_2954_; uint8_t v___x_2955_; 
v___x_2893_ = lean_io_get_num_heartbeats();
v___x_2894_ = lean_st_mk_ref(v___x_2872_);
v___x_2895_ = l_Lean_inheritedTraceOptions;
v___x_2896_ = lean_st_ref_get(v___x_2895_);
v___x_2897_ = l_Lean_diagnostics;
v___x_2898_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v___x_2873_, v___x_2897_);
v___x_2932_ = lean_st_ref_get(v___x_2894_);
v_env_2954_ = lean_ctor_get(v___x_2932_, 0);
lean_inc_ref(v_env_2954_);
lean_dec(v___x_2932_);
v___x_2955_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2954_);
lean_dec_ref(v_env_2954_);
if (v___x_2898_ == 0)
{
if (v___x_2955_ == 0)
{
lean_dec_ref(v___x_2887_);
lean_inc(v___x_2894_);
v___y_2900_ = v___x_2894_;
goto v___jp_2899_;
}
else
{
v___y_2934_ = v___x_2898_;
goto v___jp_2933_;
}
}
else
{
v___y_2934_ = v___x_2955_;
goto v___jp_2933_;
}
v___jp_2889_:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2891_ = lean_mk_io_user_error(v_a_2890_);
v___x_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
return v___x_2892_;
}
v___jp_2899_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2901_ = l_Lean_maxRecDepth;
v___x_2902_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_2873_, v___x_2901_);
lean_inc(v___x_2876_);
v___x_2903_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2903_, 0, v_fileName_2874_);
lean_ctor_set(v___x_2903_, 1, v___x_2875_);
lean_ctor_set(v___x_2903_, 2, v___x_2873_);
lean_ctor_set(v___x_2903_, 3, v___x_2902_);
lean_ctor_set(v___x_2903_, 4, v___x_2876_);
lean_ctor_set(v___x_2903_, 5, v___x_2877_);
lean_ctor_set(v___x_2903_, 6, v___x_2893_);
lean_ctor_set(v___x_2903_, 7, v___x_2878_);
lean_ctor_set(v___x_2903_, 8, v___x_2876_);
lean_ctor_set(v___x_2903_, 9, v___x_2879_);
lean_ctor_set(v___x_2903_, 10, v___x_2880_);
lean_ctor_set(v___x_2903_, 11, v___x_2896_);
v___x_2904_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2904_, 0, v___x_2903_);
lean_ctor_set(v___x_2904_, 1, v___x_2881_);
lean_ctor_set(v___x_2904_, 2, v___x_2882_);
lean_ctor_set_uint8(v___x_2904_, sizeof(void*)*3, v___x_2898_);
lean_ctor_set_uint8(v___x_2904_, sizeof(void*)*3 + 1, v_run_2883_);
v___x_2905_ = l_Lean_Compiler_LCNF_emitC(v_mainModuleName_2884_, v___x_2904_, v___y_2900_);
lean_dec(v___y_2900_);
lean_dec_ref_known(v___x_2904_, 3);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
lean_dec_ref_known(v___x_2905_, 1);
v___x_2907_ = lean_st_ref_get(v___x_2894_);
lean_dec(v___x_2894_);
lean_dec(v___x_2907_);
v___x_2908_ = lean_string_to_utf8(v_a_2906_);
lean_dec(v_a_2906_);
v___x_2909_ = lean_io_prim_handle_write(v_out_2885_, v___x_2908_);
lean_dec_ref(v___x_2908_);
return v___x_2909_;
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2931_; 
lean_dec(v___x_2894_);
v_a_2910_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2912_ = v___x_2905_;
v_isShared_2913_ = v_isSharedCheck_2931_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2905_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2931_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
if (lean_obj_tag(v_a_2910_) == 0)
{
lean_object* v_msg_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2918_; 
v_msg_2914_ = lean_ctor_get(v_a_2910_, 1);
lean_inc_ref(v_msg_2914_);
lean_dec_ref_known(v_a_2910_, 2);
v___x_2915_ = l_Lean_MessageData_toString(v_msg_2914_);
v___x_2916_ = lean_mk_io_user_error(v___x_2915_);
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 0, v___x_2916_);
v___x_2918_ = v___x_2912_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2916_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
else
{
lean_object* v_id_2920_; lean_object* v___x_2921_; 
lean_del_object(v___x_2912_);
v_id_2920_ = lean_ctor_get(v_a_2910_, 0);
lean_inc(v_id_2920_);
lean_dec_ref_known(v_a_2910_, 2);
v___x_2921_ = l_Lean_InternalExceptionId_getName(v_id_2920_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v_a_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
lean_dec(v_id_2920_);
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
lean_inc(v_a_2922_);
lean_dec_ref_known(v___x_2921_, 1);
v___x_2923_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__0));
v___x_2924_ = l_Lean_Name_toString(v_a_2922_, v___x_2886_);
v___x_2925_ = lean_string_append(v___x_2923_, v___x_2924_);
lean_dec_ref(v___x_2924_);
v_a_2890_ = v___x_2925_;
goto v___jp_2889_;
}
else
{
lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
lean_dec_ref_known(v___x_2921_, 1);
v___x_2926_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__1));
v___x_2927_ = l_Nat_reprFast(v_id_2920_);
v___x_2928_ = lean_string_append(v___x_2926_, v___x_2927_);
lean_dec_ref(v___x_2927_);
v___x_2929_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__2));
v___x_2930_ = lean_string_append(v___x_2928_, v___x_2929_);
v_a_2890_ = v___x_2930_;
goto v___jp_2889_;
}
}
}
}
}
v___jp_2933_:
{
if (v___y_2934_ == 0)
{
lean_object* v___x_2935_; lean_object* v_env_2936_; lean_object* v_nextMacroScope_2937_; lean_object* v_ngen_2938_; lean_object* v_auxDeclNGen_2939_; lean_object* v_traceState_2940_; lean_object* v_messages_2941_; lean_object* v_infoState_2942_; lean_object* v_snapshotTasks_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2952_; 
v___x_2935_ = lean_st_ref_take(v___x_2894_);
v_env_2936_ = lean_ctor_get(v___x_2935_, 0);
v_nextMacroScope_2937_ = lean_ctor_get(v___x_2935_, 1);
v_ngen_2938_ = lean_ctor_get(v___x_2935_, 2);
v_auxDeclNGen_2939_ = lean_ctor_get(v___x_2935_, 3);
v_traceState_2940_ = lean_ctor_get(v___x_2935_, 4);
v_messages_2941_ = lean_ctor_get(v___x_2935_, 6);
v_infoState_2942_ = lean_ctor_get(v___x_2935_, 7);
v_snapshotTasks_2943_ = lean_ctor_get(v___x_2935_, 8);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2952_ == 0)
{
lean_object* v_unused_2953_; 
v_unused_2953_ = lean_ctor_get(v___x_2935_, 5);
lean_dec(v_unused_2953_);
v___x_2945_ = v___x_2935_;
v_isShared_2946_ = v_isSharedCheck_2952_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_snapshotTasks_2943_);
lean_inc(v_infoState_2942_);
lean_inc(v_messages_2941_);
lean_inc(v_traceState_2940_);
lean_inc(v_auxDeclNGen_2939_);
lean_inc(v_ngen_2938_);
lean_inc(v_nextMacroScope_2937_);
lean_inc(v_env_2936_);
lean_dec(v___x_2935_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2952_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2947_; lean_object* v___x_2949_; 
v___x_2947_ = l_Lean_Kernel_enableDiag(v_env_2936_, v___x_2898_);
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 5, v___x_2887_);
lean_ctor_set(v___x_2945_, 0, v___x_2947_);
v___x_2949_ = v___x_2945_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2947_);
lean_ctor_set(v_reuseFailAlloc_2951_, 1, v_nextMacroScope_2937_);
lean_ctor_set(v_reuseFailAlloc_2951_, 2, v_ngen_2938_);
lean_ctor_set(v_reuseFailAlloc_2951_, 3, v_auxDeclNGen_2939_);
lean_ctor_set(v_reuseFailAlloc_2951_, 4, v_traceState_2940_);
lean_ctor_set(v_reuseFailAlloc_2951_, 5, v___x_2887_);
lean_ctor_set(v_reuseFailAlloc_2951_, 6, v_messages_2941_);
lean_ctor_set(v_reuseFailAlloc_2951_, 7, v_infoState_2942_);
lean_ctor_set(v_reuseFailAlloc_2951_, 8, v_snapshotTasks_2943_);
v___x_2949_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
lean_object* v___x_2950_; 
v___x_2950_ = lean_st_ref_put(v___x_2894_, v___x_2949_);
lean_inc(v___x_2894_);
v___y_2900_ = v___x_2894_;
goto v___jp_2899_;
}
}
}
else
{
lean_dec_ref(v___x_2887_);
lean_inc(v___x_2894_);
v___y_2900_ = v___x_2894_;
goto v___jp_2899_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed(lean_object** _args){
lean_object* v___x_2956_ = _args[0];
lean_object* v___x_2957_ = _args[1];
lean_object* v_fileName_2958_ = _args[2];
lean_object* v___x_2959_ = _args[3];
lean_object* v___x_2960_ = _args[4];
lean_object* v___x_2961_ = _args[5];
lean_object* v___x_2962_ = _args[6];
lean_object* v___x_2963_ = _args[7];
lean_object* v___x_2964_ = _args[8];
lean_object* v___x_2965_ = _args[9];
lean_object* v___x_2966_ = _args[10];
lean_object* v_run_2967_ = _args[11];
lean_object* v_mainModuleName_2968_ = _args[12];
lean_object* v_out_2969_ = _args[13];
lean_object* v___x_2970_ = _args[14];
lean_object* v___x_2971_ = _args[15];
lean_object* v___y_2972_ = _args[16];
_start:
{
uint8_t v_run_boxed_2973_; uint8_t v___x_12449__boxed_2974_; lean_object* v_res_2975_; 
v_run_boxed_2973_ = lean_unbox(v_run_2967_);
v___x_12449__boxed_2974_ = lean_unbox(v___x_2970_);
v_res_2975_ = l___private_Lean_Shell_0__Lean_shellMain___lam__1(v___x_2956_, v___x_2957_, v_fileName_2958_, v___x_2959_, v___x_2960_, v___x_2961_, v___x_2962_, v___x_2963_, v___x_2964_, v___x_2965_, v___x_2966_, v_run_boxed_2973_, v_mainModuleName_2968_, v_out_2969_, v___x_12449__boxed_2974_, v___x_2971_);
lean_dec(v_out_2969_);
return v_res_2975_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2977_ = l_Lean_Options_empty;
v___x_2978_ = l_Lean_Core_getMaxHeartbeats(v___x_2977_);
return v___x_2978_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2979_ = lean_unsigned_to_nat(1u);
v___x_2980_ = l_Lean_firstFrontendMacroScope;
v___x_2981_ = lean_nat_add(v___x_2980_, v___x_2979_);
return v___x_2981_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__7(void){
_start:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2992_ = lean_unsigned_to_nat(32u);
v___x_2993_ = lean_mk_empty_array_with_capacity(v___x_2992_);
v___x_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2993_);
return v___x_2994_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__8(void){
_start:
{
lean_object* v___x_2995_; 
v___x_2995_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2995_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9(void){
_start:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2996_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__8, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__8_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__8);
v___x_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
return v___x_2997_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__10(void){
_start:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2998_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9);
v___x_2999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2998_);
lean_ctor_set(v___x_2999_, 1, v___x_2998_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2(lean_object* v___x_3000_, uint8_t v___x_3001_, lean_object* v_val_3002_, lean_object* v_fileName_3003_, uint8_t v_run_3004_, lean_object* v_mainModuleName_3005_, lean_object* v___x_3006_, lean_object* v_out_3007_){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; uint64_t v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; size_t v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___f_3037_; lean_object* v___x_3038_; 
v___x_3009_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__0));
v___x_3010_ = l_Lean_instInhabitedFileMap_default;
v___x_3011_ = l_Lean_Options_empty;
v___x_3012_ = lean_box(0);
v___x_3013_ = lean_box(0);
v___x_3014_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__1, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__1_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__1);
v___x_3015_ = l_Lean_firstFrontendMacroScope;
v___x_3016_ = lean_box(0);
v___x_3017_ = lean_box(0);
v___x_3018_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__2, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__2_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__2);
v___x_3019_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__5));
v___x_3020_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__6));
v___x_3021_ = 0ULL;
v___x_3022_ = lean_unsigned_to_nat(32u);
v___x_3023_ = lean_mk_empty_array_with_capacity(v___x_3022_);
v___x_3024_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__7, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__7_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__7);
v___x_3025_ = ((size_t)5ULL);
lean_inc_n(v___x_3000_, 2);
v___x_3026_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3026_, 0, v___x_3024_);
lean_ctor_set(v___x_3026_, 1, v___x_3023_);
lean_ctor_set(v___x_3026_, 2, v___x_3000_);
lean_ctor_set(v___x_3026_, 3, v___x_3000_);
lean_ctor_set_usize(v___x_3026_, 4, v___x_3025_);
lean_inc_ref_n(v___x_3026_, 3);
v___x_3027_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3027_, 0, v___x_3026_);
lean_ctor_set_uint64(v___x_3027_, sizeof(void*)*1, v___x_3021_);
v___x_3028_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9);
v___x_3029_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__10, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__10_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__10);
v___x_3030_ = l_Lean_NameSet_empty;
v___x_3031_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3026_);
lean_ctor_set(v___x_3031_, 1, v___x_3026_);
lean_ctor_set(v___x_3031_, 2, v___x_3030_);
v___x_3032_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3032_, 0, v___x_3028_);
lean_ctor_set(v___x_3032_, 1, v___x_3028_);
lean_ctor_set(v___x_3032_, 2, v___x_3026_);
lean_ctor_set_uint8(v___x_3032_, sizeof(void*)*3, v___x_3001_);
v___x_3033_ = lean_mk_empty_array_with_capacity(v___x_3000_);
v___x_3034_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3034_, 0, v_val_3002_);
lean_ctor_set(v___x_3034_, 1, v___x_3018_);
lean_ctor_set(v___x_3034_, 2, v___x_3019_);
lean_ctor_set(v___x_3034_, 3, v___x_3020_);
lean_ctor_set(v___x_3034_, 4, v___x_3027_);
lean_ctor_set(v___x_3034_, 5, v___x_3029_);
lean_ctor_set(v___x_3034_, 6, v___x_3031_);
lean_ctor_set(v___x_3034_, 7, v___x_3032_);
lean_ctor_set(v___x_3034_, 8, v___x_3033_);
v___x_3035_ = lean_box(v_run_3004_);
v___x_3036_ = lean_box(v___x_3001_);
v___f_3037_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed), 17, 16);
lean_closure_set(v___f_3037_, 0, v___x_3034_);
lean_closure_set(v___f_3037_, 1, v___x_3011_);
lean_closure_set(v___f_3037_, 2, v_fileName_3003_);
lean_closure_set(v___f_3037_, 3, v___x_3010_);
lean_closure_set(v___f_3037_, 4, v___x_3012_);
lean_closure_set(v___f_3037_, 5, v___x_3013_);
lean_closure_set(v___f_3037_, 6, v___x_3014_);
lean_closure_set(v___f_3037_, 7, v___x_3015_);
lean_closure_set(v___f_3037_, 8, v___x_3016_);
lean_closure_set(v___f_3037_, 9, v___x_3000_);
lean_closure_set(v___f_3037_, 10, v___x_3017_);
lean_closure_set(v___f_3037_, 11, v___x_3035_);
lean_closure_set(v___f_3037_, 12, v_mainModuleName_3005_);
lean_closure_set(v___f_3037_, 13, v_out_3007_);
lean_closure_set(v___f_3037_, 14, v___x_3036_);
lean_closure_set(v___f_3037_, 15, v___x_3029_);
v___x_3038_ = l_Lean_profileitIOUnsafe___redArg(v___x_3009_, v___x_3006_, v___f_3037_, v___x_3012_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2___boxed(lean_object* v___x_3039_, lean_object* v___x_3040_, lean_object* v_val_3041_, lean_object* v_fileName_3042_, lean_object* v_run_3043_, lean_object* v_mainModuleName_3044_, lean_object* v___x_3045_, lean_object* v_out_3046_, lean_object* v___y_3047_){
_start:
{
uint8_t v___x_12651__boxed_3048_; uint8_t v_run_boxed_3049_; lean_object* v_res_3050_; 
v___x_12651__boxed_3048_ = lean_unbox(v___x_3040_);
v_run_boxed_3049_ = lean_unbox(v_run_3043_);
v_res_3050_ = l___private_Lean_Shell_0__Lean_shellMain___lam__2(v___x_3039_, v___x_12651__boxed_3048_, v_val_3041_, v_fileName_3042_, v_run_boxed_3049_, v_mainModuleName_3044_, v___x_3045_, v_out_3046_);
lean_dec_ref(v___x_3045_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(lean_object* v_val_3051_, lean_object* v_a_3052_, lean_object* v_b_3053_){
_start:
{
lean_object* v_str_3054_; lean_object* v_startInclusive_3055_; lean_object* v_endExclusive_3056_; lean_object* v___x_3057_; uint8_t v_decide_3058_; 
v_str_3054_ = lean_ctor_get(v_val_3051_, 0);
v_startInclusive_3055_ = lean_ctor_get(v_val_3051_, 1);
v_endExclusive_3056_ = lean_ctor_get(v_val_3051_, 2);
v___x_3057_ = lean_nat_sub(v_endExclusive_3056_, v_startInclusive_3055_);
v_decide_3058_ = lean_nat_dec_eq(v_a_3052_, v___x_3057_);
lean_dec(v___x_3057_);
if (v_decide_3058_ == 0)
{
lean_object* v___x_3059_; uint32_t v___x_3060_; uint32_t v___x_3061_; uint8_t v___x_3062_; 
v___x_3059_ = lean_nat_add(v_startInclusive_3055_, v_a_3052_);
v___x_3060_ = lean_string_utf8_get_fast(v_str_3054_, v___x_3059_);
v___x_3061_ = 10;
v___x_3062_ = lean_uint32_dec_eq(v___x_3060_, v___x_3061_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
lean_dec(v_a_3052_);
v___x_3063_ = lean_box(0);
v___x_3064_ = lean_string_utf8_next_fast(v_str_3054_, v___x_3059_);
lean_dec(v___x_3059_);
v___x_3065_ = lean_nat_sub(v___x_3064_, v_startInclusive_3055_);
v_a_3052_ = v___x_3065_;
v_b_3053_ = v___x_3063_;
goto _start;
}
else
{
lean_object* v___x_3067_; 
lean_dec(v___x_3059_);
v___x_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3067_, 0, v_a_3052_);
return v___x_3067_;
}
}
else
{
lean_dec(v_a_3052_);
lean_inc(v_b_3053_);
return v_b_3053_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg___boxed(lean_object* v_val_3068_, lean_object* v_a_3069_, lean_object* v_b_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3068_, v_a_3069_, v_b_3070_);
lean_dec(v_b_3070_);
lean_dec_ref(v_val_3068_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(lean_object* v_s_3072_){
_start:
{
uint32_t v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = 10;
v___x_3075_ = lean_string_push(v_s_3072_, v___x_3074_);
v___x_3076_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_3075_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___boxed(lean_object* v_s_3077_, lean_object* v_a_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_s_3077_);
return v_res_3079_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(lean_object* v_s_3080_){
_start:
{
uint32_t v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3082_ = 10;
v___x_3083_ = lean_string_push(v_s_3080_, v___x_3082_);
v___x_3084_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_3083_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4___boxed(lean_object* v_s_3085_, lean_object* v_a_3086_){
_start:
{
lean_object* v_res_3087_; 
v_res_3087_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_s_3085_);
return v_res_3087_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shellMain___closed__1(void){
_start:
{
lean_object* v___x_3089_; uint8_t v___x_3090_; 
v___x_3089_ = lean_box(0);
v___x_3090_ = lean_internal_has_address_sanitizer(v___x_3089_);
return v___x_3090_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__2(void){
_start:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3091_ = lean_box(0);
v___x_3092_ = lean_internal_get_option_overrides(v___x_3091_);
return v___x_3092_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__9(void){
_start:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3101_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__8));
v___x_3102_ = lean_string_utf8_byte_size(v___x_3101_);
return v___x_3102_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10(void){
_start:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3103_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__9, &l___private_Lean_Shell_0__Lean_shellMain___closed__9_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__9);
v___x_3104_ = lean_unsigned_to_nat(0u);
v___x_3105_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__8));
v___x_3106_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
lean_ctor_set(v___x_3106_, 1, v___x_3104_);
lean_ctor_set(v___x_3106_, 2, v___x_3103_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* lean_shell_main(lean_object* v_args_3109_, lean_object* v_opts_3110_){
_start:
{
lean_object* v_fns_3113_; uint8_t v_printPrefix_3138_; 
v_printPrefix_3138_ = lean_ctor_get_uint8(v_opts_3110_, sizeof(void*)*13 + 9);
if (v_printPrefix_3138_ == 0)
{
uint8_t v_printLibDir_3139_; 
v_printLibDir_3139_ = lean_ctor_get_uint8(v_opts_3110_, sizeof(void*)*13 + 10);
if (v_printLibDir_3139_ == 0)
{
lean_object* v_leanOpts_3140_; lean_object* v_forwardedArgs_3141_; uint8_t v_component_3142_; uint8_t v_useStdin_3143_; uint8_t v_onlyDeps_3144_; uint8_t v_onlySrcDeps_3145_; uint8_t v_depsJson_3146_; uint32_t v_trustLevel_3147_; lean_object* v_rootDir_x3f_3148_; lean_object* v_setupFileName_x3f_3149_; lean_object* v_oleanFileName_x3f_3150_; lean_object* v_ileanFileName_x3f_3151_; lean_object* v_cFileName_x3f_3152_; lean_object* v_bcFileName_x3f_3153_; uint8_t v_jsonOutput_3154_; lean_object* v_errorOnKinds_3155_; uint8_t v_printStats_3156_; uint8_t v_run_3157_; lean_object* v_incrSaveFileName_x3f_3158_; lean_object* v_incrLoadFileName_x3f_3159_; lean_object* v_incrHeaderSaveFileName_x3f_3160_; lean_object* v___f_3161_; lean_object* v___y_3163_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; uint8_t v___x_3205_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v_mainModuleName_3241_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v_contents_3300_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v_str_3329_; lean_object* v_startInclusive_3330_; lean_object* v_endExclusive_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v_fileName_3432_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3470_; lean_object* v___y_3471_; uint8_t v___y_3472_; uint8_t v___y_3475_; lean_object* v_fst_3476_; lean_object* v_snd_3477_; uint8_t v___y_3479_; lean_object* v___x_3509_; lean_object* v_maxMemory_3510_; lean_object* v___x_3511_; uint8_t v___x_3512_; 
v_leanOpts_3140_ = lean_ctor_get(v_opts_3110_, 0);
lean_inc_ref(v_leanOpts_3140_);
v_forwardedArgs_3141_ = lean_ctor_get(v_opts_3110_, 1);
lean_inc_ref(v_forwardedArgs_3141_);
v_component_3142_ = lean_ctor_get_uint8(v_opts_3110_, sizeof(void*)*13 + 8);
v_useStdin_3143_ = lean_ctor_get_uint8(v_opts_3110_, sizeof(void*)*13 + 11);
v_onlyDeps_3144_ = lean_ctor_get_uint8(v_opts_3110_, sizeof(void*)*13 + 12);
v_onlySrcDeps_3145_ = lean_ctor_get_uint8(v_opts_3110_, sizeof(void*)*13 + 13);
v_depsJson_3146_ = lean_ctor_get_uint8(v_opts_3110_, sizeof(void*)*13 + 14);
v_trustLevel_3147_ = lean_ctor_get_uint32(v_opts_3110_, sizeof(void*)*13);
v_rootDir_x3f_3148_ = lean_ctor_get(v_opts_3110_, 3);
lean_inc(v_rootDir_x3f_3148_);
v_setupFileName_x3f_3149_ = lean_ctor_get(v_opts_3110_, 4);
lean_inc(v_setupFileName_x3f_3149_);
v_oleanFileName_x3f_3150_ = lean_ctor_get(v_opts_3110_, 5);
lean_inc(v_oleanFileName_x3f_3150_);
v_ileanFileName_x3f_3151_ = lean_ctor_get(v_opts_3110_, 6);
lean_inc(v_ileanFileName_x3f_3151_);
v_cFileName_x3f_3152_ = lean_ctor_get(v_opts_3110_, 7);
lean_inc(v_cFileName_x3f_3152_);
v_bcFileName_x3f_3153_ = lean_ctor_get(v_opts_3110_, 8);
lean_inc(v_bcFileName_x3f_3153_);
v_jsonOutput_3154_ = lean_ctor_get_uint8(v_opts_3110_, sizeof(void*)*13 + 15);
v_errorOnKinds_3155_ = lean_ctor_get(v_opts_3110_, 9);
lean_inc_ref(v_errorOnKinds_3155_);
v_printStats_3156_ = lean_ctor_get_uint8(v_opts_3110_, sizeof(void*)*13 + 16);
v_run_3157_ = lean_ctor_get_uint8(v_opts_3110_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_3158_ = lean_ctor_get(v_opts_3110_, 10);
lean_inc(v_incrSaveFileName_x3f_3158_);
v_incrLoadFileName_x3f_3159_ = lean_ctor_get(v_opts_3110_, 11);
lean_inc(v_incrLoadFileName_x3f_3159_);
v_incrHeaderSaveFileName_x3f_3160_ = lean_ctor_get(v_opts_3110_, 12);
lean_inc(v_incrHeaderSaveFileName_x3f_3160_);
lean_dec_ref(v_opts_3110_);
v___f_3161_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__0));
v___x_3177_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__2, &l___private_Lean_Shell_0__Lean_shellMain___closed__2_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__2);
v___x_3178_ = l_Lean_Options_mergeBy(v___f_3161_, v_leanOpts_3140_, v___x_3177_);
v___x_3205_ = 1;
v___x_3509_ = l___private_Lean_Shell_0__Lean_maxMemory;
v_maxMemory_3510_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3178_, v___x_3509_);
v___x_3511_ = lean_unsigned_to_nat(0u);
v___x_3512_ = lean_nat_dec_eq(v_maxMemory_3510_, v___x_3511_);
if (v___x_3512_ == 0)
{
size_t v___x_3513_; size_t v___x_3514_; size_t v___x_3515_; size_t v___x_3516_; lean_object* v___x_3517_; 
v___x_3513_ = lean_usize_of_nat(v_maxMemory_3510_);
lean_dec(v_maxMemory_3510_);
v___x_3514_ = ((size_t)10ULL);
v___x_3515_ = lean_usize_shift_left(v___x_3513_, v___x_3514_);
v___x_3516_ = lean_usize_shift_left(v___x_3515_, v___x_3514_);
v___x_3517_ = lean_internal_set_max_memory(v___x_3516_);
goto v___jp_3500_;
}
else
{
lean_dec(v_maxMemory_3510_);
goto v___jp_3500_;
}
v___jp_3162_:
{
lean_object* v___x_3164_; uint8_t v___x_3165_; 
v___x_3164_ = lean_display_cumulative_profiling_times();
v___x_3165_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__1, &l___private_Lean_Shell_0__Lean_shellMain___closed__1_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__1);
if (v___x_3165_ == 0)
{
if (lean_obj_tag(v___y_3163_) == 0)
{
if (v___x_3165_ == 0)
{
uint8_t v___x_3166_; lean_object* v___x_3167_; 
v___x_3166_ = 1;
v___x_3167_ = lean_io_exit(v___x_3166_);
return v___x_3167_;
}
else
{
goto v___jp_3132_;
}
}
else
{
lean_dec_ref_known(v___y_3163_, 1);
goto v___jp_3132_;
}
}
else
{
if (lean_obj_tag(v___y_3163_) == 0)
{
goto v___jp_3135_;
}
else
{
lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3175_; 
v_isSharedCheck_3175_ = !lean_is_exclusive(v___y_3163_);
if (v_isSharedCheck_3175_ == 0)
{
lean_object* v_unused_3176_; 
v_unused_3176_ = lean_ctor_get(v___y_3163_, 0);
lean_dec(v_unused_3176_);
v___x_3169_ = v___y_3163_;
v_isShared_3170_ = v_isSharedCheck_3175_;
goto v_resetjp_3168_;
}
else
{
lean_dec(v___y_3163_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3175_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
if (v___x_3165_ == 0)
{
lean_del_object(v___x_3169_);
goto v___jp_3135_;
}
else
{
lean_object* v___x_3171_; lean_object* v___x_3173_; 
v___x_3171_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3170_ == 0)
{
lean_ctor_set_tag(v___x_3169_, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3171_);
v___x_3173_ = v___x_3169_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_3171_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
}
}
v___jp_3179_:
{
if (lean_obj_tag(v_bcFileName_x3f_3153_) == 1)
{
lean_object* v_val_3183_; lean_object* v___x_3184_; 
v_val_3183_ = lean_ctor_get(v_bcFileName_x3f_3153_, 0);
lean_inc(v_val_3183_);
lean_dec_ref_known(v_bcFileName_x3f_3153_, 1);
v___x_3184_ = lean_init_llvm();
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
lean_dec_ref_known(v___x_3184_, 1);
v___x_3185_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__3));
v___x_3186_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_emitLLVM___boxed), 4, 3);
lean_closure_set(v___x_3186_, 0, v___y_3182_);
lean_closure_set(v___x_3186_, 1, v___y_3181_);
lean_closure_set(v___x_3186_, 2, v_val_3183_);
v___x_3187_ = lean_box(0);
v___x_3188_ = l_Lean_profileitIOUnsafe___redArg(v___x_3185_, v___x_3178_, v___x_3186_, v___x_3187_);
lean_dec_ref(v___x_3178_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_dec_ref_known(v___x_3188_, 1);
v___y_3163_ = v___y_3180_;
goto v___jp_3162_;
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_dec(v___y_3180_);
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3188_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3188_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
else
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
lean_dec(v_val_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___x_3178_);
v_a_3197_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3184_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3184_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3197_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
else
{
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___x_3178_);
lean_dec(v_bcFileName_x3f_3153_);
v___y_3163_ = v___y_3180_;
goto v___jp_3162_;
}
}
v___jp_3206_:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3207_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__4));
v___x_3208_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_3207_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v___x_3209_; 
lean_dec_ref_known(v___x_3208_, 1);
v___x_3209_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_3205_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3217_; 
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3217_ == 0)
{
lean_object* v_unused_3218_; 
v_unused_3218_ = lean_ctor_get(v___x_3209_, 0);
lean_dec(v_unused_3218_);
v___x_3211_ = v___x_3209_;
v_isShared_3212_ = v_isSharedCheck_3217_;
goto v_resetjp_3210_;
}
else
{
lean_dec(v___x_3209_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3217_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3213_; lean_object* v___x_3215_; 
v___x_3213_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 0, v___x_3213_);
v___x_3215_ = v___x_3211_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3213_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
v_a_3219_ = lean_ctor_get(v___x_3209_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3209_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3209_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
v_a_3227_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3229_ = v___x_3208_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3208_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3227_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
v___jp_3235_:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3242_ = lean_unsigned_to_nat(0u);
v___x_3243_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__5));
lean_inc(v_mainModuleName_3241_);
lean_inc_ref(v___x_3178_);
v___x_3244_ = l_Lean_Elab_runFrontend(v___y_3240_, v___x_3178_, v___y_3238_, v_mainModuleName_3241_, v_trustLevel_3147_, v_oleanFileName_x3f_3150_, v_ileanFileName_x3f_3151_, v_jsonOutput_3154_, v_errorOnKinds_3155_, v___x_3243_, v_printStats_3156_, v___y_3239_, v_incrSaveFileName_x3f_3158_, v_incrLoadFileName_x3f_3159_, v_incrHeaderSaveFileName_x3f_3160_);
lean_dec_ref(v_errorOnKinds_3155_);
lean_dec(v_ileanFileName_x3f_3151_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3270_; 
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3247_ = v___x_3244_;
v_isShared_3248_ = v_isSharedCheck_3270_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3244_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3270_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
if (lean_obj_tag(v_a_3245_) == 1)
{
if (v_run_3157_ == 0)
{
lean_del_object(v___x_3247_);
lean_dec(v___y_3237_);
if (lean_obj_tag(v_cFileName_x3f_3152_) == 1)
{
lean_object* v_val_3249_; lean_object* v_val_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___f_3253_; lean_object* v___x_3254_; 
v_val_3249_ = lean_ctor_get(v_a_3245_, 0);
lean_inc_n(v_val_3249_, 2);
v_val_3250_ = lean_ctor_get(v_cFileName_x3f_3152_, 0);
lean_inc(v_val_3250_);
lean_dec_ref_known(v_cFileName_x3f_3152_, 1);
v___x_3251_ = lean_box(v___x_3205_);
v___x_3252_ = lean_box(v_run_3157_);
lean_inc_ref(v___x_3178_);
lean_inc(v_mainModuleName_3241_);
v___f_3253_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__2___boxed), 9, 7);
lean_closure_set(v___f_3253_, 0, v___x_3242_);
lean_closure_set(v___f_3253_, 1, v___x_3251_);
lean_closure_set(v___f_3253_, 2, v_val_3249_);
lean_closure_set(v___f_3253_, 3, v___y_3236_);
lean_closure_set(v___f_3253_, 4, v___x_3252_);
lean_closure_set(v___f_3253_, 5, v_mainModuleName_3241_);
lean_closure_set(v___f_3253_, 6, v___x_3178_);
v___x_3254_ = l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically(v_val_3250_, v___f_3253_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_dec_ref_known(v___x_3254_, 1);
v___y_3180_ = v_a_3245_;
v___y_3181_ = v_mainModuleName_3241_;
v___y_3182_ = v_val_3249_;
goto v___jp_3179_;
}
else
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_dec(v_val_3249_);
lean_dec_ref_known(v_a_3245_, 1);
lean_dec(v_mainModuleName_3241_);
lean_dec_ref(v___x_3178_);
lean_dec(v_bcFileName_x3f_3153_);
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3257_ = v___x_3254_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3254_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
else
{
lean_object* v_val_3263_; 
lean_dec_ref(v___y_3236_);
lean_dec(v_cFileName_x3f_3152_);
v_val_3263_ = lean_ctor_get(v_a_3245_, 0);
lean_inc(v_val_3263_);
v___y_3180_ = v_a_3245_;
v___y_3181_ = v_mainModuleName_3241_;
v___y_3182_ = v_val_3263_;
goto v___jp_3179_;
}
}
else
{
lean_object* v_val_3264_; uint32_t v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3268_; 
lean_dec(v_mainModuleName_3241_);
lean_dec_ref(v___y_3236_);
lean_dec(v_bcFileName_x3f_3153_);
lean_dec(v_cFileName_x3f_3152_);
v_val_3264_ = lean_ctor_get(v_a_3245_, 0);
lean_inc(v_val_3264_);
lean_dec_ref_known(v_a_3245_, 1);
v___x_3265_ = lean_eval_main(v_val_3264_, v___x_3178_, v___y_3237_);
lean_dec(v___y_3237_);
lean_dec_ref(v___x_3178_);
lean_dec(v_val_3264_);
v___x_3266_ = lean_box_uint32(v___x_3265_);
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 0, v___x_3266_);
v___x_3268_ = v___x_3247_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v___x_3266_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
else
{
lean_del_object(v___x_3247_);
lean_dec(v_mainModuleName_3241_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec_ref(v___x_3178_);
lean_dec(v_bcFileName_x3f_3153_);
lean_dec(v_cFileName_x3f_3152_);
v___y_3163_ = v_a_3245_;
goto v___jp_3162_;
}
}
}
else
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
lean_dec(v_mainModuleName_3241_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec_ref(v___x_3178_);
lean_dec(v_bcFileName_x3f_3153_);
lean_dec(v_cFileName_x3f_3152_);
v_a_3271_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3273_ = v___x_3244_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3244_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3271_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
v___jp_3279_:
{
if (lean_obj_tag(v___y_3285_) == 0)
{
lean_object* v_a_3286_; 
v_a_3286_ = lean_ctor_get(v___y_3285_, 0);
lean_inc(v_a_3286_);
lean_dec_ref_known(v___y_3285_, 1);
v___y_3236_ = v___y_3280_;
v___y_3237_ = v___y_3281_;
v___y_3238_ = v___y_3282_;
v___y_3239_ = v___y_3283_;
v___y_3240_ = v___y_3284_;
v_mainModuleName_3241_ = v_a_3286_;
goto v___jp_3235_;
}
else
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3294_; 
lean_dec_ref(v___y_3284_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec_ref(v___x_3178_);
lean_dec(v_incrHeaderSaveFileName_x3f_3160_);
lean_dec(v_incrLoadFileName_x3f_3159_);
lean_dec(v_incrSaveFileName_x3f_3158_);
lean_dec_ref(v_errorOnKinds_3155_);
lean_dec(v_bcFileName_x3f_3153_);
lean_dec(v_cFileName_x3f_3152_);
lean_dec(v_ileanFileName_x3f_3151_);
lean_dec(v_oleanFileName_x3f_3150_);
v_a_3287_ = lean_ctor_get(v___y_3285_, 0);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___y_3285_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3289_ = v___y_3285_;
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___y_3285_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3292_; 
if (v_isShared_3290_ == 0)
{
v___x_3292_ = v___x_3289_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_a_3287_);
v___x_3292_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
return v___x_3292_;
}
}
}
}
v___jp_3295_:
{
if (lean_obj_tag(v_setupFileName_x3f_3149_) == 0)
{
lean_object* v___x_3301_; 
v___x_3301_ = lean_box(0);
if (lean_obj_tag(v___y_3298_) == 1)
{
lean_object* v_val_3302_; lean_object* v___x_3303_; 
v_val_3302_ = lean_ctor_get(v___y_3298_, 0);
lean_inc(v_val_3302_);
lean_dec_ref_known(v___y_3298_, 1);
v___x_3303_ = l_Lean_moduleNameOfFileName(v_val_3302_, v_rootDir_x3f_3148_);
if (lean_obj_tag(v___x_3303_) == 0)
{
v___y_3280_ = v___y_3296_;
v___y_3281_ = v___y_3297_;
v___y_3282_ = v___y_3299_;
v___y_3283_ = v___x_3301_;
v___y_3284_ = v_contents_3300_;
v___y_3285_ = v___x_3303_;
goto v___jp_3279_;
}
else
{
if (lean_obj_tag(v_oleanFileName_x3f_3150_) == 0)
{
if (lean_obj_tag(v_cFileName_x3f_3152_) == 0)
{
lean_object* v___x_3304_; 
lean_dec_ref_known(v___x_3303_, 1);
v___x_3304_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__7));
v___y_3236_ = v___y_3296_;
v___y_3237_ = v___y_3297_;
v___y_3238_ = v___y_3299_;
v___y_3239_ = v___x_3301_;
v___y_3240_ = v_contents_3300_;
v_mainModuleName_3241_ = v___x_3304_;
goto v___jp_3235_;
}
else
{
v___y_3280_ = v___y_3296_;
v___y_3281_ = v___y_3297_;
v___y_3282_ = v___y_3299_;
v___y_3283_ = v___x_3301_;
v___y_3284_ = v_contents_3300_;
v___y_3285_ = v___x_3303_;
goto v___jp_3279_;
}
}
else
{
v___y_3280_ = v___y_3296_;
v___y_3281_ = v___y_3297_;
v___y_3282_ = v___y_3299_;
v___y_3283_ = v___x_3301_;
v___y_3284_ = v_contents_3300_;
v___y_3285_ = v___x_3303_;
goto v___jp_3279_;
}
}
}
else
{
lean_object* v___x_3305_; 
lean_dec(v___y_3298_);
lean_dec(v_rootDir_x3f_3148_);
v___x_3305_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__7));
v___y_3236_ = v___y_3296_;
v___y_3237_ = v___y_3297_;
v___y_3238_ = v___y_3299_;
v___y_3239_ = v___x_3301_;
v___y_3240_ = v_contents_3300_;
v_mainModuleName_3241_ = v___x_3305_;
goto v___jp_3235_;
}
}
else
{
lean_object* v_val_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3324_; 
lean_dec(v___y_3298_);
lean_dec(v_rootDir_x3f_3148_);
v_val_3306_ = lean_ctor_get(v_setupFileName_x3f_3149_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v_setupFileName_x3f_3149_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3308_ = v_setupFileName_x3f_3149_;
v_isShared_3309_ = v_isSharedCheck_3324_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_val_3306_);
lean_dec(v_setupFileName_x3f_3149_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3324_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3310_; 
v___x_3310_ = l_Lean_ModuleSetup_load(v_val_3306_);
lean_dec(v_val_3306_);
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_object* v_a_3311_; lean_object* v_name_3312_; lean_object* v___x_3314_; 
v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
lean_inc(v_a_3311_);
lean_dec_ref_known(v___x_3310_, 1);
v_name_3312_ = lean_ctor_get(v_a_3311_, 0);
lean_inc(v_name_3312_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 0, v_a_3311_);
v___x_3314_ = v___x_3308_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3311_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
v___y_3236_ = v___y_3296_;
v___y_3237_ = v___y_3297_;
v___y_3238_ = v___y_3299_;
v___y_3239_ = v___x_3314_;
v___y_3240_ = v_contents_3300_;
v_mainModuleName_3241_ = v_name_3312_;
goto v___jp_3235_;
}
}
else
{
lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3323_; 
lean_del_object(v___x_3308_);
lean_dec_ref(v_contents_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec_ref(v___x_3178_);
lean_dec(v_incrHeaderSaveFileName_x3f_3160_);
lean_dec(v_incrLoadFileName_x3f_3159_);
lean_dec(v_incrSaveFileName_x3f_3158_);
lean_dec_ref(v_errorOnKinds_3155_);
lean_dec(v_bcFileName_x3f_3153_);
lean_dec(v_cFileName_x3f_3152_);
lean_dec(v_ileanFileName_x3f_3151_);
lean_dec(v_oleanFileName_x3f_3150_);
v_a_3316_ = lean_ctor_get(v___x_3310_, 0);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3318_ = v___x_3310_;
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v___x_3310_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3321_; 
if (v_isShared_3319_ == 0)
{
v___x_3321_ = v___x_3318_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_a_3316_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
}
}
}
v___jp_3325_:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; uint8_t v___x_3338_; 
v___x_3334_ = lean_nat_add(v_startInclusive_3330_, v___y_3333_);
lean_dec(v___y_3333_);
lean_inc(v___x_3334_);
lean_inc_ref(v_str_3329_);
v___x_3335_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3335_, 0, v_str_3329_);
lean_ctor_set(v___x_3335_, 1, v_startInclusive_3330_);
lean_ctor_set(v___x_3335_, 2, v___x_3334_);
v___x_3336_ = l_String_Slice_trimAscii(v___x_3335_);
v___x_3337_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__10, &l___private_Lean_Shell_0__Lean_shellMain___closed__10_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10);
v___x_3338_ = l_String_Slice_beq(v___x_3336_, v___x_3337_);
if (v___x_3338_ == 0)
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
lean_dec(v___x_3334_);
lean_dec_ref(v___y_3332_);
lean_dec(v_endExclusive_3331_);
lean_dec_ref(v_str_3329_);
lean_dec(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec_ref(v___x_3178_);
lean_dec(v_incrHeaderSaveFileName_x3f_3160_);
lean_dec(v_incrLoadFileName_x3f_3159_);
lean_dec(v_incrSaveFileName_x3f_3158_);
lean_dec_ref(v_errorOnKinds_3155_);
lean_dec(v_bcFileName_x3f_3153_);
lean_dec(v_cFileName_x3f_3152_);
lean_dec(v_ileanFileName_x3f_3151_);
lean_dec(v_oleanFileName_x3f_3150_);
lean_dec(v_setupFileName_x3f_3149_);
lean_dec(v_rootDir_x3f_3148_);
v___x_3339_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__11));
v___x_3340_ = l_String_Slice_toString(v___x_3336_);
lean_dec_ref(v___x_3336_);
v___x_3341_ = lean_string_append(v___x_3339_, v___x_3340_);
lean_dec_ref(v___x_3340_);
v___x_3342_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
v___x_3343_ = lean_string_append(v___x_3341_, v___x_3342_);
v___x_3344_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_3343_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3352_; 
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3352_ == 0)
{
lean_object* v_unused_3353_; 
v_unused_3353_ = lean_ctor_get(v___x_3344_, 0);
lean_dec(v_unused_3353_);
v___x_3346_ = v___x_3344_;
v_isShared_3347_ = v_isSharedCheck_3352_;
goto v_resetjp_3345_;
}
else
{
lean_dec(v___x_3344_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3352_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3348_; lean_object* v___x_3350_; 
v___x_3348_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v___x_3348_);
v___x_3350_ = v___x_3346_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v___x_3348_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
else
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3361_; 
v_a_3354_ = lean_ctor_get(v___x_3344_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3356_ = v___x_3344_;
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3344_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3359_; 
if (v_isShared_3357_ == 0)
{
v___x_3359_ = v___x_3356_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_a_3354_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
else
{
lean_object* v___x_3362_; 
lean_dec_ref(v___x_3336_);
v___x_3362_ = lean_string_utf8_extract_fast(v_str_3329_, v___x_3334_, v_endExclusive_3331_);
lean_dec(v_endExclusive_3331_);
lean_dec(v___x_3334_);
lean_dec_ref(v_str_3329_);
v___y_3296_ = v___y_3326_;
v___y_3297_ = v___y_3327_;
v___y_3298_ = v___y_3328_;
v___y_3299_ = v___y_3332_;
v_contents_3300_ = v___x_3362_;
goto v___jp_3295_;
}
}
v___jp_3363_:
{
if (lean_obj_tag(v___y_3367_) == 0)
{
lean_object* v_a_3368_; lean_object* v___x_3369_; 
v_a_3368_ = lean_ctor_get(v___y_3367_, 0);
lean_inc(v_a_3368_);
lean_dec_ref_known(v___y_3367_, 1);
v___x_3369_ = lean_decode_lossy_utf8(v_a_3368_);
lean_dec(v_a_3368_);
if (v_onlyDeps_3144_ == 0)
{
if (v_onlySrcDeps_3145_ == 0)
{
lean_object* v___x_3370_; 
lean_inc_ref(v___x_3369_);
v___x_3370_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v___x_3369_);
if (lean_obj_tag(v___x_3370_) == 1)
{
lean_object* v_val_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
lean_dec_ref(v___x_3369_);
v_val_3371_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_val_3371_);
lean_dec_ref_known(v___x_3370_, 1);
v___x_3372_ = lean_unsigned_to_nat(0u);
v___x_3373_ = lean_box(0);
v___x_3374_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3371_, v___x_3372_, v___x_3373_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v_str_3375_; lean_object* v_startInclusive_3376_; lean_object* v_endExclusive_3377_; lean_object* v___x_3378_; 
v_str_3375_ = lean_ctor_get(v_val_3371_, 0);
lean_inc_ref(v_str_3375_);
v_startInclusive_3376_ = lean_ctor_get(v_val_3371_, 1);
lean_inc(v_startInclusive_3376_);
v_endExclusive_3377_ = lean_ctor_get(v_val_3371_, 2);
lean_inc(v_endExclusive_3377_);
lean_dec(v_val_3371_);
v___x_3378_ = lean_nat_sub(v_endExclusive_3377_, v_startInclusive_3376_);
lean_inc_ref(v___y_3365_);
v___y_3326_ = v___y_3365_;
v___y_3327_ = v___y_3364_;
v___y_3328_ = v___y_3366_;
v_str_3329_ = v_str_3375_;
v_startInclusive_3330_ = v_startInclusive_3376_;
v_endExclusive_3331_ = v_endExclusive_3377_;
v___y_3332_ = v___y_3365_;
v___y_3333_ = v___x_3378_;
goto v___jp_3325_;
}
else
{
lean_object* v_val_3379_; lean_object* v_str_3380_; lean_object* v_startInclusive_3381_; lean_object* v_endExclusive_3382_; 
v_val_3379_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_val_3379_);
lean_dec_ref_known(v___x_3374_, 1);
v_str_3380_ = lean_ctor_get(v_val_3371_, 0);
lean_inc_ref(v_str_3380_);
v_startInclusive_3381_ = lean_ctor_get(v_val_3371_, 1);
lean_inc(v_startInclusive_3381_);
v_endExclusive_3382_ = lean_ctor_get(v_val_3371_, 2);
lean_inc(v_endExclusive_3382_);
lean_dec(v_val_3371_);
lean_inc_ref(v___y_3365_);
v___y_3326_ = v___y_3365_;
v___y_3327_ = v___y_3364_;
v___y_3328_ = v___y_3366_;
v_str_3329_ = v_str_3380_;
v_startInclusive_3330_ = v_startInclusive_3381_;
v_endExclusive_3331_ = v_endExclusive_3382_;
v___y_3332_ = v___y_3365_;
v___y_3333_ = v_val_3379_;
goto v___jp_3325_;
}
}
else
{
lean_dec(v___x_3370_);
lean_inc_ref(v___y_3365_);
v___y_3296_ = v___y_3365_;
v___y_3297_ = v___y_3364_;
v___y_3298_ = v___y_3366_;
v___y_3299_ = v___y_3365_;
v_contents_3300_ = v___x_3369_;
goto v___jp_3295_;
}
}
else
{
lean_object* v___x_3383_; lean_object* v___x_3384_; 
lean_dec(v___y_3366_);
lean_dec(v___y_3364_);
lean_dec_ref(v___x_3178_);
lean_dec(v_incrHeaderSaveFileName_x3f_3160_);
lean_dec(v_incrLoadFileName_x3f_3159_);
lean_dec(v_incrSaveFileName_x3f_3158_);
lean_dec_ref(v_errorOnKinds_3155_);
lean_dec(v_bcFileName_x3f_3153_);
lean_dec(v_cFileName_x3f_3152_);
lean_dec(v_ileanFileName_x3f_3151_);
lean_dec(v_oleanFileName_x3f_3150_);
lean_dec(v_setupFileName_x3f_3149_);
lean_dec(v_rootDir_x3f_3148_);
v___x_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3383_, 0, v___y_3365_);
v___x_3384_ = l_Lean_Elab_printImportSrcs(v___x_3369_, v___x_3383_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3392_; 
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3392_ == 0)
{
lean_object* v_unused_3393_; 
v_unused_3393_ = lean_ctor_get(v___x_3384_, 0);
lean_dec(v_unused_3393_);
v___x_3386_ = v___x_3384_;
v_isShared_3387_ = v_isSharedCheck_3392_;
goto v_resetjp_3385_;
}
else
{
lean_dec(v___x_3384_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3392_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3388_; lean_object* v___x_3390_; 
v___x_3388_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 0, v___x_3388_);
v___x_3390_ = v___x_3386_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3388_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
else
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
v_a_3394_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3396_ = v___x_3384_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3384_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3399_; 
if (v_isShared_3397_ == 0)
{
v___x_3399_ = v___x_3396_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3394_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
}
else
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
lean_dec(v___y_3366_);
lean_dec(v___y_3364_);
lean_dec_ref(v___x_3178_);
lean_dec(v_incrHeaderSaveFileName_x3f_3160_);
lean_dec(v_incrLoadFileName_x3f_3159_);
lean_dec(v_incrSaveFileName_x3f_3158_);
lean_dec_ref(v_errorOnKinds_3155_);
lean_dec(v_bcFileName_x3f_3153_);
lean_dec(v_cFileName_x3f_3152_);
lean_dec(v_ileanFileName_x3f_3151_);
lean_dec(v_oleanFileName_x3f_3150_);
lean_dec(v_setupFileName_x3f_3149_);
lean_dec(v_rootDir_x3f_3148_);
v___x_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3402_, 0, v___y_3365_);
v___x_3403_ = l_Lean_Elab_printImports(v___x_3369_, v___x_3402_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3411_; 
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3411_ == 0)
{
lean_object* v_unused_3412_; 
v_unused_3412_ = lean_ctor_get(v___x_3403_, 0);
lean_dec(v_unused_3412_);
v___x_3405_ = v___x_3403_;
v_isShared_3406_ = v_isSharedCheck_3411_;
goto v_resetjp_3404_;
}
else
{
lean_dec(v___x_3403_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3411_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3407_; lean_object* v___x_3409_; 
v___x_3407_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3406_ == 0)
{
lean_ctor_set(v___x_3405_, 0, v___x_3407_);
v___x_3409_ = v___x_3405_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3407_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
else
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
v_a_3413_ = lean_ctor_get(v___x_3403_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3403_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3403_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
}
else
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3428_; 
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec_ref(v___x_3178_);
lean_dec(v_incrHeaderSaveFileName_x3f_3160_);
lean_dec(v_incrLoadFileName_x3f_3159_);
lean_dec(v_incrSaveFileName_x3f_3158_);
lean_dec_ref(v_errorOnKinds_3155_);
lean_dec(v_bcFileName_x3f_3153_);
lean_dec(v_cFileName_x3f_3152_);
lean_dec(v_ileanFileName_x3f_3151_);
lean_dec(v_oleanFileName_x3f_3150_);
lean_dec(v_setupFileName_x3f_3149_);
lean_dec(v_rootDir_x3f_3148_);
v_a_3421_ = lean_ctor_get(v___y_3367_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___y_3367_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3423_ = v___y_3367_;
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___y_3367_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3424_ == 0)
{
v___x_3426_ = v___x_3423_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_a_3421_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
v___jp_3429_:
{
if (v_useStdin_3143_ == 0)
{
lean_object* v___x_3433_; 
v___x_3433_ = l_IO_FS_readBinFile(v_fileName_3432_);
v___y_3364_ = v___y_3430_;
v___y_3365_ = v_fileName_3432_;
v___y_3366_ = v___y_3431_;
v___y_3367_ = v___x_3433_;
goto v___jp_3363_;
}
else
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3434_ = lean_get_stdin();
v___x_3435_ = l_IO_FS_Stream_readBinToEnd(v___x_3434_);
v___y_3364_ = v___y_3430_;
v___y_3365_ = v_fileName_3432_;
v___y_3366_ = v___y_3431_;
v___y_3367_ = v___x_3435_;
goto v___jp_3363_;
}
}
v___jp_3436_:
{
if (lean_obj_tag(v___y_3438_) == 1)
{
lean_object* v_val_3439_; 
v_val_3439_ = lean_ctor_get(v___y_3438_, 0);
lean_inc(v_val_3439_);
v___y_3430_ = v___y_3437_;
v___y_3431_ = v___y_3438_;
v_fileName_3432_ = v_val_3439_;
goto v___jp_3429_;
}
else
{
if (v_useStdin_3143_ == 0)
{
lean_object* v___x_3440_; lean_object* v___x_3441_; 
lean_dec(v___y_3438_);
lean_dec(v___y_3437_);
lean_dec_ref(v___x_3178_);
lean_dec(v_incrHeaderSaveFileName_x3f_3160_);
lean_dec(v_incrLoadFileName_x3f_3159_);
lean_dec(v_incrSaveFileName_x3f_3158_);
lean_dec_ref(v_errorOnKinds_3155_);
lean_dec(v_bcFileName_x3f_3153_);
lean_dec(v_cFileName_x3f_3152_);
lean_dec(v_ileanFileName_x3f_3151_);
lean_dec(v_oleanFileName_x3f_3150_);
lean_dec(v_setupFileName_x3f_3149_);
lean_dec(v_rootDir_x3f_3148_);
v___x_3440_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__4));
v___x_3441_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_3440_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v___x_3442_; 
lean_dec_ref_known(v___x_3441_, 1);
v___x_3442_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_3205_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3450_; 
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3450_ == 0)
{
lean_object* v_unused_3451_; 
v_unused_3451_ = lean_ctor_get(v___x_3442_, 0);
lean_dec(v_unused_3451_);
v___x_3444_ = v___x_3442_;
v_isShared_3445_ = v_isSharedCheck_3450_;
goto v_resetjp_3443_;
}
else
{
lean_dec(v___x_3442_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3450_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3446_; lean_object* v___x_3448_; 
v___x_3446_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3445_ == 0)
{
lean_ctor_set(v___x_3444_, 0, v___x_3446_);
v___x_3448_ = v___x_3444_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3446_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
else
{
lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3459_; 
v_a_3452_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3454_ = v___x_3442_;
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_3442_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
if (v_isShared_3455_ == 0)
{
v___x_3457_ = v___x_3454_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_a_3452_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
}
else
{
lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
v_a_3460_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3462_ = v___x_3441_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_3441_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3465_; 
if (v_isShared_3463_ == 0)
{
v___x_3465_ = v___x_3462_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_a_3460_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
else
{
lean_object* v___x_3468_; 
v___x_3468_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__12));
v___y_3430_ = v___y_3437_;
v___y_3431_ = v___y_3438_;
v_fileName_3432_ = v___x_3468_;
goto v___jp_3429_;
}
}
}
v___jp_3469_:
{
uint8_t v___x_3473_; 
v___x_3473_ = l_List_isEmpty___redArg(v___y_3470_);
if (v___x_3473_ == 0)
{
lean_dec(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___x_3178_);
lean_dec(v_incrHeaderSaveFileName_x3f_3160_);
lean_dec(v_incrLoadFileName_x3f_3159_);
lean_dec(v_incrSaveFileName_x3f_3158_);
lean_dec_ref(v_errorOnKinds_3155_);
lean_dec(v_bcFileName_x3f_3153_);
lean_dec(v_cFileName_x3f_3152_);
lean_dec(v_ileanFileName_x3f_3151_);
lean_dec(v_oleanFileName_x3f_3150_);
lean_dec(v_setupFileName_x3f_3149_);
lean_dec(v_rootDir_x3f_3148_);
goto v___jp_3206_;
}
else
{
if (v___y_3472_ == 0)
{
v___y_3437_ = v___y_3470_;
v___y_3438_ = v___y_3471_;
goto v___jp_3436_;
}
else
{
lean_dec(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___x_3178_);
lean_dec(v_incrHeaderSaveFileName_x3f_3160_);
lean_dec(v_incrLoadFileName_x3f_3159_);
lean_dec(v_incrSaveFileName_x3f_3158_);
lean_dec_ref(v_errorOnKinds_3155_);
lean_dec(v_bcFileName_x3f_3153_);
lean_dec(v_cFileName_x3f_3152_);
lean_dec(v_ileanFileName_x3f_3151_);
lean_dec(v_oleanFileName_x3f_3150_);
lean_dec(v_setupFileName_x3f_3149_);
lean_dec(v_rootDir_x3f_3148_);
goto v___jp_3206_;
}
}
}
v___jp_3474_:
{
if (v_run_3157_ == 0)
{
v___y_3470_ = v_snd_3477_;
v___y_3471_ = v_fst_3476_;
v___y_3472_ = v___y_3475_;
goto v___jp_3469_;
}
else
{
if (v___y_3475_ == 0)
{
v___y_3437_ = v_snd_3477_;
v___y_3438_ = v_fst_3476_;
goto v___jp_3436_;
}
else
{
v___y_3470_ = v_snd_3477_;
v___y_3471_ = v_fst_3476_;
v___y_3472_ = v___y_3475_;
goto v___jp_3469_;
}
}
}
v___jp_3478_:
{
if (lean_obj_tag(v_args_3109_) == 0)
{
lean_object* v___x_3480_; 
v___x_3480_ = lean_box(0);
v___y_3475_ = v___y_3479_;
v_fst_3476_ = v___x_3480_;
v_snd_3477_ = v_args_3109_;
goto v___jp_3474_;
}
else
{
lean_object* v_head_3481_; lean_object* v_tail_3482_; lean_object* v___x_3483_; 
v_head_3481_ = lean_ctor_get(v_args_3109_, 0);
lean_inc(v_head_3481_);
v_tail_3482_ = lean_ctor_get(v_args_3109_, 1);
lean_inc(v_tail_3482_);
lean_dec_ref_known(v_args_3109_, 2);
v___x_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3483_, 0, v_head_3481_);
v___y_3475_ = v___y_3479_;
v_fst_3476_ = v___x_3483_;
v_snd_3477_ = v_tail_3482_;
goto v___jp_3474_;
}
}
v___jp_3484_:
{
switch(v_component_3142_)
{
case 0:
{
lean_dec_ref(v_forwardedArgs_3141_);
if (v_onlyDeps_3144_ == 0)
{
v___y_3479_ = v_printLibDir_3139_;
goto v___jp_3478_;
}
else
{
if (v_depsJson_3146_ == 0)
{
v___y_3479_ = v_depsJson_3146_;
goto v___jp_3478_;
}
else
{
lean_dec_ref(v___x_3178_);
lean_dec(v_incrHeaderSaveFileName_x3f_3160_);
lean_dec(v_incrLoadFileName_x3f_3159_);
lean_dec(v_incrSaveFileName_x3f_3158_);
lean_dec_ref(v_errorOnKinds_3155_);
lean_dec(v_bcFileName_x3f_3153_);
lean_dec(v_cFileName_x3f_3152_);
lean_dec(v_ileanFileName_x3f_3151_);
lean_dec(v_oleanFileName_x3f_3150_);
lean_dec(v_setupFileName_x3f_3149_);
lean_dec(v_rootDir_x3f_3148_);
if (v_useStdin_3143_ == 0)
{
lean_object* v___x_3485_; 
v___x_3485_ = lean_array_mk(v_args_3109_);
v_fns_3113_ = v___x_3485_;
goto v___jp_3112_;
}
else
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
lean_dec(v_args_3109_);
v___x_3486_ = lean_get_stdin();
v___x_3487_ = l_IO_FS_Stream_lines(v___x_3486_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3488_);
lean_dec_ref_known(v___x_3487_, 1);
v_fns_3113_ = v_a_3488_;
goto v___jp_3112_;
}
else
{
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3496_; 
v_a_3489_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3491_ = v___x_3487_;
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3487_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3494_; 
if (v_isShared_3492_ == 0)
{
v___x_3494_ = v___x_3491_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3489_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; 
lean_dec_ref(v___x_3178_);
lean_dec(v_incrHeaderSaveFileName_x3f_3160_);
lean_dec(v_incrLoadFileName_x3f_3159_);
lean_dec(v_incrSaveFileName_x3f_3158_);
lean_dec_ref(v_errorOnKinds_3155_);
lean_dec(v_bcFileName_x3f_3153_);
lean_dec(v_cFileName_x3f_3152_);
lean_dec(v_ileanFileName_x3f_3151_);
lean_dec(v_oleanFileName_x3f_3150_);
lean_dec(v_setupFileName_x3f_3149_);
lean_dec(v_rootDir_x3f_3148_);
lean_dec(v_args_3109_);
v___x_3497_ = lean_array_to_list(v_forwardedArgs_3141_);
v___x_3498_ = l_Lean_Server_Watchdog_watchdogMain(v___x_3497_);
return v___x_3498_;
}
default: 
{
lean_object* v___x_3499_; 
lean_dec(v_incrHeaderSaveFileName_x3f_3160_);
lean_dec(v_incrLoadFileName_x3f_3159_);
lean_dec(v_incrSaveFileName_x3f_3158_);
lean_dec_ref(v_errorOnKinds_3155_);
lean_dec(v_bcFileName_x3f_3153_);
lean_dec(v_cFileName_x3f_3152_);
lean_dec(v_ileanFileName_x3f_3151_);
lean_dec(v_oleanFileName_x3f_3150_);
lean_dec(v_setupFileName_x3f_3149_);
lean_dec(v_rootDir_x3f_3148_);
lean_dec_ref(v_forwardedArgs_3141_);
lean_dec(v_args_3109_);
v___x_3499_ = l_Lean_Server_FileWorker_workerMain(v___x_3178_);
return v___x_3499_;
}
}
}
v___jp_3500_:
{
lean_object* v___x_3501_; lean_object* v_timeout_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; 
v___x_3501_ = l___private_Lean_Shell_0__Lean_timeout;
v_timeout_3502_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3178_, v___x_3501_);
v___x_3503_ = lean_unsigned_to_nat(0u);
v___x_3504_ = lean_nat_dec_eq(v_timeout_3502_, v___x_3503_);
if (v___x_3504_ == 0)
{
size_t v___x_3505_; size_t v___x_3506_; size_t v___x_3507_; lean_object* v___x_3508_; 
v___x_3505_ = lean_usize_of_nat(v_timeout_3502_);
lean_dec(v_timeout_3502_);
v___x_3506_ = ((size_t)1000ULL);
v___x_3507_ = lean_usize_mul(v___x_3505_, v___x_3506_);
v___x_3508_ = lean_internal_set_max_heartbeat(v___x_3507_);
goto v___jp_3484_;
}
else
{
lean_dec(v_timeout_3502_);
goto v___jp_3484_;
}
}
}
else
{
lean_object* v___x_3518_; 
lean_dec_ref(v_opts_3110_);
lean_dec(v_args_3109_);
v___x_3518_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; lean_object* v___x_3520_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_a_3519_);
lean_dec_ref_known(v___x_3518_, 1);
v___x_3520_ = l_Lean_getLibDir(v_a_3519_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v___x_3522_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3521_);
lean_dec_ref_known(v___x_3520_, 1);
v___x_3522_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3521_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3530_; 
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3530_ == 0)
{
lean_object* v_unused_3531_; 
v_unused_3531_ = lean_ctor_get(v___x_3522_, 0);
lean_dec(v_unused_3531_);
v___x_3524_ = v___x_3522_;
v_isShared_3525_ = v_isSharedCheck_3530_;
goto v_resetjp_3523_;
}
else
{
lean_dec(v___x_3522_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3530_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3526_; lean_object* v___x_3528_; 
v___x_3526_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 0, v___x_3526_);
v___x_3528_ = v___x_3524_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3526_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
else
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
v_a_3532_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3522_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3522_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3532_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
v_a_3540_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3520_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3520_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
v_a_3548_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3518_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3518_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
}
else
{
lean_object* v___x_3556_; 
lean_dec_ref(v_opts_3110_);
lean_dec(v_args_3109_);
v___x_3556_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v_a_3557_; lean_object* v___x_3558_; 
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
lean_inc(v_a_3557_);
lean_dec_ref_known(v___x_3556_, 1);
v___x_3558_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3557_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3566_; 
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3566_ == 0)
{
lean_object* v_unused_3567_; 
v_unused_3567_ = lean_ctor_get(v___x_3558_, 0);
lean_dec(v_unused_3567_);
v___x_3560_ = v___x_3558_;
v_isShared_3561_ = v_isSharedCheck_3566_;
goto v_resetjp_3559_;
}
else
{
lean_dec(v___x_3558_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3566_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3562_; lean_object* v___x_3564_; 
v___x_3562_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 0, v___x_3562_);
v___x_3564_ = v___x_3560_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3562_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
else
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3575_; 
v_a_3568_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3570_ = v___x_3558_;
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3558_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3573_; 
if (v_isShared_3571_ == 0)
{
v___x_3573_ = v___x_3570_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_a_3568_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
}
else
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3583_; 
v_a_3576_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3578_ = v___x_3556_;
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3556_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3581_; 
if (v_isShared_3579_ == 0)
{
v___x_3581_ = v___x_3578_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_a_3576_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
}
v___jp_3112_:
{
lean_object* v___x_3114_; 
v___x_3114_ = l_Lean_printImportsJson(v_fns_3113_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3122_; 
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3122_ == 0)
{
lean_object* v_unused_3123_; 
v_unused_3123_ = lean_ctor_get(v___x_3114_, 0);
lean_dec(v_unused_3123_);
v___x_3116_ = v___x_3114_;
v_isShared_3117_ = v_isSharedCheck_3122_;
goto v_resetjp_3115_;
}
else
{
lean_dec(v___x_3114_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3122_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3118_; lean_object* v___x_3120_; 
v___x_3118_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 0, v___x_3118_);
v___x_3120_ = v___x_3116_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3118_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
else
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
v_a_3124_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3126_ = v___x_3114_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3114_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3124_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
v___jp_3132_:
{
uint8_t v___x_3133_; lean_object* v___x_3134_; 
v___x_3133_ = 0;
v___x_3134_ = lean_io_exit(v___x_3133_);
return v___x_3134_;
}
v___jp_3135_:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3136_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
return v___x_3137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object* v_args_3584_, lean_object* v_opts_3585_, lean_object* v_a_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = lean_shell_main(v_args_3584_, v_opts_3585_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(lean_object* v_val_3588_, lean_object* v_inst_3589_, lean_object* v_R_3590_, lean_object* v_a_3591_, lean_object* v_b_3592_, lean_object* v_c_3593_){
_start:
{
lean_object* v___x_3594_; 
v___x_3594_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3588_, v_a_3591_, v_b_3592_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___boxed(lean_object* v_val_3595_, lean_object* v_inst_3596_, lean_object* v_R_3597_, lean_object* v_a_3598_, lean_object* v_b_3599_, lean_object* v_c_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(v_val_3595_, v_inst_3596_, v_R_3597_, v_a_3598_, v_b_3599_, v_c_3600_);
lean_dec(v_b_3599_);
lean_dec_ref(v_val_3595_);
return v_res_3601_;
}
}
lean_object* runtime_initialize_Lean_Elab_Frontend(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ParseImportsFast(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Watchdog(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_FileWorker(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_EmitC(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_Process(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Shell(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Frontend(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ParseImportsFast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Watchdog(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_FileWorker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_EmitC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_Process(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Shell_0__Lean_shortVersionString = _init_l___private_Lean_Shell_0__Lean_shortVersionString();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shortVersionString);
l___private_Lean_Shell_0__Lean_versionHeader = _init_l___private_Lean_Shell_0__Lean_versionHeader();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_versionHeader);
l___private_Lean_Shell_0__Lean_featuresString = _init_l___private_Lean_Shell_0__Lean_featuresString();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_featuresString);
res = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Shell_0__Lean_maxMemory = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Shell_0__Lean_maxMemory);
lean_dec_ref(res);
res = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Shell_0__Lean_timeout = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Shell_0__Lean_timeout);
lean_dec_ref(res);
res = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Shell_0__Lean_verbose = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Shell_0__Lean_verbose);
lean_dec_ref(res);
l___private_Lean_Shell_0__Lean_defaultTrustLevel = _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel();
l___private_Lean_Shell_0__Lean_defaultNumThreads = _init_l___private_Lean_Shell_0__Lean_defaultNumThreads();
l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1 = _init_l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1);
l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1 = _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Shell(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Frontend(uint8_t builtin);
lean_object* initialize_Lean_Elab_ParseImportsFast(uint8_t builtin);
lean_object* initialize_Lean_Server_Watchdog(uint8_t builtin);
lean_object* initialize_Lean_Server_FileWorker(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_EmitC(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
lean_object* initialize_Lean_Compiler_Options(uint8_t builtin);
lean_object* initialize_Std_Async_Process(uint8_t builtin);
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
res = initialize_Lean_Compiler_LCNF_EmitC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Async_Process(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Shell(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Shell(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Shell(builtin);
}
#ifdef __cplusplus
}
#endif
