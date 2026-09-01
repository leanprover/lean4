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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* l_Lean_getOptionDecls();
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_toName(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1;
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
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
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
static lean_object* _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1(void){
_start:
{
lean_object* v___x_519_; uint32_t v___x_520_; uint32_t v___x_521_; uint8_t v___x_522_; uint8_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_519_ = lean_box(0);
v___x_520_ = l___private_Lean_Shell_0__Lean_defaultNumThreads;
v___x_521_ = l___private_Lean_Shell_0__Lean_defaultTrustLevel;
v___x_522_ = 0;
v___x_523_ = 0;
v___x_524_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0));
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
LEAN_EXPORT lean_object* lean_shell_options_mk(lean_object* v_x_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1, &l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1_once, _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1);
return v___x_528_;
}
}
LEAN_EXPORT uint8_t lean_shell_options_get_run(lean_object* v_opts_529_){
_start:
{
uint8_t v_run_530_; 
v_run_530_ = lean_ctor_get_uint8(v_opts_529_, sizeof(void*)*13 + 17);
lean_dec_ref(v_opts_529_);
return v_run_530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getRun___boxed(lean_object* v_opts_531_){
_start:
{
uint8_t v_res_532_; lean_object* v_r_533_; 
v_res_532_ = lean_shell_options_get_run(v_opts_531_);
v_r_533_ = lean_box(v_res_532_);
return v_r_533_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(lean_object* v_opts_534_, lean_object* v_opt_535_){
_start:
{
lean_object* v_name_536_; lean_object* v_defValue_537_; lean_object* v_map_538_; lean_object* v___x_539_; 
v_name_536_ = lean_ctor_get(v_opt_535_, 0);
v_defValue_537_ = lean_ctor_get(v_opt_535_, 1);
v_map_538_ = lean_ctor_get(v_opts_534_, 0);
v___x_539_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_538_, v_name_536_);
if (lean_obj_tag(v___x_539_) == 0)
{
uint8_t v___x_540_; 
v___x_540_ = lean_unbox(v_defValue_537_);
return v___x_540_;
}
else
{
lean_object* v_val_541_; 
v_val_541_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_val_541_);
lean_dec_ref_known(v___x_539_, 1);
if (lean_obj_tag(v_val_541_) == 1)
{
uint8_t v_v_542_; 
v_v_542_ = lean_ctor_get_uint8(v_val_541_, 0);
lean_dec_ref_known(v_val_541_, 0);
return v_v_542_;
}
else
{
uint8_t v___x_543_; 
lean_dec(v_val_541_);
v___x_543_ = lean_unbox(v_defValue_537_);
return v___x_543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0___boxed(lean_object* v_opts_544_, lean_object* v_opt_545_){
_start:
{
uint8_t v_res_546_; lean_object* v_r_547_; 
v_res_546_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v_opts_544_, v_opt_545_);
lean_dec_ref(v_opt_545_);
lean_dec_ref(v_opts_544_);
v_r_547_ = lean_box(v_res_546_);
return v_r_547_;
}
}
LEAN_EXPORT uint8_t lean_shell_options_get_profiler(lean_object* v_opts_548_){
_start:
{
lean_object* v_leanOpts_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v_leanOpts_549_ = lean_ctor_get(v_opts_548_, 0);
lean_inc_ref(v_leanOpts_549_);
lean_dec_ref(v_opts_548_);
v___x_550_ = l_Lean_profiler;
v___x_551_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v_leanOpts_549_, v___x_550_);
lean_dec_ref(v_leanOpts_549_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getProfiler___boxed(lean_object* v_opts_552_){
_start:
{
uint8_t v_res_553_; lean_object* v_r_554_; 
v_res_553_ = lean_shell_options_get_profiler(v_opts_552_);
v_r_554_ = lean_box(v_res_553_);
return v_r_554_;
}
}
LEAN_EXPORT uint32_t lean_shell_options_get_num_threads(lean_object* v_opts_555_){
_start:
{
uint32_t v_numThreads_556_; 
v_numThreads_556_ = lean_ctor_get_uint32(v_opts_555_, sizeof(void*)*13 + 4);
lean_dec_ref(v_opts_555_);
return v_numThreads_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getNumThreads___boxed(lean_object* v_opts_557_){
_start:
{
uint32_t v_res_558_; lean_object* v_r_559_; 
v_res_558_ = lean_shell_options_get_num_threads(v_opts_557_);
v_r_559_ = lean_box_uint32(v_res_558_);
return v_r_559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_checkOptArg(lean_object* v_optName_562_, lean_object* v_optArg_x3f_563_){
_start:
{
if (lean_obj_tag(v_optArg_x3f_563_) == 1)
{
lean_object* v_val_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
v_val_565_ = lean_ctor_get(v_optArg_x3f_563_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v_optArg_x3f_563_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v_optArg_x3f_563_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_val_565_);
lean_dec(v_optArg_x3f_563_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set_tag(v___x_567_, 0);
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_val_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
lean_dec(v_optArg_x3f_563_);
v___x_573_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__0));
v___x_574_ = lean_string_append(v___x_573_, v_optName_562_);
v___x_575_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__1));
v___x_576_ = lean_string_append(v___x_574_, v___x_575_);
v___x_577_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
v___x_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_checkOptArg___boxed(lean_object* v_optName_579_, lean_object* v_optArg_x3f_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l___private_Lean_Shell_0__Lean_checkOptArg(v_optName_579_, v_optArg_x3f_580_);
lean_dec_ref(v_optName_579_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0(lean_object* v_o_586_, lean_object* v_k_587_, lean_object* v_v_588_){
_start:
{
lean_object* v_map_589_; uint8_t v_hasTrace_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_604_; 
v_map_589_ = lean_ctor_get(v_o_586_, 0);
v_hasTrace_590_ = lean_ctor_get_uint8(v_o_586_, sizeof(void*)*1);
v_isSharedCheck_604_ = !lean_is_exclusive(v_o_586_);
if (v_isSharedCheck_604_ == 0)
{
v___x_592_ = v_o_586_;
v_isShared_593_ = v_isSharedCheck_604_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_map_589_);
lean_dec(v_o_586_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_604_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_594_, 0, v_v_588_);
lean_inc(v_k_587_);
v___x_595_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_587_, v___x_594_, v_map_589_);
if (v_hasTrace_590_ == 0)
{
lean_object* v___x_596_; uint8_t v___x_597_; lean_object* v___x_599_; 
v___x_596_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_597_ = l_Lean_Name_isPrefixOf(v___x_596_, v_k_587_);
lean_dec(v_k_587_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_595_);
v___x_599_ = v___x_592_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_595_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_ctor_set_uint8(v___x_599_, sizeof(void*)*1, v___x_597_);
return v___x_599_;
}
}
else
{
lean_object* v___x_602_; 
lean_dec(v_k_587_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_595_);
v___x_602_ = v___x_592_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_595_);
lean_ctor_set_uint8(v_reuseFailAlloc_603_, sizeof(void*)*1, v_hasTrace_590_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(lean_object* v___x_605_, lean_object* v_arg_606_, lean_object* v_a_607_, lean_object* v_b_608_){
_start:
{
uint8_t v_decide_609_; 
v_decide_609_ = lean_nat_dec_eq(v_a_607_, v___x_605_);
if (v_decide_609_ == 0)
{
uint32_t v___x_610_; uint32_t v___x_611_; uint8_t v___x_612_; 
v___x_610_ = lean_string_utf8_get_fast(v_arg_606_, v_a_607_);
v___x_611_ = 61;
v___x_612_ = lean_uint32_dec_eq(v___x_610_, v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = lean_box(0);
v___x_614_ = lean_string_utf8_next_fast(v_arg_606_, v_a_607_);
lean_dec(v_a_607_);
v_a_607_ = v___x_614_;
v_b_608_ = v___x_613_;
goto _start;
}
else
{
lean_object* v___x_616_; 
v___x_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_616_, 0, v_a_607_);
return v___x_616_;
}
}
else
{
lean_dec(v_a_607_);
lean_inc(v_b_608_);
return v_b_608_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg___boxed(lean_object* v___x_617_, lean_object* v_arg_618_, lean_object* v_a_619_, lean_object* v_b_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_617_, v_arg_618_, v_a_619_, v_b_620_);
lean_dec(v_b_620_);
lean_dec_ref(v_arg_618_);
lean_dec(v___x_617_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_setConfigOption(lean_object* v_opts_625_, lean_object* v_arg_626_){
_start:
{
lean_object* v___y_629_; lean_object* v_searcher_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v_searcher_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = lean_string_utf8_byte_size(v_arg_626_);
v___x_662_ = lean_box(0);
v___x_663_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_661_, v_arg_626_, v_searcher_660_, v___x_662_);
if (lean_obj_tag(v___x_663_) == 0)
{
v___y_629_ = v___x_661_;
goto v___jp_628_;
}
else
{
lean_object* v_val_664_; 
v_val_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_val_664_);
lean_dec_ref_known(v___x_663_, 1);
v___y_629_ = v_val_664_;
goto v___jp_628_;
}
v___jp_628_:
{
lean_object* v___x_630_; uint8_t v_decide_631_; 
v___x_630_ = lean_string_utf8_byte_size(v_arg_626_);
v_decide_631_ = lean_nat_dec_eq(v___y_629_, v___x_630_);
if (v_decide_631_ == 0)
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_649_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_649_ == 0)
{
v___x_635_ = v___x_632_;
v_isShared_636_ = v_isSharedCheck_649_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_632_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_649_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v_name_640_; lean_object* v_val_641_; lean_object* v___x_642_; 
v___x_637_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_629_);
lean_inc_ref(v_arg_626_);
v___x_638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_638_, 0, v_arg_626_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
lean_ctor_set(v___x_638_, 2, v___y_629_);
v___x_639_ = lean_string_utf8_next_fast(v_arg_626_, v___y_629_);
lean_dec(v___y_629_);
v_name_640_ = l_String_Slice_toName(v___x_638_);
lean_dec_ref_known(v___x_638_, 3);
v_val_641_ = lean_string_utf8_extract_fast(v_arg_626_, v___x_639_, v___x_630_);
lean_dec_ref(v_arg_626_);
v___x_642_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_633_, v_name_640_);
lean_dec(v_a_633_);
if (lean_obj_tag(v___x_642_) == 1)
{
lean_object* v_val_643_; lean_object* v___x_644_; 
lean_del_object(v___x_635_);
v_val_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_val_643_);
lean_dec_ref_known(v___x_642_, 1);
v___x_644_ = l_Lean_Language_Lean_setOption(v_opts_625_, v_val_643_, v_name_640_, v_val_641_);
return v___x_644_;
}
else
{
lean_object* v___x_645_; lean_object* v___x_647_; 
lean_dec(v___x_642_);
v___x_645_ = l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0(v_opts_625_, v_name_640_, v_val_641_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_645_);
v___x_647_ = v___x_635_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec(v___y_629_);
lean_dec_ref(v_arg_626_);
lean_dec_ref(v_opts_625_);
v_a_650_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_632_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_632_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; 
lean_dec(v___y_629_);
lean_dec_ref(v_arg_626_);
lean_dec_ref(v_opts_625_);
v___x_658_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_setConfigOption___closed__1));
v___x_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
return v___x_659_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_setConfigOption___boxed(lean_object* v_opts_665_, lean_object* v_arg_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_opts_665_, v_arg_666_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(lean_object* v___x_669_, lean_object* v___x_670_, lean_object* v_arg_671_, lean_object* v_inst_672_, lean_object* v_R_673_, lean_object* v_a_674_, lean_object* v_b_675_, lean_object* v_c_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_669_, v_arg_671_, v_a_674_, v_b_675_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___boxed(lean_object* v___x_678_, lean_object* v___x_679_, lean_object* v_arg_680_, lean_object* v_inst_681_, lean_object* v_R_682_, lean_object* v_a_683_, lean_object* v_b_684_, lean_object* v_c_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(v___x_678_, v___x_679_, v_arg_680_, v_inst_681_, v_R_682_, v_a_683_, v_b_684_, v_c_685_);
lean_dec(v_b_684_);
lean_dec_ref(v_arg_680_);
lean_dec_ref(v___x_679_);
lean_dec(v___x_678_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(lean_object* v_msg_688_){
_start:
{
lean_object* v___f_690_; lean_object* v___x_691_; 
v___f_690_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_691_ = l_IO_eprint___redArg(v___f_690_, v_msg_688_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_691_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
else
{
lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_707_; 
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; 
v_unused_708_ = lean_ctor_get(v___x_691_, 0);
lean_dec(v_unused_708_);
v___x_701_ = v___x_691_;
v_isShared_702_ = v_isSharedCheck_707_;
goto v_resetjp_700_;
}
else
{
lean_dec(v___x_691_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_707_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_703_ = lean_box(0);
if (v_isShared_702_ == 0)
{
lean_ctor_set_tag(v___x_701_, 0);
lean_ctor_set(v___x_701_, 0, v___x_703_);
v___x_705_ = v___x_701_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___boxed(lean_object* v_msg_709_, lean_object* v_a_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(v_msg_709_);
return v_res_711_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_714_; lean_object* v___x_715_; 
v___x_714_ = 1;
v___x_715_ = lean_box_uint32(v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(lean_object* v_x_716_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = lean_apply_1(v_x_716_, lean_box(0));
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_739_; lean_object* v___f_740_; lean_object* v___x_741_; 
v_a_734_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_725_, 1);
v___x_739_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___f_740_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_741_ = l_IO_eprint___redArg(v___f_740_, v___x_739_);
lean_dec_ref(v___x_741_);
goto v___jp_735_;
v___jp_735_:
{
lean_object* v___x_736_; lean_object* v___f_737_; lean_object* v___x_738_; 
v___x_736_ = lean_io_error_to_string(v_a_734_);
v___f_737_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_738_ = l_IO_eprint___redArg(v___f_737_, v___x_736_);
lean_dec_ref(v___x_738_);
goto v___jp_721_;
}
}
v___jp_718_:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
return v___x_720_;
}
v___jp_721_:
{
lean_object* v___x_722_; lean_object* v___f_723_; lean_object* v___x_724_; 
v___x_722_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___f_723_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_724_ = l_IO_eprint___redArg(v___f_723_, v___x_722_);
lean_dec_ref(v___x_724_);
goto v___jp_718_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed(lean_object* v_x_742_, lean_object* v_a_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(v_x_742_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(lean_object* v_00_u03b1_745_, lean_object* v_x_746_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = lean_apply_1(v_x_746_, lean_box(0));
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_755_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_755_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_769_; lean_object* v___f_770_; lean_object* v___x_771_; 
v_a_764_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_755_, 1);
v___x_769_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___f_770_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_771_ = l_IO_eprint___redArg(v___f_770_, v___x_769_);
lean_dec_ref(v___x_771_);
goto v___jp_765_;
v___jp_765_:
{
lean_object* v___x_766_; lean_object* v___f_767_; lean_object* v___x_768_; 
v___x_766_ = lean_io_error_to_string(v_a_764_);
v___f_767_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_768_ = l_IO_eprint___redArg(v___f_767_, v___x_766_);
lean_dec_ref(v___x_768_);
goto v___jp_751_;
}
}
v___jp_748_:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
return v___x_750_;
}
v___jp_751_:
{
lean_object* v___x_752_; lean_object* v___f_753_; lean_object* v___x_754_; 
v___x_752_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___f_753_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_754_ = l_IO_eprint___redArg(v___f_753_, v___x_752_);
lean_dec_ref(v___x_754_);
goto v___jp_748_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___boxed(lean_object* v_00_u03b1_772_, lean_object* v_x_773_, lean_object* v_a_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(v_00_u03b1_772_, v_x_773_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(lean_object* v_opt_778_){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___f_787_; lean_object* v___x_788_; 
v___x_783_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__0));
v___x_784_ = lean_string_append(v___x_783_, v_opt_778_);
v___x_785_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
v___x_786_ = lean_string_append(v___x_784_, v___x_785_);
v___f_787_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_788_ = l_IO_eprint___redArg(v___f_787_, v___x_786_);
lean_dec_ref(v___x_788_);
goto v___jp_780_;
v___jp_780_:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
return v___x_782_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___boxed(lean_object* v_opt_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(v_opt_789_);
lean_dec_ref(v_opt_789_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(lean_object* v_opt_794_){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___f_803_; lean_object* v___x_804_; 
v___x_799_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__0));
v___x_800_ = lean_string_append(v___x_799_, v_opt_794_);
v___x_801_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__1));
v___x_802_ = lean_string_append(v___x_800_, v___x_801_);
v___f_803_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_804_ = l_IO_eprint___redArg(v___f_803_, v___x_802_);
lean_dec_ref(v___x_804_);
goto v___jp_796_;
v___jp_796_:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
return v___x_798_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___boxed(lean_object* v_opt_805_, lean_object* v_a_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(v_opt_805_);
lean_dec_ref(v_opt_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(lean_object* v_s_808_){
_start:
{
lean_object* v___x_810_; lean_object* v_putStr_811_; lean_object* v___x_812_; 
v___x_810_ = lean_get_stderr();
v_putStr_811_ = lean_ctor_get(v___x_810_, 4);
lean_inc_ref(v_putStr_811_);
lean_dec_ref(v___x_810_);
v___x_812_ = lean_apply_2(v_putStr_811_, v_s_808_, lean_box(0));
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0___boxed(lean_object* v_s_813_, lean_object* v_a_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v_s_813_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(lean_object* v_s_816_){
_start:
{
lean_object* v___x_818_; lean_object* v_putStr_819_; lean_object* v___x_820_; 
v___x_818_ = lean_get_stdout();
v_putStr_819_ = lean_ctor_get(v___x_818_, 4);
lean_inc_ref(v_putStr_819_);
lean_dec_ref(v___x_818_);
v___x_820_ = lean_apply_2(v_putStr_819_, v_s_816_, lean_box(0));
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5___boxed(lean_object* v_s_821_, lean_object* v_a_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v_s_821_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(lean_object* v_s_824_){
_start:
{
uint32_t v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_826_ = 10;
v___x_827_ = lean_string_push(v_s_824_, v___x_826_);
v___x_828_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3___boxed(lean_object* v_s_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v_s_829_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(lean_object* v_o_832_, lean_object* v_k_833_, uint8_t v_v_834_){
_start:
{
lean_object* v_map_835_; uint8_t v_hasTrace_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_850_; 
v_map_835_ = lean_ctor_get(v_o_832_, 0);
v_hasTrace_836_ = lean_ctor_get_uint8(v_o_832_, sizeof(void*)*1);
v_isSharedCheck_850_ = !lean_is_exclusive(v_o_832_);
if (v_isSharedCheck_850_ == 0)
{
v___x_838_ = v_o_832_;
v_isShared_839_ = v_isSharedCheck_850_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_map_835_);
lean_dec(v_o_832_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_850_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_840_, 0, v_v_834_);
lean_inc(v_k_833_);
v___x_841_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_833_, v___x_840_, v_map_835_);
if (v_hasTrace_836_ == 0)
{
lean_object* v___x_842_; uint8_t v___x_843_; lean_object* v___x_845_; 
v___x_842_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_843_ = l_Lean_Name_isPrefixOf(v___x_842_, v_k_833_);
lean_dec(v_k_833_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_841_);
v___x_845_ = v___x_838_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_841_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_ctor_set_uint8(v___x_845_, sizeof(void*)*1, v___x_843_);
return v___x_845_;
}
}
else
{
lean_object* v___x_848_; 
lean_dec(v_k_833_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_841_);
v___x_848_ = v___x_838_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_841_);
lean_ctor_set_uint8(v_reuseFailAlloc_849_, sizeof(void*)*1, v_hasTrace_836_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1___boxed(lean_object* v_o_851_, lean_object* v_k_852_, lean_object* v_v_853_){
_start:
{
uint8_t v_v_boxed_854_; lean_object* v_res_855_; 
v_v_boxed_854_ = lean_unbox(v_v_853_);
v_res_855_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(v_o_851_, v_k_852_, v_v_boxed_854_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(lean_object* v_opts_856_, lean_object* v_opt_857_, uint8_t v_val_858_){
_start:
{
lean_object* v_name_859_; lean_object* v___x_860_; 
v_name_859_ = lean_ctor_get(v_opt_857_, 0);
lean_inc(v_name_859_);
lean_dec_ref(v_opt_857_);
v___x_860_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(v_opts_856_, v_name_859_, v_val_858_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1___boxed(lean_object* v_opts_861_, lean_object* v_opt_862_, lean_object* v_val_863_){
_start:
{
uint8_t v_val_boxed_864_; lean_object* v_res_865_; 
v_val_boxed_864_ = lean_unbox(v_val_863_);
v_res_865_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_opts_861_, v_opt_862_, v_val_boxed_864_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__3(lean_object* v_o_866_, lean_object* v_k_867_, lean_object* v_v_868_){
_start:
{
lean_object* v_map_869_; uint8_t v_hasTrace_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_884_; 
v_map_869_ = lean_ctor_get(v_o_866_, 0);
v_hasTrace_870_ = lean_ctor_get_uint8(v_o_866_, sizeof(void*)*1);
v_isSharedCheck_884_ = !lean_is_exclusive(v_o_866_);
if (v_isSharedCheck_884_ == 0)
{
v___x_872_ = v_o_866_;
v_isShared_873_ = v_isSharedCheck_884_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_map_869_);
lean_dec(v_o_866_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_884_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_874_, 0, v_v_868_);
lean_inc(v_k_867_);
v___x_875_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_867_, v___x_874_, v_map_869_);
if (v_hasTrace_870_ == 0)
{
lean_object* v___x_876_; uint8_t v___x_877_; lean_object* v___x_879_; 
v___x_876_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_877_ = l_Lean_Name_isPrefixOf(v___x_876_, v_k_867_);
lean_dec(v_k_867_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_875_);
v___x_879_ = v___x_872_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_875_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_ctor_set_uint8(v___x_879_, sizeof(void*)*1, v___x_877_);
return v___x_879_;
}
}
else
{
lean_object* v___x_882_; 
lean_dec(v_k_867_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_875_);
v___x_882_ = v___x_872_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_875_);
lean_ctor_set_uint8(v_reuseFailAlloc_883_, sizeof(void*)*1, v_hasTrace_870_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(lean_object* v_opts_885_, lean_object* v_opt_886_, lean_object* v_val_887_){
_start:
{
lean_object* v_name_888_; lean_object* v___x_889_; 
v_name_888_ = lean_ctor_get(v_opt_886_, 0);
lean_inc(v_name_888_);
lean_dec_ref(v_opt_886_);
v___x_889_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__3(v_opts_885_, v_name_888_, v_val_887_);
return v___x_889_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28(void){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_918_ = l_System_Platform_numBits;
v___x_919_ = lean_unsigned_to_nat(2u);
v___x_920_ = lean_nat_pow(v___x_919_, v___x_918_);
return v___x_920_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1(void){
_start:
{
uint32_t v___x_930_; lean_object* v___x_931_; 
v___x_930_ = 0;
v___x_931_ = lean_box_uint32(v___x_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* lean_shell_options_process(lean_object* v_opts_932_, uint32_t v_opt_933_, lean_object* v_optArg_x3f_934_){
_start:
{
lean_object* v___y_1048_; lean_object* v___y_1094_; uint32_t v___x_1154_; uint8_t v___x_1155_; 
v___x_1154_ = 101;
v___x_1155_ = lean_uint32_dec_eq(v_opt_933_, v___x_1154_);
if (v___x_1155_ == 0)
{
uint32_t v___x_1156_; uint8_t v___x_1157_; 
v___x_1156_ = 106;
v___x_1157_ = lean_uint32_dec_eq(v_opt_933_, v___x_1156_);
if (v___x_1157_ == 0)
{
uint32_t v___x_1158_; uint8_t v___x_1159_; 
v___x_1158_ = 118;
v___x_1159_ = lean_uint32_dec_eq(v_opt_933_, v___x_1158_);
if (v___x_1159_ == 0)
{
uint32_t v___x_1160_; uint8_t v___x_1161_; 
v___x_1160_ = 86;
v___x_1161_ = lean_uint32_dec_eq(v_opt_933_, v___x_1160_);
if (v___x_1161_ == 0)
{
uint32_t v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = 103;
v___x_1163_ = lean_uint32_dec_eq(v_opt_933_, v___x_1162_);
if (v___x_1163_ == 0)
{
uint32_t v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = 104;
v___x_1165_ = lean_uint32_dec_eq(v_opt_933_, v___x_1164_);
if (v___x_1165_ == 0)
{
uint32_t v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = 102;
v___x_1167_ = lean_uint32_dec_eq(v_opt_933_, v___x_1166_);
if (v___x_1167_ == 0)
{
uint32_t v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = 99;
v___x_1169_ = lean_uint32_dec_eq(v_opt_933_, v___x_1168_);
if (v___x_1169_ == 0)
{
uint32_t v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = 98;
v___x_1171_ = lean_uint32_dec_eq(v_opt_933_, v___x_1170_);
if (v___x_1171_ == 0)
{
uint32_t v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = 115;
v___x_1173_ = lean_uint32_dec_eq(v_opt_933_, v___x_1172_);
if (v___x_1173_ == 0)
{
uint32_t v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = 73;
v___x_1175_ = lean_uint32_dec_eq(v_opt_933_, v___x_1174_);
if (v___x_1175_ == 0)
{
uint32_t v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = 114;
v___x_1177_ = lean_uint32_dec_eq(v_opt_933_, v___x_1176_);
if (v___x_1177_ == 0)
{
uint32_t v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = 111;
v___x_1179_ = lean_uint32_dec_eq(v_opt_933_, v___x_1178_);
if (v___x_1179_ == 0)
{
uint32_t v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = 105;
v___x_1181_ = lean_uint32_dec_eq(v_opt_933_, v___x_1180_);
if (v___x_1181_ == 0)
{
uint32_t v___x_1182_; uint8_t v___x_1183_; 
v___x_1182_ = 82;
v___x_1183_ = lean_uint32_dec_eq(v_opt_933_, v___x_1182_);
if (v___x_1183_ == 0)
{
uint32_t v___x_1184_; uint8_t v___x_1185_; 
v___x_1184_ = 77;
v___x_1185_ = lean_uint32_dec_eq(v_opt_933_, v___x_1184_);
if (v___x_1185_ == 0)
{
uint32_t v___x_1186_; uint8_t v___x_1187_; 
v___x_1186_ = 84;
v___x_1187_ = lean_uint32_dec_eq(v_opt_933_, v___x_1186_);
if (v___x_1187_ == 0)
{
uint32_t v___x_1188_; uint8_t v___x_1189_; 
v___x_1188_ = 116;
v___x_1189_ = lean_uint32_dec_eq(v_opt_933_, v___x_1188_);
if (v___x_1189_ == 0)
{
uint32_t v___x_1190_; uint8_t v___x_1191_; 
v___x_1190_ = 113;
v___x_1191_ = lean_uint32_dec_eq(v_opt_933_, v___x_1190_);
if (v___x_1191_ == 0)
{
uint32_t v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = 100;
v___x_1193_ = lean_uint32_dec_eq(v_opt_933_, v___x_1192_);
if (v___x_1193_ == 0)
{
uint32_t v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = 79;
v___x_1195_ = lean_uint32_dec_eq(v_opt_933_, v___x_1194_);
if (v___x_1195_ == 0)
{
uint32_t v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = 78;
v___x_1197_ = lean_uint32_dec_eq(v_opt_933_, v___x_1196_);
if (v___x_1197_ == 0)
{
uint32_t v___x_1198_; uint8_t v___x_1199_; 
v___x_1198_ = 74;
v___x_1199_ = lean_uint32_dec_eq(v_opt_933_, v___x_1198_);
if (v___x_1199_ == 0)
{
uint32_t v___x_1200_; uint8_t v___x_1201_; 
v___x_1200_ = 97;
v___x_1201_ = lean_uint32_dec_eq(v_opt_933_, v___x_1200_);
if (v___x_1201_ == 0)
{
uint32_t v___x_1202_; uint8_t v___x_1203_; 
v___x_1202_ = 120;
v___x_1203_ = lean_uint32_dec_eq(v_opt_933_, v___x_1202_);
if (v___x_1203_ == 0)
{
uint32_t v___x_1204_; uint8_t v___x_1205_; 
v___x_1204_ = 76;
v___x_1205_ = lean_uint32_dec_eq(v_opt_933_, v___x_1204_);
if (v___x_1205_ == 0)
{
uint32_t v___x_1206_; uint8_t v___x_1207_; 
v___x_1206_ = 68;
v___x_1207_ = lean_uint32_dec_eq(v_opt_933_, v___x_1206_);
if (v___x_1207_ == 0)
{
uint32_t v___x_1208_; uint8_t v___x_1209_; 
v___x_1208_ = 83;
v___x_1209_ = lean_uint32_dec_eq(v_opt_933_, v___x_1208_);
if (v___x_1209_ == 0)
{
uint32_t v___x_1210_; uint8_t v___x_1211_; 
v___x_1210_ = 87;
v___x_1211_ = lean_uint32_dec_eq(v_opt_933_, v___x_1210_);
if (v___x_1211_ == 0)
{
uint32_t v___x_1212_; uint8_t v___x_1213_; 
v___x_1212_ = 80;
v___x_1213_ = lean_uint32_dec_eq(v_opt_933_, v___x_1212_);
if (v___x_1213_ == 0)
{
uint32_t v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = 66;
v___x_1215_ = lean_uint32_dec_eq(v_opt_933_, v___x_1214_);
if (v___x_1215_ == 0)
{
uint32_t v___x_1216_; uint8_t v___x_1217_; 
v___x_1216_ = 112;
v___x_1217_ = lean_uint32_dec_eq(v_opt_933_, v___x_1216_);
if (v___x_1217_ == 0)
{
uint32_t v___x_1218_; uint8_t v___x_1219_; 
v___x_1218_ = 108;
v___x_1219_ = lean_uint32_dec_eq(v_opt_933_, v___x_1218_);
if (v___x_1219_ == 0)
{
uint32_t v___x_1220_; uint8_t v___x_1221_; 
v___x_1220_ = 117;
v___x_1221_ = lean_uint32_dec_eq(v_opt_933_, v___x_1220_);
if (v___x_1221_ == 0)
{
uint32_t v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = 69;
v___x_1223_ = lean_uint32_dec_eq(v_opt_933_, v___x_1222_);
if (v___x_1223_ == 0)
{
uint32_t v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = 89;
v___x_1225_ = lean_uint32_dec_eq(v_opt_933_, v___x_1224_);
if (v___x_1225_ == 0)
{
uint32_t v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = 90;
v___x_1227_ = lean_uint32_dec_eq(v_opt_933_, v___x_1226_);
if (v___x_1227_ == 0)
{
uint32_t v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = 72;
v___x_1229_ = lean_uint32_dec_eq(v_opt_933_, v___x_1228_);
if (v___x_1229_ == 0)
{
lean_dec(v_optArg_x3f_934_);
lean_dec_ref(v_opts_932_);
goto v___jp_1066_;
}
else
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1));
v___x_1231_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1230_, v_optArg_x3f_934_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1272_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1234_ = v___x_1231_;
v_isShared_1235_ = v_isSharedCheck_1272_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1231_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1272_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v_leanOpts_1236_; lean_object* v_forwardedArgs_1237_; uint8_t v_component_1238_; uint8_t v_printPrefix_1239_; uint8_t v_printLibDir_1240_; uint8_t v_useStdin_1241_; uint8_t v_onlyDeps_1242_; uint8_t v_onlySrcDeps_1243_; uint8_t v_depsJson_1244_; lean_object* v_opts_1245_; uint32_t v_trustLevel_1246_; uint32_t v_numThreads_1247_; lean_object* v_rootDir_x3f_1248_; lean_object* v_setupFileName_x3f_1249_; lean_object* v_oleanFileName_x3f_1250_; lean_object* v_ileanFileName_x3f_1251_; lean_object* v_cFileName_x3f_1252_; lean_object* v_bcFileName_x3f_1253_; uint8_t v_jsonOutput_1254_; lean_object* v_errorOnKinds_1255_; uint8_t v_printStats_1256_; uint8_t v_run_1257_; lean_object* v_incrSaveFileName_x3f_1258_; lean_object* v_incrLoadFileName_x3f_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1270_; 
v_leanOpts_1236_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_1237_ = lean_ctor_get(v_opts_932_, 1);
v_component_1238_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_1239_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_1240_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_1241_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_1242_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1243_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_1244_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_1245_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_1246_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_1247_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1248_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_1249_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_1250_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_1251_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_1252_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_1253_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_1254_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_1255_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_1256_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_1257_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1258_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_1259_ = lean_ctor_get(v_opts_932_, 11);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_1270_ == 0)
{
lean_object* v_unused_1271_; 
v_unused_1271_ = lean_ctor_get(v_opts_932_, 12);
lean_dec(v_unused_1271_);
v___x_1261_ = v_opts_932_;
v_isShared_1262_ = v_isSharedCheck_1270_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_incrLoadFileName_x3f_1259_);
lean_inc(v_incrSaveFileName_x3f_1258_);
lean_inc(v_errorOnKinds_1255_);
lean_inc(v_bcFileName_x3f_1253_);
lean_inc(v_cFileName_x3f_1252_);
lean_inc(v_ileanFileName_x3f_1251_);
lean_inc(v_oleanFileName_x3f_1250_);
lean_inc(v_setupFileName_x3f_1249_);
lean_inc(v_rootDir_x3f_1248_);
lean_inc(v_opts_1245_);
lean_inc(v_forwardedArgs_1237_);
lean_inc(v_leanOpts_1236_);
lean_dec(v_opts_932_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1270_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; lean_object* v___x_1265_; 
v___x_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1263_, 0, v_a_1232_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 12, v___x_1263_);
v___x_1265_ = v___x_1261_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_leanOpts_1236_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_forwardedArgs_1237_);
lean_ctor_set(v_reuseFailAlloc_1269_, 2, v_opts_1245_);
lean_ctor_set(v_reuseFailAlloc_1269_, 3, v_rootDir_x3f_1248_);
lean_ctor_set(v_reuseFailAlloc_1269_, 4, v_setupFileName_x3f_1249_);
lean_ctor_set(v_reuseFailAlloc_1269_, 5, v_oleanFileName_x3f_1250_);
lean_ctor_set(v_reuseFailAlloc_1269_, 6, v_ileanFileName_x3f_1251_);
lean_ctor_set(v_reuseFailAlloc_1269_, 7, v_cFileName_x3f_1252_);
lean_ctor_set(v_reuseFailAlloc_1269_, 8, v_bcFileName_x3f_1253_);
lean_ctor_set(v_reuseFailAlloc_1269_, 9, v_errorOnKinds_1255_);
lean_ctor_set(v_reuseFailAlloc_1269_, 10, v_incrSaveFileName_x3f_1258_);
lean_ctor_set(v_reuseFailAlloc_1269_, 11, v_incrLoadFileName_x3f_1259_);
lean_ctor_set(v_reuseFailAlloc_1269_, 12, v___x_1263_);
lean_ctor_set_uint8(v_reuseFailAlloc_1269_, sizeof(void*)*13 + 8, v_component_1238_);
lean_ctor_set_uint8(v_reuseFailAlloc_1269_, sizeof(void*)*13 + 9, v_printPrefix_1239_);
lean_ctor_set_uint8(v_reuseFailAlloc_1269_, sizeof(void*)*13 + 10, v_printLibDir_1240_);
lean_ctor_set_uint8(v_reuseFailAlloc_1269_, sizeof(void*)*13 + 11, v_useStdin_1241_);
lean_ctor_set_uint8(v_reuseFailAlloc_1269_, sizeof(void*)*13 + 12, v_onlyDeps_1242_);
lean_ctor_set_uint8(v_reuseFailAlloc_1269_, sizeof(void*)*13 + 13, v_onlySrcDeps_1243_);
lean_ctor_set_uint8(v_reuseFailAlloc_1269_, sizeof(void*)*13 + 14, v_depsJson_1244_);
lean_ctor_set_uint32(v_reuseFailAlloc_1269_, sizeof(void*)*13, v_trustLevel_1246_);
lean_ctor_set_uint32(v_reuseFailAlloc_1269_, sizeof(void*)*13 + 4, v_numThreads_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1269_, sizeof(void*)*13 + 15, v_jsonOutput_1254_);
lean_ctor_set_uint8(v_reuseFailAlloc_1269_, sizeof(void*)*13 + 16, v_printStats_1256_);
lean_ctor_set_uint8(v_reuseFailAlloc_1269_, sizeof(void*)*13 + 17, v_run_1257_);
v___x_1265_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
lean_object* v___x_1267_; 
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v___x_1265_);
v___x_1267_ = v___x_1234_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
lean_dec_ref(v_opts_932_);
v_a_1273_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1273_);
lean_dec_ref_known(v___x_1231_, 1);
v___x_1277_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1278_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1277_);
lean_dec_ref(v___x_1278_);
goto v___jp_1274_;
v___jp_1274_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = lean_io_error_to_string(v_a_1273_);
v___x_1276_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1275_);
lean_dec_ref(v___x_1276_);
goto v___jp_1038_;
}
}
}
}
else
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2));
v___x_1280_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1279_, v_optArg_x3f_934_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1321_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1321_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1321_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v_leanOpts_1285_; lean_object* v_forwardedArgs_1286_; uint8_t v_component_1287_; uint8_t v_printPrefix_1288_; uint8_t v_printLibDir_1289_; uint8_t v_useStdin_1290_; uint8_t v_onlyDeps_1291_; uint8_t v_onlySrcDeps_1292_; uint8_t v_depsJson_1293_; lean_object* v_opts_1294_; uint32_t v_trustLevel_1295_; uint32_t v_numThreads_1296_; lean_object* v_rootDir_x3f_1297_; lean_object* v_setupFileName_x3f_1298_; lean_object* v_oleanFileName_x3f_1299_; lean_object* v_ileanFileName_x3f_1300_; lean_object* v_cFileName_x3f_1301_; lean_object* v_bcFileName_x3f_1302_; uint8_t v_jsonOutput_1303_; lean_object* v_errorOnKinds_1304_; uint8_t v_printStats_1305_; uint8_t v_run_1306_; lean_object* v_incrSaveFileName_x3f_1307_; lean_object* v_incrHeaderSaveFileName_x3f_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1319_; 
v_leanOpts_1285_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_1286_ = lean_ctor_get(v_opts_932_, 1);
v_component_1287_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_1288_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_1289_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_1290_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_1291_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1292_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_1293_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_1294_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_1295_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_1296_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1297_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_1298_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_1299_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_1300_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_1301_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_1302_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_1303_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_1304_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_1305_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_1306_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1307_ = lean_ctor_get(v_opts_932_, 10);
v_incrHeaderSaveFileName_x3f_1308_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_1319_ == 0)
{
lean_object* v_unused_1320_; 
v_unused_1320_ = lean_ctor_get(v_opts_932_, 11);
lean_dec(v_unused_1320_);
v___x_1310_ = v_opts_932_;
v_isShared_1311_ = v_isSharedCheck_1319_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1308_);
lean_inc(v_incrSaveFileName_x3f_1307_);
lean_inc(v_errorOnKinds_1304_);
lean_inc(v_bcFileName_x3f_1302_);
lean_inc(v_cFileName_x3f_1301_);
lean_inc(v_ileanFileName_x3f_1300_);
lean_inc(v_oleanFileName_x3f_1299_);
lean_inc(v_setupFileName_x3f_1298_);
lean_inc(v_rootDir_x3f_1297_);
lean_inc(v_opts_1294_);
lean_inc(v_forwardedArgs_1286_);
lean_inc(v_leanOpts_1285_);
lean_dec(v_opts_932_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1319_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1312_, 0, v_a_1281_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 11, v___x_1312_);
v___x_1314_ = v___x_1310_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_leanOpts_1285_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_forwardedArgs_1286_);
lean_ctor_set(v_reuseFailAlloc_1318_, 2, v_opts_1294_);
lean_ctor_set(v_reuseFailAlloc_1318_, 3, v_rootDir_x3f_1297_);
lean_ctor_set(v_reuseFailAlloc_1318_, 4, v_setupFileName_x3f_1298_);
lean_ctor_set(v_reuseFailAlloc_1318_, 5, v_oleanFileName_x3f_1299_);
lean_ctor_set(v_reuseFailAlloc_1318_, 6, v_ileanFileName_x3f_1300_);
lean_ctor_set(v_reuseFailAlloc_1318_, 7, v_cFileName_x3f_1301_);
lean_ctor_set(v_reuseFailAlloc_1318_, 8, v_bcFileName_x3f_1302_);
lean_ctor_set(v_reuseFailAlloc_1318_, 9, v_errorOnKinds_1304_);
lean_ctor_set(v_reuseFailAlloc_1318_, 10, v_incrSaveFileName_x3f_1307_);
lean_ctor_set(v_reuseFailAlloc_1318_, 11, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1318_, 12, v_incrHeaderSaveFileName_x3f_1308_);
lean_ctor_set_uint8(v_reuseFailAlloc_1318_, sizeof(void*)*13 + 8, v_component_1287_);
lean_ctor_set_uint8(v_reuseFailAlloc_1318_, sizeof(void*)*13 + 9, v_printPrefix_1288_);
lean_ctor_set_uint8(v_reuseFailAlloc_1318_, sizeof(void*)*13 + 10, v_printLibDir_1289_);
lean_ctor_set_uint8(v_reuseFailAlloc_1318_, sizeof(void*)*13 + 11, v_useStdin_1290_);
lean_ctor_set_uint8(v_reuseFailAlloc_1318_, sizeof(void*)*13 + 12, v_onlyDeps_1291_);
lean_ctor_set_uint8(v_reuseFailAlloc_1318_, sizeof(void*)*13 + 13, v_onlySrcDeps_1292_);
lean_ctor_set_uint8(v_reuseFailAlloc_1318_, sizeof(void*)*13 + 14, v_depsJson_1293_);
lean_ctor_set_uint32(v_reuseFailAlloc_1318_, sizeof(void*)*13, v_trustLevel_1295_);
lean_ctor_set_uint32(v_reuseFailAlloc_1318_, sizeof(void*)*13 + 4, v_numThreads_1296_);
lean_ctor_set_uint8(v_reuseFailAlloc_1318_, sizeof(void*)*13 + 15, v_jsonOutput_1303_);
lean_ctor_set_uint8(v_reuseFailAlloc_1318_, sizeof(void*)*13 + 16, v_printStats_1305_);
lean_ctor_set_uint8(v_reuseFailAlloc_1318_, sizeof(void*)*13 + 17, v_run_1306_);
v___x_1314_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1316_; 
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1314_);
v___x_1316_ = v___x_1283_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
lean_dec_ref(v_opts_932_);
v_a_1322_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1322_);
lean_dec_ref_known(v___x_1280_, 1);
v___x_1326_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1327_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1326_);
lean_dec_ref(v___x_1327_);
goto v___jp_1323_;
v___jp_1323_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = lean_io_error_to_string(v_a_1322_);
v___x_1325_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1324_);
lean_dec_ref(v___x_1325_);
goto v___jp_1072_;
}
}
}
}
else
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3));
v___x_1329_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1328_, v_optArg_x3f_934_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1370_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1332_ = v___x_1329_;
v_isShared_1333_ = v_isSharedCheck_1370_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1370_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v_leanOpts_1334_; lean_object* v_forwardedArgs_1335_; uint8_t v_component_1336_; uint8_t v_printPrefix_1337_; uint8_t v_printLibDir_1338_; uint8_t v_useStdin_1339_; uint8_t v_onlyDeps_1340_; uint8_t v_onlySrcDeps_1341_; uint8_t v_depsJson_1342_; lean_object* v_opts_1343_; uint32_t v_trustLevel_1344_; uint32_t v_numThreads_1345_; lean_object* v_rootDir_x3f_1346_; lean_object* v_setupFileName_x3f_1347_; lean_object* v_oleanFileName_x3f_1348_; lean_object* v_ileanFileName_x3f_1349_; lean_object* v_cFileName_x3f_1350_; lean_object* v_bcFileName_x3f_1351_; uint8_t v_jsonOutput_1352_; lean_object* v_errorOnKinds_1353_; uint8_t v_printStats_1354_; uint8_t v_run_1355_; lean_object* v_incrLoadFileName_x3f_1356_; lean_object* v_incrHeaderSaveFileName_x3f_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1368_; 
v_leanOpts_1334_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_1335_ = lean_ctor_get(v_opts_932_, 1);
v_component_1336_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_1337_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_1338_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_1339_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_1340_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1341_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_1342_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_1343_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_1344_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_1345_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1346_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_1347_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_1348_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_1349_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_1350_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_1351_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_1352_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_1353_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_1354_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_1355_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrLoadFileName_x3f_1356_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_1357_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_1368_ == 0)
{
lean_object* v_unused_1369_; 
v_unused_1369_ = lean_ctor_get(v_opts_932_, 10);
lean_dec(v_unused_1369_);
v___x_1359_ = v_opts_932_;
v_isShared_1360_ = v_isSharedCheck_1368_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1357_);
lean_inc(v_incrLoadFileName_x3f_1356_);
lean_inc(v_errorOnKinds_1353_);
lean_inc(v_bcFileName_x3f_1351_);
lean_inc(v_cFileName_x3f_1350_);
lean_inc(v_ileanFileName_x3f_1349_);
lean_inc(v_oleanFileName_x3f_1348_);
lean_inc(v_setupFileName_x3f_1347_);
lean_inc(v_rootDir_x3f_1346_);
lean_inc(v_opts_1343_);
lean_inc(v_forwardedArgs_1335_);
lean_inc(v_leanOpts_1334_);
lean_dec(v_opts_932_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1368_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; lean_object* v___x_1363_; 
v___x_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1361_, 0, v_a_1330_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 10, v___x_1361_);
v___x_1363_ = v___x_1359_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_leanOpts_1334_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_forwardedArgs_1335_);
lean_ctor_set(v_reuseFailAlloc_1367_, 2, v_opts_1343_);
lean_ctor_set(v_reuseFailAlloc_1367_, 3, v_rootDir_x3f_1346_);
lean_ctor_set(v_reuseFailAlloc_1367_, 4, v_setupFileName_x3f_1347_);
lean_ctor_set(v_reuseFailAlloc_1367_, 5, v_oleanFileName_x3f_1348_);
lean_ctor_set(v_reuseFailAlloc_1367_, 6, v_ileanFileName_x3f_1349_);
lean_ctor_set(v_reuseFailAlloc_1367_, 7, v_cFileName_x3f_1350_);
lean_ctor_set(v_reuseFailAlloc_1367_, 8, v_bcFileName_x3f_1351_);
lean_ctor_set(v_reuseFailAlloc_1367_, 9, v_errorOnKinds_1353_);
lean_ctor_set(v_reuseFailAlloc_1367_, 10, v___x_1361_);
lean_ctor_set(v_reuseFailAlloc_1367_, 11, v_incrLoadFileName_x3f_1356_);
lean_ctor_set(v_reuseFailAlloc_1367_, 12, v_incrHeaderSaveFileName_x3f_1357_);
lean_ctor_set_uint8(v_reuseFailAlloc_1367_, sizeof(void*)*13 + 8, v_component_1336_);
lean_ctor_set_uint8(v_reuseFailAlloc_1367_, sizeof(void*)*13 + 9, v_printPrefix_1337_);
lean_ctor_set_uint8(v_reuseFailAlloc_1367_, sizeof(void*)*13 + 10, v_printLibDir_1338_);
lean_ctor_set_uint8(v_reuseFailAlloc_1367_, sizeof(void*)*13 + 11, v_useStdin_1339_);
lean_ctor_set_uint8(v_reuseFailAlloc_1367_, sizeof(void*)*13 + 12, v_onlyDeps_1340_);
lean_ctor_set_uint8(v_reuseFailAlloc_1367_, sizeof(void*)*13 + 13, v_onlySrcDeps_1341_);
lean_ctor_set_uint8(v_reuseFailAlloc_1367_, sizeof(void*)*13 + 14, v_depsJson_1342_);
lean_ctor_set_uint32(v_reuseFailAlloc_1367_, sizeof(void*)*13, v_trustLevel_1344_);
lean_ctor_set_uint32(v_reuseFailAlloc_1367_, sizeof(void*)*13 + 4, v_numThreads_1345_);
lean_ctor_set_uint8(v_reuseFailAlloc_1367_, sizeof(void*)*13 + 15, v_jsonOutput_1352_);
lean_ctor_set_uint8(v_reuseFailAlloc_1367_, sizeof(void*)*13 + 16, v_printStats_1354_);
lean_ctor_set_uint8(v_reuseFailAlloc_1367_, sizeof(void*)*13 + 17, v_run_1355_);
v___x_1363_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1365_; 
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v___x_1363_);
v___x_1365_ = v___x_1332_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_dec_ref(v_opts_932_);
v_a_1371_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_a_1371_);
lean_dec_ref_known(v___x_1329_, 1);
v___x_1375_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1376_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1375_);
lean_dec_ref(v___x_1376_);
goto v___jp_1372_;
v___jp_1372_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = lean_io_error_to_string(v_a_1371_);
v___x_1374_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1373_);
lean_dec_ref(v___x_1374_);
goto v___jp_1032_;
}
}
}
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4));
v___x_1378_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1377_, v_optArg_x3f_934_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1420_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1381_ = v___x_1378_;
v_isShared_1382_ = v_isSharedCheck_1420_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1378_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1420_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v_leanOpts_1383_; lean_object* v_forwardedArgs_1384_; uint8_t v_component_1385_; uint8_t v_printPrefix_1386_; uint8_t v_printLibDir_1387_; uint8_t v_useStdin_1388_; uint8_t v_onlyDeps_1389_; uint8_t v_onlySrcDeps_1390_; uint8_t v_depsJson_1391_; lean_object* v_opts_1392_; uint32_t v_trustLevel_1393_; uint32_t v_numThreads_1394_; lean_object* v_rootDir_x3f_1395_; lean_object* v_setupFileName_x3f_1396_; lean_object* v_oleanFileName_x3f_1397_; lean_object* v_ileanFileName_x3f_1398_; lean_object* v_cFileName_x3f_1399_; lean_object* v_bcFileName_x3f_1400_; uint8_t v_jsonOutput_1401_; lean_object* v_errorOnKinds_1402_; uint8_t v_printStats_1403_; uint8_t v_run_1404_; lean_object* v_incrSaveFileName_x3f_1405_; lean_object* v_incrLoadFileName_x3f_1406_; lean_object* v_incrHeaderSaveFileName_x3f_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1419_; 
v_leanOpts_1383_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_1384_ = lean_ctor_get(v_opts_932_, 1);
v_component_1385_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_1386_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_1387_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_1388_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_1389_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1390_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_1391_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_1392_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_1393_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_1394_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1395_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_1396_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_1397_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_1398_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_1399_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_1400_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_1401_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_1402_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_1403_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_1404_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1405_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_1406_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_1407_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_1419_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1409_ = v_opts_932_;
v_isShared_1410_ = v_isSharedCheck_1419_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1407_);
lean_inc(v_incrLoadFileName_x3f_1406_);
lean_inc(v_incrSaveFileName_x3f_1405_);
lean_inc(v_errorOnKinds_1402_);
lean_inc(v_bcFileName_x3f_1400_);
lean_inc(v_cFileName_x3f_1399_);
lean_inc(v_ileanFileName_x3f_1398_);
lean_inc(v_oleanFileName_x3f_1397_);
lean_inc(v_setupFileName_x3f_1396_);
lean_inc(v_rootDir_x3f_1395_);
lean_inc(v_opts_1392_);
lean_inc(v_forwardedArgs_1384_);
lean_inc(v_leanOpts_1383_);
lean_dec(v_opts_932_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1419_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1411_ = l_String_toName(v_a_1379_);
v___x_1412_ = lean_array_push(v_errorOnKinds_1402_, v___x_1411_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 9, v___x_1412_);
v___x_1414_ = v___x_1409_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_leanOpts_1383_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_forwardedArgs_1384_);
lean_ctor_set(v_reuseFailAlloc_1418_, 2, v_opts_1392_);
lean_ctor_set(v_reuseFailAlloc_1418_, 3, v_rootDir_x3f_1395_);
lean_ctor_set(v_reuseFailAlloc_1418_, 4, v_setupFileName_x3f_1396_);
lean_ctor_set(v_reuseFailAlloc_1418_, 5, v_oleanFileName_x3f_1397_);
lean_ctor_set(v_reuseFailAlloc_1418_, 6, v_ileanFileName_x3f_1398_);
lean_ctor_set(v_reuseFailAlloc_1418_, 7, v_cFileName_x3f_1399_);
lean_ctor_set(v_reuseFailAlloc_1418_, 8, v_bcFileName_x3f_1400_);
lean_ctor_set(v_reuseFailAlloc_1418_, 9, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1418_, 10, v_incrSaveFileName_x3f_1405_);
lean_ctor_set(v_reuseFailAlloc_1418_, 11, v_incrLoadFileName_x3f_1406_);
lean_ctor_set(v_reuseFailAlloc_1418_, 12, v_incrHeaderSaveFileName_x3f_1407_);
lean_ctor_set_uint8(v_reuseFailAlloc_1418_, sizeof(void*)*13 + 8, v_component_1385_);
lean_ctor_set_uint8(v_reuseFailAlloc_1418_, sizeof(void*)*13 + 9, v_printPrefix_1386_);
lean_ctor_set_uint8(v_reuseFailAlloc_1418_, sizeof(void*)*13 + 10, v_printLibDir_1387_);
lean_ctor_set_uint8(v_reuseFailAlloc_1418_, sizeof(void*)*13 + 11, v_useStdin_1388_);
lean_ctor_set_uint8(v_reuseFailAlloc_1418_, sizeof(void*)*13 + 12, v_onlyDeps_1389_);
lean_ctor_set_uint8(v_reuseFailAlloc_1418_, sizeof(void*)*13 + 13, v_onlySrcDeps_1390_);
lean_ctor_set_uint8(v_reuseFailAlloc_1418_, sizeof(void*)*13 + 14, v_depsJson_1391_);
lean_ctor_set_uint32(v_reuseFailAlloc_1418_, sizeof(void*)*13, v_trustLevel_1393_);
lean_ctor_set_uint32(v_reuseFailAlloc_1418_, sizeof(void*)*13 + 4, v_numThreads_1394_);
lean_ctor_set_uint8(v_reuseFailAlloc_1418_, sizeof(void*)*13 + 15, v_jsonOutput_1401_);
lean_ctor_set_uint8(v_reuseFailAlloc_1418_, sizeof(void*)*13 + 16, v_printStats_1403_);
lean_ctor_set_uint8(v_reuseFailAlloc_1418_, sizeof(void*)*13 + 17, v_run_1404_);
v___x_1414_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1416_; 
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v___x_1414_);
v___x_1416_ = v___x_1381_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_dec_ref(v_opts_932_);
v_a_1421_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1378_, 1);
v___x_1425_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1426_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1425_);
lean_dec_ref(v___x_1426_);
goto v___jp_1422_;
v___jp_1422_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = lean_io_error_to_string(v_a_1421_);
v___x_1424_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1423_);
lean_dec_ref(v___x_1424_);
goto v___jp_1078_;
}
}
}
}
else
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5));
v___x_1428_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1427_, v_optArg_x3f_934_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1469_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1469_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1469_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v_leanOpts_1433_; lean_object* v_forwardedArgs_1434_; uint8_t v_component_1435_; uint8_t v_printPrefix_1436_; uint8_t v_printLibDir_1437_; uint8_t v_useStdin_1438_; uint8_t v_onlyDeps_1439_; uint8_t v_onlySrcDeps_1440_; uint8_t v_depsJson_1441_; lean_object* v_opts_1442_; uint32_t v_trustLevel_1443_; uint32_t v_numThreads_1444_; lean_object* v_rootDir_x3f_1445_; lean_object* v_oleanFileName_x3f_1446_; lean_object* v_ileanFileName_x3f_1447_; lean_object* v_cFileName_x3f_1448_; lean_object* v_bcFileName_x3f_1449_; uint8_t v_jsonOutput_1450_; lean_object* v_errorOnKinds_1451_; uint8_t v_printStats_1452_; uint8_t v_run_1453_; lean_object* v_incrSaveFileName_x3f_1454_; lean_object* v_incrLoadFileName_x3f_1455_; lean_object* v_incrHeaderSaveFileName_x3f_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1467_; 
v_leanOpts_1433_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_1434_ = lean_ctor_get(v_opts_932_, 1);
v_component_1435_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_1436_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_1437_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_1438_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_1439_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1440_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_1441_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_1442_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_1443_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_1444_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1445_ = lean_ctor_get(v_opts_932_, 3);
v_oleanFileName_x3f_1446_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_1447_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_1448_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_1449_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_1450_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_1451_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_1452_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_1453_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1454_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_1455_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_1456_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_1467_ == 0)
{
lean_object* v_unused_1468_; 
v_unused_1468_ = lean_ctor_get(v_opts_932_, 4);
lean_dec(v_unused_1468_);
v___x_1458_ = v_opts_932_;
v_isShared_1459_ = v_isSharedCheck_1467_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1456_);
lean_inc(v_incrLoadFileName_x3f_1455_);
lean_inc(v_incrSaveFileName_x3f_1454_);
lean_inc(v_errorOnKinds_1451_);
lean_inc(v_bcFileName_x3f_1449_);
lean_inc(v_cFileName_x3f_1448_);
lean_inc(v_ileanFileName_x3f_1447_);
lean_inc(v_oleanFileName_x3f_1446_);
lean_inc(v_rootDir_x3f_1445_);
lean_inc(v_opts_1442_);
lean_inc(v_forwardedArgs_1434_);
lean_inc(v_leanOpts_1433_);
lean_dec(v_opts_932_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1467_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1460_, 0, v_a_1429_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 4, v___x_1460_);
v___x_1462_ = v___x_1458_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_leanOpts_1433_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_forwardedArgs_1434_);
lean_ctor_set(v_reuseFailAlloc_1466_, 2, v_opts_1442_);
lean_ctor_set(v_reuseFailAlloc_1466_, 3, v_rootDir_x3f_1445_);
lean_ctor_set(v_reuseFailAlloc_1466_, 4, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1466_, 5, v_oleanFileName_x3f_1446_);
lean_ctor_set(v_reuseFailAlloc_1466_, 6, v_ileanFileName_x3f_1447_);
lean_ctor_set(v_reuseFailAlloc_1466_, 7, v_cFileName_x3f_1448_);
lean_ctor_set(v_reuseFailAlloc_1466_, 8, v_bcFileName_x3f_1449_);
lean_ctor_set(v_reuseFailAlloc_1466_, 9, v_errorOnKinds_1451_);
lean_ctor_set(v_reuseFailAlloc_1466_, 10, v_incrSaveFileName_x3f_1454_);
lean_ctor_set(v_reuseFailAlloc_1466_, 11, v_incrLoadFileName_x3f_1455_);
lean_ctor_set(v_reuseFailAlloc_1466_, 12, v_incrHeaderSaveFileName_x3f_1456_);
lean_ctor_set_uint8(v_reuseFailAlloc_1466_, sizeof(void*)*13 + 8, v_component_1435_);
lean_ctor_set_uint8(v_reuseFailAlloc_1466_, sizeof(void*)*13 + 9, v_printPrefix_1436_);
lean_ctor_set_uint8(v_reuseFailAlloc_1466_, sizeof(void*)*13 + 10, v_printLibDir_1437_);
lean_ctor_set_uint8(v_reuseFailAlloc_1466_, sizeof(void*)*13 + 11, v_useStdin_1438_);
lean_ctor_set_uint8(v_reuseFailAlloc_1466_, sizeof(void*)*13 + 12, v_onlyDeps_1439_);
lean_ctor_set_uint8(v_reuseFailAlloc_1466_, sizeof(void*)*13 + 13, v_onlySrcDeps_1440_);
lean_ctor_set_uint8(v_reuseFailAlloc_1466_, sizeof(void*)*13 + 14, v_depsJson_1441_);
lean_ctor_set_uint32(v_reuseFailAlloc_1466_, sizeof(void*)*13, v_trustLevel_1443_);
lean_ctor_set_uint32(v_reuseFailAlloc_1466_, sizeof(void*)*13 + 4, v_numThreads_1444_);
lean_ctor_set_uint8(v_reuseFailAlloc_1466_, sizeof(void*)*13 + 15, v_jsonOutput_1450_);
lean_ctor_set_uint8(v_reuseFailAlloc_1466_, sizeof(void*)*13 + 16, v_printStats_1452_);
lean_ctor_set_uint8(v_reuseFailAlloc_1466_, sizeof(void*)*13 + 17, v_run_1453_);
v___x_1462_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1464_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1462_);
v___x_1464_ = v___x_1431_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_dec_ref(v_opts_932_);
v_a_1470_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1470_);
lean_dec_ref_known(v___x_1428_, 1);
v___x_1474_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1475_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1474_);
lean_dec_ref(v___x_1475_);
goto v___jp_1471_;
v___jp_1471_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = lean_io_error_to_string(v_a_1470_);
v___x_1473_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1472_);
lean_dec_ref(v___x_1473_);
goto v___jp_1026_;
}
}
}
}
else
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6));
v___x_1477_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1476_, v_optArg_x3f_934_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1479_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc_n(v_a_1478_, 2);
lean_dec_ref_known(v___x_1477_, 1);
v___x_1479_ = lean_load_dynlib(v_a_1478_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1521_; 
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1521_ == 0)
{
lean_object* v_unused_1522_; 
v_unused_1522_ = lean_ctor_get(v___x_1479_, 0);
lean_dec(v_unused_1522_);
v___x_1481_ = v___x_1479_;
v_isShared_1482_ = v_isSharedCheck_1521_;
goto v_resetjp_1480_;
}
else
{
lean_dec(v___x_1479_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1521_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v_leanOpts_1483_; lean_object* v_forwardedArgs_1484_; uint8_t v_component_1485_; uint8_t v_printPrefix_1486_; uint8_t v_printLibDir_1487_; uint8_t v_useStdin_1488_; uint8_t v_onlyDeps_1489_; uint8_t v_onlySrcDeps_1490_; uint8_t v_depsJson_1491_; lean_object* v_opts_1492_; uint32_t v_trustLevel_1493_; uint32_t v_numThreads_1494_; lean_object* v_rootDir_x3f_1495_; lean_object* v_setupFileName_x3f_1496_; lean_object* v_oleanFileName_x3f_1497_; lean_object* v_ileanFileName_x3f_1498_; lean_object* v_cFileName_x3f_1499_; lean_object* v_bcFileName_x3f_1500_; uint8_t v_jsonOutput_1501_; lean_object* v_errorOnKinds_1502_; uint8_t v_printStats_1503_; uint8_t v_run_1504_; lean_object* v_incrSaveFileName_x3f_1505_; lean_object* v_incrLoadFileName_x3f_1506_; lean_object* v_incrHeaderSaveFileName_x3f_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1520_; 
v_leanOpts_1483_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_1484_ = lean_ctor_get(v_opts_932_, 1);
v_component_1485_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_1486_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_1487_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_1488_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_1489_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1490_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_1491_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_1492_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_1493_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_1494_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1495_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_1496_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_1497_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_1498_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_1499_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_1500_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_1501_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_1502_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_1503_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_1504_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1505_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_1506_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_1507_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_1520_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1509_ = v_opts_932_;
v_isShared_1510_ = v_isSharedCheck_1520_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1507_);
lean_inc(v_incrLoadFileName_x3f_1506_);
lean_inc(v_incrSaveFileName_x3f_1505_);
lean_inc(v_errorOnKinds_1502_);
lean_inc(v_bcFileName_x3f_1500_);
lean_inc(v_cFileName_x3f_1499_);
lean_inc(v_ileanFileName_x3f_1498_);
lean_inc(v_oleanFileName_x3f_1497_);
lean_inc(v_setupFileName_x3f_1496_);
lean_inc(v_rootDir_x3f_1495_);
lean_inc(v_opts_1492_);
lean_inc(v_forwardedArgs_1484_);
lean_inc(v_leanOpts_1483_);
lean_dec(v_opts_932_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1520_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
v___x_1511_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7));
v___x_1512_ = lean_string_append(v___x_1511_, v_a_1478_);
lean_dec(v_a_1478_);
v___x_1513_ = lean_array_push(v_forwardedArgs_1484_, v___x_1512_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 1, v___x_1513_);
v___x_1515_ = v___x_1509_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_leanOpts_1483_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1519_, 2, v_opts_1492_);
lean_ctor_set(v_reuseFailAlloc_1519_, 3, v_rootDir_x3f_1495_);
lean_ctor_set(v_reuseFailAlloc_1519_, 4, v_setupFileName_x3f_1496_);
lean_ctor_set(v_reuseFailAlloc_1519_, 5, v_oleanFileName_x3f_1497_);
lean_ctor_set(v_reuseFailAlloc_1519_, 6, v_ileanFileName_x3f_1498_);
lean_ctor_set(v_reuseFailAlloc_1519_, 7, v_cFileName_x3f_1499_);
lean_ctor_set(v_reuseFailAlloc_1519_, 8, v_bcFileName_x3f_1500_);
lean_ctor_set(v_reuseFailAlloc_1519_, 9, v_errorOnKinds_1502_);
lean_ctor_set(v_reuseFailAlloc_1519_, 10, v_incrSaveFileName_x3f_1505_);
lean_ctor_set(v_reuseFailAlloc_1519_, 11, v_incrLoadFileName_x3f_1506_);
lean_ctor_set(v_reuseFailAlloc_1519_, 12, v_incrHeaderSaveFileName_x3f_1507_);
lean_ctor_set_uint8(v_reuseFailAlloc_1519_, sizeof(void*)*13 + 8, v_component_1485_);
lean_ctor_set_uint8(v_reuseFailAlloc_1519_, sizeof(void*)*13 + 9, v_printPrefix_1486_);
lean_ctor_set_uint8(v_reuseFailAlloc_1519_, sizeof(void*)*13 + 10, v_printLibDir_1487_);
lean_ctor_set_uint8(v_reuseFailAlloc_1519_, sizeof(void*)*13 + 11, v_useStdin_1488_);
lean_ctor_set_uint8(v_reuseFailAlloc_1519_, sizeof(void*)*13 + 12, v_onlyDeps_1489_);
lean_ctor_set_uint8(v_reuseFailAlloc_1519_, sizeof(void*)*13 + 13, v_onlySrcDeps_1490_);
lean_ctor_set_uint8(v_reuseFailAlloc_1519_, sizeof(void*)*13 + 14, v_depsJson_1491_);
lean_ctor_set_uint32(v_reuseFailAlloc_1519_, sizeof(void*)*13, v_trustLevel_1493_);
lean_ctor_set_uint32(v_reuseFailAlloc_1519_, sizeof(void*)*13 + 4, v_numThreads_1494_);
lean_ctor_set_uint8(v_reuseFailAlloc_1519_, sizeof(void*)*13 + 15, v_jsonOutput_1501_);
lean_ctor_set_uint8(v_reuseFailAlloc_1519_, sizeof(void*)*13 + 16, v_printStats_1503_);
lean_ctor_set_uint8(v_reuseFailAlloc_1519_, sizeof(void*)*13 + 17, v_run_1504_);
v___x_1515_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1517_; 
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v___x_1515_);
v___x_1517_ = v___x_1481_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1515_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
lean_dec(v_a_1478_);
lean_dec_ref(v_opts_932_);
v_a_1523_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1479_, 1);
v___x_1527_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1528_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1527_);
lean_dec_ref(v___x_1528_);
goto v___jp_1524_;
v___jp_1524_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = lean_io_error_to_string(v_a_1523_);
v___x_1526_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1525_);
lean_dec_ref(v___x_1526_);
goto v___jp_1084_;
}
}
}
else
{
lean_object* v_a_1529_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
lean_dec_ref(v_opts_932_);
v_a_1529_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1477_, 1);
v___x_1533_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1534_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1533_);
lean_dec_ref(v___x_1534_);
goto v___jp_1530_;
v___jp_1530_:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = lean_io_error_to_string(v_a_1529_);
v___x_1532_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1531_);
lean_dec_ref(v___x_1532_);
goto v___jp_1020_;
}
}
}
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8));
v___x_1536_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1535_, v_optArg_x3f_934_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1608_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1608_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1608_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v_fst_1542_; lean_object* v_snd_1543_; lean_object* v___y_1592_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1603_ = lean_unsigned_to_nat(0u);
v___x_1604_ = lean_string_utf8_byte_size(v_a_1537_);
v___x_1605_ = lean_box(0);
v___x_1606_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_1604_, v_a_1537_, v___x_1603_, v___x_1605_);
if (lean_obj_tag(v___x_1606_) == 0)
{
v___y_1592_ = v___x_1604_;
goto v___jp_1591_;
}
else
{
lean_object* v_val_1607_; 
v_val_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_val_1607_);
lean_dec_ref_known(v___x_1606_, 1);
v___y_1592_ = v_val_1607_;
goto v___jp_1591_;
}
v___jp_1541_:
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_load_plugin(v_fst_1542_, v_snd_1543_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1586_; 
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1586_ == 0)
{
lean_object* v_unused_1587_; 
v_unused_1587_ = lean_ctor_get(v___x_1544_, 0);
lean_dec(v_unused_1587_);
v___x_1546_ = v___x_1544_;
v_isShared_1547_ = v_isSharedCheck_1586_;
goto v_resetjp_1545_;
}
else
{
lean_dec(v___x_1544_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1586_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v_leanOpts_1548_; lean_object* v_forwardedArgs_1549_; uint8_t v_component_1550_; uint8_t v_printPrefix_1551_; uint8_t v_printLibDir_1552_; uint8_t v_useStdin_1553_; uint8_t v_onlyDeps_1554_; uint8_t v_onlySrcDeps_1555_; uint8_t v_depsJson_1556_; lean_object* v_opts_1557_; uint32_t v_trustLevel_1558_; uint32_t v_numThreads_1559_; lean_object* v_rootDir_x3f_1560_; lean_object* v_setupFileName_x3f_1561_; lean_object* v_oleanFileName_x3f_1562_; lean_object* v_ileanFileName_x3f_1563_; lean_object* v_cFileName_x3f_1564_; lean_object* v_bcFileName_x3f_1565_; uint8_t v_jsonOutput_1566_; lean_object* v_errorOnKinds_1567_; uint8_t v_printStats_1568_; uint8_t v_run_1569_; lean_object* v_incrSaveFileName_x3f_1570_; lean_object* v_incrLoadFileName_x3f_1571_; lean_object* v_incrHeaderSaveFileName_x3f_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1585_; 
v_leanOpts_1548_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_1549_ = lean_ctor_get(v_opts_932_, 1);
v_component_1550_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_1551_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_1552_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_1553_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_1554_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1555_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_1556_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_1557_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_1558_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_1559_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1560_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_1561_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_1562_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_1563_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_1564_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_1565_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_1566_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_1567_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_1568_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_1569_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1570_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_1571_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_1572_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_1585_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1574_ = v_opts_932_;
v_isShared_1575_ = v_isSharedCheck_1585_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1572_);
lean_inc(v_incrLoadFileName_x3f_1571_);
lean_inc(v_incrSaveFileName_x3f_1570_);
lean_inc(v_errorOnKinds_1567_);
lean_inc(v_bcFileName_x3f_1565_);
lean_inc(v_cFileName_x3f_1564_);
lean_inc(v_ileanFileName_x3f_1563_);
lean_inc(v_oleanFileName_x3f_1562_);
lean_inc(v_setupFileName_x3f_1561_);
lean_inc(v_rootDir_x3f_1560_);
lean_inc(v_opts_1557_);
lean_inc(v_forwardedArgs_1549_);
lean_inc(v_leanOpts_1548_);
lean_dec(v_opts_932_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1585_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
v___x_1576_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9));
v___x_1577_ = lean_string_append(v___x_1576_, v_a_1537_);
lean_dec(v_a_1537_);
v___x_1578_ = lean_array_push(v_forwardedArgs_1549_, v___x_1577_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 1, v___x_1578_);
v___x_1580_ = v___x_1574_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_leanOpts_1548_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1584_, 2, v_opts_1557_);
lean_ctor_set(v_reuseFailAlloc_1584_, 3, v_rootDir_x3f_1560_);
lean_ctor_set(v_reuseFailAlloc_1584_, 4, v_setupFileName_x3f_1561_);
lean_ctor_set(v_reuseFailAlloc_1584_, 5, v_oleanFileName_x3f_1562_);
lean_ctor_set(v_reuseFailAlloc_1584_, 6, v_ileanFileName_x3f_1563_);
lean_ctor_set(v_reuseFailAlloc_1584_, 7, v_cFileName_x3f_1564_);
lean_ctor_set(v_reuseFailAlloc_1584_, 8, v_bcFileName_x3f_1565_);
lean_ctor_set(v_reuseFailAlloc_1584_, 9, v_errorOnKinds_1567_);
lean_ctor_set(v_reuseFailAlloc_1584_, 10, v_incrSaveFileName_x3f_1570_);
lean_ctor_set(v_reuseFailAlloc_1584_, 11, v_incrLoadFileName_x3f_1571_);
lean_ctor_set(v_reuseFailAlloc_1584_, 12, v_incrHeaderSaveFileName_x3f_1572_);
lean_ctor_set_uint8(v_reuseFailAlloc_1584_, sizeof(void*)*13 + 8, v_component_1550_);
lean_ctor_set_uint8(v_reuseFailAlloc_1584_, sizeof(void*)*13 + 9, v_printPrefix_1551_);
lean_ctor_set_uint8(v_reuseFailAlloc_1584_, sizeof(void*)*13 + 10, v_printLibDir_1552_);
lean_ctor_set_uint8(v_reuseFailAlloc_1584_, sizeof(void*)*13 + 11, v_useStdin_1553_);
lean_ctor_set_uint8(v_reuseFailAlloc_1584_, sizeof(void*)*13 + 12, v_onlyDeps_1554_);
lean_ctor_set_uint8(v_reuseFailAlloc_1584_, sizeof(void*)*13 + 13, v_onlySrcDeps_1555_);
lean_ctor_set_uint8(v_reuseFailAlloc_1584_, sizeof(void*)*13 + 14, v_depsJson_1556_);
lean_ctor_set_uint32(v_reuseFailAlloc_1584_, sizeof(void*)*13, v_trustLevel_1558_);
lean_ctor_set_uint32(v_reuseFailAlloc_1584_, sizeof(void*)*13 + 4, v_numThreads_1559_);
lean_ctor_set_uint8(v_reuseFailAlloc_1584_, sizeof(void*)*13 + 15, v_jsonOutput_1566_);
lean_ctor_set_uint8(v_reuseFailAlloc_1584_, sizeof(void*)*13 + 16, v_printStats_1568_);
lean_ctor_set_uint8(v_reuseFailAlloc_1584_, sizeof(void*)*13 + 17, v_run_1569_);
v___x_1580_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1582_; 
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 0, v___x_1580_);
v___x_1582_ = v___x_1546_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_dec(v_a_1537_);
lean_dec_ref(v_opts_932_);
v_a_1588_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1544_, 1);
v___x_1589_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1590_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1589_);
lean_dec_ref(v___x_1590_);
v___y_1094_ = v_a_1588_;
goto v___jp_1093_;
}
}
v___jp_1591_:
{
lean_object* v___x_1593_; uint8_t v_decide_1594_; 
v___x_1593_ = lean_string_utf8_byte_size(v_a_1537_);
v_decide_1594_ = lean_nat_dec_eq(v___y_1592_, v___x_1593_);
if (v_decide_1594_ == 0)
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1595_ = lean_unsigned_to_nat(0u);
v___x_1596_ = lean_string_utf8_next_fast(v_a_1537_, v___y_1592_);
v___x_1597_ = lean_string_utf8_extract_fast(v_a_1537_, v___x_1595_, v___y_1592_);
lean_dec(v___y_1592_);
v___x_1598_ = lean_string_utf8_extract_fast(v_a_1537_, v___x_1596_, v___x_1593_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set_tag(v___x_1539_, 1);
lean_ctor_set(v___x_1539_, 0, v___x_1598_);
v___x_1600_ = v___x_1539_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
v_fst_1542_ = v___x_1597_;
v_snd_1543_ = v___x_1600_;
goto v___jp_1541_;
}
}
else
{
lean_object* v___x_1602_; 
lean_dec(v___y_1592_);
lean_del_object(v___x_1539_);
v___x_1602_ = lean_box(0);
lean_inc(v_a_1537_);
v_fst_1542_ = v_a_1537_;
v_snd_1543_ = v___x_1602_;
goto v___jp_1541_;
}
}
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
lean_dec_ref(v_opts_932_);
v_a_1609_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1609_);
lean_dec_ref_known(v___x_1536_, 1);
v___x_1613_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1614_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1613_);
lean_dec_ref(v___x_1614_);
goto v___jp_1610_;
v___jp_1610_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = lean_io_error_to_string(v_a_1609_);
v___x_1612_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1611_);
lean_dec_ref(v___x_1612_);
goto v___jp_1014_;
}
}
}
}
else
{
uint8_t v___x_1615_; 
v___x_1615_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__16, &l___private_Lean_Shell_0__Lean_displayHelp___closed__16_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__16);
if (v___x_1615_ == 0)
{
lean_dec(v_optArg_x3f_934_);
lean_dec_ref(v_opts_932_);
goto v___jp_1066_;
}
else
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10));
v___x_1617_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1616_, v_optArg_x3f_934_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1626_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1626_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1626_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1622_; lean_object* v___x_1624_; 
v___x_1622_ = lean_internal_enable_debug(v_a_1618_);
lean_dec(v_a_1618_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v_opts_932_);
v___x_1624_ = v___x_1620_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_opts_932_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
lean_dec_ref(v_opts_932_);
v_a_1627_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1617_, 1);
v___x_1631_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1632_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1631_);
lean_dec_ref(v___x_1632_);
goto v___jp_1628_;
v___jp_1628_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = lean_io_error_to_string(v_a_1627_);
v___x_1630_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1629_);
lean_dec_ref(v___x_1630_);
goto v___jp_1100_;
}
}
}
}
}
else
{
lean_object* v_leanOpts_1633_; lean_object* v_forwardedArgs_1634_; uint8_t v_component_1635_; uint8_t v_printPrefix_1636_; uint8_t v_printLibDir_1637_; uint8_t v_useStdin_1638_; uint8_t v_onlyDeps_1639_; uint8_t v_onlySrcDeps_1640_; uint8_t v_depsJson_1641_; lean_object* v_opts_1642_; uint32_t v_trustLevel_1643_; uint32_t v_numThreads_1644_; lean_object* v_rootDir_x3f_1645_; lean_object* v_setupFileName_x3f_1646_; lean_object* v_oleanFileName_x3f_1647_; lean_object* v_ileanFileName_x3f_1648_; lean_object* v_cFileName_x3f_1649_; lean_object* v_bcFileName_x3f_1650_; uint8_t v_jsonOutput_1651_; lean_object* v_errorOnKinds_1652_; uint8_t v_printStats_1653_; uint8_t v_run_1654_; lean_object* v_incrSaveFileName_x3f_1655_; lean_object* v_incrLoadFileName_x3f_1656_; lean_object* v_incrHeaderSaveFileName_x3f_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1667_; 
lean_dec(v_optArg_x3f_934_);
v_leanOpts_1633_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_1634_ = lean_ctor_get(v_opts_932_, 1);
v_component_1635_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_1636_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_1637_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_1638_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_1639_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1640_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_1641_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_1642_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_1643_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_1644_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1645_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_1646_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_1647_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_1648_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_1649_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_1650_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_1651_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_1652_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_1653_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_1654_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1655_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_1656_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_1657_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_1667_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1659_ = v_opts_932_;
v_isShared_1660_ = v_isSharedCheck_1667_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1657_);
lean_inc(v_incrLoadFileName_x3f_1656_);
lean_inc(v_incrSaveFileName_x3f_1655_);
lean_inc(v_errorOnKinds_1652_);
lean_inc(v_bcFileName_x3f_1650_);
lean_inc(v_cFileName_x3f_1649_);
lean_inc(v_ileanFileName_x3f_1648_);
lean_inc(v_oleanFileName_x3f_1647_);
lean_inc(v_setupFileName_x3f_1646_);
lean_inc(v_rootDir_x3f_1645_);
lean_inc(v_opts_1642_);
lean_inc(v_forwardedArgs_1634_);
lean_inc(v_leanOpts_1633_);
lean_dec(v_opts_932_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1667_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1664_; 
v___x_1661_ = l_Lean_profiler;
v___x_1662_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_1633_, v___x_1661_, v___x_1213_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 0, v___x_1662_);
v___x_1664_ = v___x_1659_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1662_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_forwardedArgs_1634_);
lean_ctor_set(v_reuseFailAlloc_1666_, 2, v_opts_1642_);
lean_ctor_set(v_reuseFailAlloc_1666_, 3, v_rootDir_x3f_1645_);
lean_ctor_set(v_reuseFailAlloc_1666_, 4, v_setupFileName_x3f_1646_);
lean_ctor_set(v_reuseFailAlloc_1666_, 5, v_oleanFileName_x3f_1647_);
lean_ctor_set(v_reuseFailAlloc_1666_, 6, v_ileanFileName_x3f_1648_);
lean_ctor_set(v_reuseFailAlloc_1666_, 7, v_cFileName_x3f_1649_);
lean_ctor_set(v_reuseFailAlloc_1666_, 8, v_bcFileName_x3f_1650_);
lean_ctor_set(v_reuseFailAlloc_1666_, 9, v_errorOnKinds_1652_);
lean_ctor_set(v_reuseFailAlloc_1666_, 10, v_incrSaveFileName_x3f_1655_);
lean_ctor_set(v_reuseFailAlloc_1666_, 11, v_incrLoadFileName_x3f_1656_);
lean_ctor_set(v_reuseFailAlloc_1666_, 12, v_incrHeaderSaveFileName_x3f_1657_);
lean_ctor_set_uint8(v_reuseFailAlloc_1666_, sizeof(void*)*13 + 8, v_component_1635_);
lean_ctor_set_uint8(v_reuseFailAlloc_1666_, sizeof(void*)*13 + 9, v_printPrefix_1636_);
lean_ctor_set_uint8(v_reuseFailAlloc_1666_, sizeof(void*)*13 + 10, v_printLibDir_1637_);
lean_ctor_set_uint8(v_reuseFailAlloc_1666_, sizeof(void*)*13 + 11, v_useStdin_1638_);
lean_ctor_set_uint8(v_reuseFailAlloc_1666_, sizeof(void*)*13 + 12, v_onlyDeps_1639_);
lean_ctor_set_uint8(v_reuseFailAlloc_1666_, sizeof(void*)*13 + 13, v_onlySrcDeps_1640_);
lean_ctor_set_uint8(v_reuseFailAlloc_1666_, sizeof(void*)*13 + 14, v_depsJson_1641_);
lean_ctor_set_uint32(v_reuseFailAlloc_1666_, sizeof(void*)*13, v_trustLevel_1643_);
lean_ctor_set_uint32(v_reuseFailAlloc_1666_, sizeof(void*)*13 + 4, v_numThreads_1644_);
lean_ctor_set_uint8(v_reuseFailAlloc_1666_, sizeof(void*)*13 + 15, v_jsonOutput_1651_);
lean_ctor_set_uint8(v_reuseFailAlloc_1666_, sizeof(void*)*13 + 16, v_printStats_1653_);
lean_ctor_set_uint8(v_reuseFailAlloc_1666_, sizeof(void*)*13 + 17, v_run_1654_);
v___x_1664_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
lean_object* v___x_1665_; 
v___x_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
return v___x_1665_;
}
}
}
}
else
{
lean_object* v_leanOpts_1668_; lean_object* v_forwardedArgs_1669_; uint8_t v_printPrefix_1670_; uint8_t v_printLibDir_1671_; uint8_t v_useStdin_1672_; uint8_t v_onlyDeps_1673_; uint8_t v_onlySrcDeps_1674_; uint8_t v_depsJson_1675_; lean_object* v_opts_1676_; uint32_t v_trustLevel_1677_; uint32_t v_numThreads_1678_; lean_object* v_rootDir_x3f_1679_; lean_object* v_setupFileName_x3f_1680_; lean_object* v_oleanFileName_x3f_1681_; lean_object* v_ileanFileName_x3f_1682_; lean_object* v_cFileName_x3f_1683_; lean_object* v_bcFileName_x3f_1684_; uint8_t v_jsonOutput_1685_; lean_object* v_errorOnKinds_1686_; uint8_t v_printStats_1687_; uint8_t v_run_1688_; lean_object* v_incrSaveFileName_x3f_1689_; lean_object* v_incrLoadFileName_x3f_1690_; lean_object* v_incrHeaderSaveFileName_x3f_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1700_; 
lean_dec(v_optArg_x3f_934_);
v_leanOpts_1668_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_1669_ = lean_ctor_get(v_opts_932_, 1);
v_printPrefix_1670_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_1671_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_1672_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_1673_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1674_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_1675_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_1676_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_1677_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_1678_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1679_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_1680_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_1681_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_1682_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_1683_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_1684_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_1685_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_1686_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_1687_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_1688_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1689_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_1690_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_1691_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1693_ = v_opts_932_;
v_isShared_1694_ = v_isSharedCheck_1700_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1691_);
lean_inc(v_incrLoadFileName_x3f_1690_);
lean_inc(v_incrSaveFileName_x3f_1689_);
lean_inc(v_errorOnKinds_1686_);
lean_inc(v_bcFileName_x3f_1684_);
lean_inc(v_cFileName_x3f_1683_);
lean_inc(v_ileanFileName_x3f_1682_);
lean_inc(v_oleanFileName_x3f_1681_);
lean_inc(v_setupFileName_x3f_1680_);
lean_inc(v_rootDir_x3f_1679_);
lean_inc(v_opts_1676_);
lean_inc(v_forwardedArgs_1669_);
lean_inc(v_leanOpts_1668_);
lean_dec(v_opts_932_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1700_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
uint8_t v___x_1695_; lean_object* v___x_1697_; 
v___x_1695_ = 2;
if (v_isShared_1694_ == 0)
{
v___x_1697_ = v___x_1693_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_leanOpts_1668_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_forwardedArgs_1669_);
lean_ctor_set(v_reuseFailAlloc_1699_, 2, v_opts_1676_);
lean_ctor_set(v_reuseFailAlloc_1699_, 3, v_rootDir_x3f_1679_);
lean_ctor_set(v_reuseFailAlloc_1699_, 4, v_setupFileName_x3f_1680_);
lean_ctor_set(v_reuseFailAlloc_1699_, 5, v_oleanFileName_x3f_1681_);
lean_ctor_set(v_reuseFailAlloc_1699_, 6, v_ileanFileName_x3f_1682_);
lean_ctor_set(v_reuseFailAlloc_1699_, 7, v_cFileName_x3f_1683_);
lean_ctor_set(v_reuseFailAlloc_1699_, 8, v_bcFileName_x3f_1684_);
lean_ctor_set(v_reuseFailAlloc_1699_, 9, v_errorOnKinds_1686_);
lean_ctor_set(v_reuseFailAlloc_1699_, 10, v_incrSaveFileName_x3f_1689_);
lean_ctor_set(v_reuseFailAlloc_1699_, 11, v_incrLoadFileName_x3f_1690_);
lean_ctor_set(v_reuseFailAlloc_1699_, 12, v_incrHeaderSaveFileName_x3f_1691_);
lean_ctor_set_uint8(v_reuseFailAlloc_1699_, sizeof(void*)*13 + 9, v_printPrefix_1670_);
lean_ctor_set_uint8(v_reuseFailAlloc_1699_, sizeof(void*)*13 + 10, v_printLibDir_1671_);
lean_ctor_set_uint8(v_reuseFailAlloc_1699_, sizeof(void*)*13 + 11, v_useStdin_1672_);
lean_ctor_set_uint8(v_reuseFailAlloc_1699_, sizeof(void*)*13 + 12, v_onlyDeps_1673_);
lean_ctor_set_uint8(v_reuseFailAlloc_1699_, sizeof(void*)*13 + 13, v_onlySrcDeps_1674_);
lean_ctor_set_uint8(v_reuseFailAlloc_1699_, sizeof(void*)*13 + 14, v_depsJson_1675_);
lean_ctor_set_uint32(v_reuseFailAlloc_1699_, sizeof(void*)*13, v_trustLevel_1677_);
lean_ctor_set_uint32(v_reuseFailAlloc_1699_, sizeof(void*)*13 + 4, v_numThreads_1678_);
lean_ctor_set_uint8(v_reuseFailAlloc_1699_, sizeof(void*)*13 + 15, v_jsonOutput_1685_);
lean_ctor_set_uint8(v_reuseFailAlloc_1699_, sizeof(void*)*13 + 16, v_printStats_1687_);
lean_ctor_set_uint8(v_reuseFailAlloc_1699_, sizeof(void*)*13 + 17, v_run_1688_);
v___x_1697_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
lean_object* v___x_1698_; 
lean_ctor_set_uint8(v___x_1697_, sizeof(void*)*13 + 8, v___x_1695_);
v___x_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1697_);
return v___x_1698_;
}
}
}
}
else
{
lean_object* v_leanOpts_1701_; lean_object* v_forwardedArgs_1702_; uint8_t v_printPrefix_1703_; uint8_t v_printLibDir_1704_; uint8_t v_useStdin_1705_; uint8_t v_onlyDeps_1706_; uint8_t v_onlySrcDeps_1707_; uint8_t v_depsJson_1708_; lean_object* v_opts_1709_; uint32_t v_trustLevel_1710_; uint32_t v_numThreads_1711_; lean_object* v_rootDir_x3f_1712_; lean_object* v_setupFileName_x3f_1713_; lean_object* v_oleanFileName_x3f_1714_; lean_object* v_ileanFileName_x3f_1715_; lean_object* v_cFileName_x3f_1716_; lean_object* v_bcFileName_x3f_1717_; uint8_t v_jsonOutput_1718_; lean_object* v_errorOnKinds_1719_; uint8_t v_printStats_1720_; uint8_t v_run_1721_; lean_object* v_incrSaveFileName_x3f_1722_; lean_object* v_incrLoadFileName_x3f_1723_; lean_object* v_incrHeaderSaveFileName_x3f_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1733_; 
lean_dec(v_optArg_x3f_934_);
v_leanOpts_1701_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_1702_ = lean_ctor_get(v_opts_932_, 1);
v_printPrefix_1703_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_1704_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_1705_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_1706_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1707_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_1708_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_1709_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_1710_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_1711_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1712_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_1713_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_1714_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_1715_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_1716_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_1717_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_1718_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_1719_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_1720_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_1721_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1722_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_1723_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_1724_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1726_ = v_opts_932_;
v_isShared_1727_ = v_isSharedCheck_1733_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1724_);
lean_inc(v_incrLoadFileName_x3f_1723_);
lean_inc(v_incrSaveFileName_x3f_1722_);
lean_inc(v_errorOnKinds_1719_);
lean_inc(v_bcFileName_x3f_1717_);
lean_inc(v_cFileName_x3f_1716_);
lean_inc(v_ileanFileName_x3f_1715_);
lean_inc(v_oleanFileName_x3f_1714_);
lean_inc(v_setupFileName_x3f_1713_);
lean_inc(v_rootDir_x3f_1712_);
lean_inc(v_opts_1709_);
lean_inc(v_forwardedArgs_1702_);
lean_inc(v_leanOpts_1701_);
lean_dec(v_opts_932_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1733_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
uint8_t v___x_1728_; lean_object* v___x_1730_; 
v___x_1728_ = 1;
if (v_isShared_1727_ == 0)
{
v___x_1730_ = v___x_1726_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_leanOpts_1701_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_forwardedArgs_1702_);
lean_ctor_set(v_reuseFailAlloc_1732_, 2, v_opts_1709_);
lean_ctor_set(v_reuseFailAlloc_1732_, 3, v_rootDir_x3f_1712_);
lean_ctor_set(v_reuseFailAlloc_1732_, 4, v_setupFileName_x3f_1713_);
lean_ctor_set(v_reuseFailAlloc_1732_, 5, v_oleanFileName_x3f_1714_);
lean_ctor_set(v_reuseFailAlloc_1732_, 6, v_ileanFileName_x3f_1715_);
lean_ctor_set(v_reuseFailAlloc_1732_, 7, v_cFileName_x3f_1716_);
lean_ctor_set(v_reuseFailAlloc_1732_, 8, v_bcFileName_x3f_1717_);
lean_ctor_set(v_reuseFailAlloc_1732_, 9, v_errorOnKinds_1719_);
lean_ctor_set(v_reuseFailAlloc_1732_, 10, v_incrSaveFileName_x3f_1722_);
lean_ctor_set(v_reuseFailAlloc_1732_, 11, v_incrLoadFileName_x3f_1723_);
lean_ctor_set(v_reuseFailAlloc_1732_, 12, v_incrHeaderSaveFileName_x3f_1724_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*13 + 9, v_printPrefix_1703_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*13 + 10, v_printLibDir_1704_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*13 + 11, v_useStdin_1705_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*13 + 12, v_onlyDeps_1706_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*13 + 13, v_onlySrcDeps_1707_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*13 + 14, v_depsJson_1708_);
lean_ctor_set_uint32(v_reuseFailAlloc_1732_, sizeof(void*)*13, v_trustLevel_1710_);
lean_ctor_set_uint32(v_reuseFailAlloc_1732_, sizeof(void*)*13 + 4, v_numThreads_1711_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*13 + 15, v_jsonOutput_1718_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*13 + 16, v_printStats_1720_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*13 + 17, v_run_1721_);
v___x_1730_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1731_; 
lean_ctor_set_uint8(v___x_1730_, sizeof(void*)*13 + 8, v___x_1728_);
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
return v___x_1731_;
}
}
}
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11));
v___x_1735_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1734_, v_optArg_x3f_934_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v_leanOpts_1737_; lean_object* v_forwardedArgs_1738_; uint8_t v_component_1739_; uint8_t v_printPrefix_1740_; uint8_t v_printLibDir_1741_; uint8_t v_useStdin_1742_; uint8_t v_onlyDeps_1743_; uint8_t v_onlySrcDeps_1744_; uint8_t v_depsJson_1745_; lean_object* v_opts_1746_; uint32_t v_trustLevel_1747_; uint32_t v_numThreads_1748_; lean_object* v_rootDir_x3f_1749_; lean_object* v_setupFileName_x3f_1750_; lean_object* v_oleanFileName_x3f_1751_; lean_object* v_ileanFileName_x3f_1752_; lean_object* v_cFileName_x3f_1753_; lean_object* v_bcFileName_x3f_1754_; uint8_t v_jsonOutput_1755_; lean_object* v_errorOnKinds_1756_; uint8_t v_printStats_1757_; uint8_t v_run_1758_; lean_object* v_incrSaveFileName_x3f_1759_; lean_object* v_incrLoadFileName_x3f_1760_; lean_object* v_incrHeaderSaveFileName_x3f_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1786_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref_known(v___x_1735_, 1);
v_leanOpts_1737_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_1738_ = lean_ctor_get(v_opts_932_, 1);
v_component_1739_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_1740_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_1741_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_1742_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_1743_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1744_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_1745_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_1746_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_1747_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_1748_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1749_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_1750_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_1751_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_1752_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_1753_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_1754_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_1755_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_1756_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_1757_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_1758_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1759_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_1760_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_1761_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1763_ = v_opts_932_;
v_isShared_1764_ = v_isSharedCheck_1786_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1761_);
lean_inc(v_incrLoadFileName_x3f_1760_);
lean_inc(v_incrSaveFileName_x3f_1759_);
lean_inc(v_errorOnKinds_1756_);
lean_inc(v_bcFileName_x3f_1754_);
lean_inc(v_cFileName_x3f_1753_);
lean_inc(v_ileanFileName_x3f_1752_);
lean_inc(v_oleanFileName_x3f_1751_);
lean_inc(v_setupFileName_x3f_1750_);
lean_inc(v_rootDir_x3f_1749_);
lean_inc(v_opts_1746_);
lean_inc(v_forwardedArgs_1738_);
lean_inc(v_leanOpts_1737_);
lean_dec(v_opts_932_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1786_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1765_; 
lean_inc(v_a_1736_);
v___x_1765_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_leanOpts_1737_, v_a_1736_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1779_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1768_ = v___x_1765_;
v_isShared_1769_ = v_isSharedCheck_1779_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1779_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1770_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12));
v___x_1771_ = lean_string_append(v___x_1770_, v_a_1736_);
lean_dec(v_a_1736_);
v___x_1772_ = lean_array_push(v_forwardedArgs_1738_, v___x_1771_);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 1, v___x_1772_);
lean_ctor_set(v___x_1763_, 0, v_a_1766_);
v___x_1774_ = v___x_1763_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1766_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v___x_1772_);
lean_ctor_set(v_reuseFailAlloc_1778_, 2, v_opts_1746_);
lean_ctor_set(v_reuseFailAlloc_1778_, 3, v_rootDir_x3f_1749_);
lean_ctor_set(v_reuseFailAlloc_1778_, 4, v_setupFileName_x3f_1750_);
lean_ctor_set(v_reuseFailAlloc_1778_, 5, v_oleanFileName_x3f_1751_);
lean_ctor_set(v_reuseFailAlloc_1778_, 6, v_ileanFileName_x3f_1752_);
lean_ctor_set(v_reuseFailAlloc_1778_, 7, v_cFileName_x3f_1753_);
lean_ctor_set(v_reuseFailAlloc_1778_, 8, v_bcFileName_x3f_1754_);
lean_ctor_set(v_reuseFailAlloc_1778_, 9, v_errorOnKinds_1756_);
lean_ctor_set(v_reuseFailAlloc_1778_, 10, v_incrSaveFileName_x3f_1759_);
lean_ctor_set(v_reuseFailAlloc_1778_, 11, v_incrLoadFileName_x3f_1760_);
lean_ctor_set(v_reuseFailAlloc_1778_, 12, v_incrHeaderSaveFileName_x3f_1761_);
lean_ctor_set_uint8(v_reuseFailAlloc_1778_, sizeof(void*)*13 + 8, v_component_1739_);
lean_ctor_set_uint8(v_reuseFailAlloc_1778_, sizeof(void*)*13 + 9, v_printPrefix_1740_);
lean_ctor_set_uint8(v_reuseFailAlloc_1778_, sizeof(void*)*13 + 10, v_printLibDir_1741_);
lean_ctor_set_uint8(v_reuseFailAlloc_1778_, sizeof(void*)*13 + 11, v_useStdin_1742_);
lean_ctor_set_uint8(v_reuseFailAlloc_1778_, sizeof(void*)*13 + 12, v_onlyDeps_1743_);
lean_ctor_set_uint8(v_reuseFailAlloc_1778_, sizeof(void*)*13 + 13, v_onlySrcDeps_1744_);
lean_ctor_set_uint8(v_reuseFailAlloc_1778_, sizeof(void*)*13 + 14, v_depsJson_1745_);
lean_ctor_set_uint32(v_reuseFailAlloc_1778_, sizeof(void*)*13, v_trustLevel_1747_);
lean_ctor_set_uint32(v_reuseFailAlloc_1778_, sizeof(void*)*13 + 4, v_numThreads_1748_);
lean_ctor_set_uint8(v_reuseFailAlloc_1778_, sizeof(void*)*13 + 15, v_jsonOutput_1755_);
lean_ctor_set_uint8(v_reuseFailAlloc_1778_, sizeof(void*)*13 + 16, v_printStats_1757_);
lean_ctor_set_uint8(v_reuseFailAlloc_1778_, sizeof(void*)*13 + 17, v_run_1758_);
v___x_1774_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1776_; 
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1774_);
v___x_1776_ = v___x_1768_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1774_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
lean_del_object(v___x_1763_);
lean_dec(v_incrHeaderSaveFileName_x3f_1761_);
lean_dec(v_incrLoadFileName_x3f_1760_);
lean_dec(v_incrSaveFileName_x3f_1759_);
lean_dec_ref(v_errorOnKinds_1756_);
lean_dec(v_bcFileName_x3f_1754_);
lean_dec(v_cFileName_x3f_1753_);
lean_dec(v_ileanFileName_x3f_1752_);
lean_dec(v_oleanFileName_x3f_1751_);
lean_dec(v_setupFileName_x3f_1750_);
lean_dec(v_rootDir_x3f_1749_);
lean_dec_ref(v_opts_1746_);
lean_dec_ref(v_forwardedArgs_1738_);
lean_dec(v_a_1736_);
v_a_1780_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1780_);
lean_dec_ref_known(v___x_1765_, 1);
v___x_1784_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1785_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1784_);
lean_dec_ref(v___x_1785_);
goto v___jp_1781_;
v___jp_1781_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = lean_io_error_to_string(v_a_1780_);
v___x_1783_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1782_);
lean_dec_ref(v___x_1783_);
goto v___jp_1008_;
}
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
lean_dec_ref(v_opts_932_);
v_a_1787_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1787_);
lean_dec_ref_known(v___x_1735_, 1);
v___x_1791_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1792_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1791_);
lean_dec_ref(v___x_1792_);
goto v___jp_1788_;
v___jp_1788_:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = lean_io_error_to_string(v_a_1787_);
v___x_1790_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1789_);
lean_dec_ref(v___x_1790_);
goto v___jp_1106_;
}
}
}
}
else
{
lean_object* v_leanOpts_1793_; lean_object* v_forwardedArgs_1794_; uint8_t v_component_1795_; uint8_t v_printPrefix_1796_; uint8_t v_useStdin_1797_; uint8_t v_onlyDeps_1798_; uint8_t v_onlySrcDeps_1799_; uint8_t v_depsJson_1800_; lean_object* v_opts_1801_; uint32_t v_trustLevel_1802_; uint32_t v_numThreads_1803_; lean_object* v_rootDir_x3f_1804_; lean_object* v_setupFileName_x3f_1805_; lean_object* v_oleanFileName_x3f_1806_; lean_object* v_ileanFileName_x3f_1807_; lean_object* v_cFileName_x3f_1808_; lean_object* v_bcFileName_x3f_1809_; uint8_t v_jsonOutput_1810_; lean_object* v_errorOnKinds_1811_; uint8_t v_printStats_1812_; uint8_t v_run_1813_; lean_object* v_incrSaveFileName_x3f_1814_; lean_object* v_incrLoadFileName_x3f_1815_; lean_object* v_incrHeaderSaveFileName_x3f_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1824_; 
lean_dec(v_optArg_x3f_934_);
v_leanOpts_1793_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_1794_ = lean_ctor_get(v_opts_932_, 1);
v_component_1795_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_1796_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_useStdin_1797_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_1798_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1799_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_1800_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_1801_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_1802_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_1803_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1804_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_1805_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_1806_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_1807_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_1808_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_1809_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_1810_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_1811_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_1812_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_1813_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1814_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_1815_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_1816_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_1824_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1818_ = v_opts_932_;
v_isShared_1819_ = v_isSharedCheck_1824_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1816_);
lean_inc(v_incrLoadFileName_x3f_1815_);
lean_inc(v_incrSaveFileName_x3f_1814_);
lean_inc(v_errorOnKinds_1811_);
lean_inc(v_bcFileName_x3f_1809_);
lean_inc(v_cFileName_x3f_1808_);
lean_inc(v_ileanFileName_x3f_1807_);
lean_inc(v_oleanFileName_x3f_1806_);
lean_inc(v_setupFileName_x3f_1805_);
lean_inc(v_rootDir_x3f_1804_);
lean_inc(v_opts_1801_);
lean_inc(v_forwardedArgs_1794_);
lean_inc(v_leanOpts_1793_);
lean_dec(v_opts_932_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1824_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_leanOpts_1793_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_forwardedArgs_1794_);
lean_ctor_set(v_reuseFailAlloc_1823_, 2, v_opts_1801_);
lean_ctor_set(v_reuseFailAlloc_1823_, 3, v_rootDir_x3f_1804_);
lean_ctor_set(v_reuseFailAlloc_1823_, 4, v_setupFileName_x3f_1805_);
lean_ctor_set(v_reuseFailAlloc_1823_, 5, v_oleanFileName_x3f_1806_);
lean_ctor_set(v_reuseFailAlloc_1823_, 6, v_ileanFileName_x3f_1807_);
lean_ctor_set(v_reuseFailAlloc_1823_, 7, v_cFileName_x3f_1808_);
lean_ctor_set(v_reuseFailAlloc_1823_, 8, v_bcFileName_x3f_1809_);
lean_ctor_set(v_reuseFailAlloc_1823_, 9, v_errorOnKinds_1811_);
lean_ctor_set(v_reuseFailAlloc_1823_, 10, v_incrSaveFileName_x3f_1814_);
lean_ctor_set(v_reuseFailAlloc_1823_, 11, v_incrLoadFileName_x3f_1815_);
lean_ctor_set(v_reuseFailAlloc_1823_, 12, v_incrHeaderSaveFileName_x3f_1816_);
lean_ctor_set_uint8(v_reuseFailAlloc_1823_, sizeof(void*)*13 + 8, v_component_1795_);
lean_ctor_set_uint8(v_reuseFailAlloc_1823_, sizeof(void*)*13 + 9, v_printPrefix_1796_);
lean_ctor_set_uint8(v_reuseFailAlloc_1823_, sizeof(void*)*13 + 11, v_useStdin_1797_);
lean_ctor_set_uint8(v_reuseFailAlloc_1823_, sizeof(void*)*13 + 12, v_onlyDeps_1798_);
lean_ctor_set_uint8(v_reuseFailAlloc_1823_, sizeof(void*)*13 + 13, v_onlySrcDeps_1799_);
lean_ctor_set_uint8(v_reuseFailAlloc_1823_, sizeof(void*)*13 + 14, v_depsJson_1800_);
lean_ctor_set_uint32(v_reuseFailAlloc_1823_, sizeof(void*)*13, v_trustLevel_1802_);
lean_ctor_set_uint32(v_reuseFailAlloc_1823_, sizeof(void*)*13 + 4, v_numThreads_1803_);
lean_ctor_set_uint8(v_reuseFailAlloc_1823_, sizeof(void*)*13 + 15, v_jsonOutput_1810_);
lean_ctor_set_uint8(v_reuseFailAlloc_1823_, sizeof(void*)*13 + 16, v_printStats_1812_);
lean_ctor_set_uint8(v_reuseFailAlloc_1823_, sizeof(void*)*13 + 17, v_run_1813_);
v___x_1821_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1822_; 
lean_ctor_set_uint8(v___x_1821_, sizeof(void*)*13 + 10, v___x_1205_);
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
return v___x_1822_;
}
}
}
}
else
{
lean_object* v_leanOpts_1825_; lean_object* v_forwardedArgs_1826_; uint8_t v_component_1827_; uint8_t v_printLibDir_1828_; uint8_t v_useStdin_1829_; uint8_t v_onlyDeps_1830_; uint8_t v_onlySrcDeps_1831_; uint8_t v_depsJson_1832_; lean_object* v_opts_1833_; uint32_t v_trustLevel_1834_; uint32_t v_numThreads_1835_; lean_object* v_rootDir_x3f_1836_; lean_object* v_setupFileName_x3f_1837_; lean_object* v_oleanFileName_x3f_1838_; lean_object* v_ileanFileName_x3f_1839_; lean_object* v_cFileName_x3f_1840_; lean_object* v_bcFileName_x3f_1841_; uint8_t v_jsonOutput_1842_; lean_object* v_errorOnKinds_1843_; uint8_t v_printStats_1844_; uint8_t v_run_1845_; lean_object* v_incrSaveFileName_x3f_1846_; lean_object* v_incrLoadFileName_x3f_1847_; lean_object* v_incrHeaderSaveFileName_x3f_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1856_; 
lean_dec(v_optArg_x3f_934_);
v_leanOpts_1825_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_1826_ = lean_ctor_get(v_opts_932_, 1);
v_component_1827_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printLibDir_1828_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_1829_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_1830_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1831_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_1832_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_1833_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_1834_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_1835_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1836_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_1837_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_1838_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_1839_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_1840_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_1841_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_1842_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_1843_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_1844_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_1845_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1846_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_1847_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_1848_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1850_ = v_opts_932_;
v_isShared_1851_ = v_isSharedCheck_1856_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1848_);
lean_inc(v_incrLoadFileName_x3f_1847_);
lean_inc(v_incrSaveFileName_x3f_1846_);
lean_inc(v_errorOnKinds_1843_);
lean_inc(v_bcFileName_x3f_1841_);
lean_inc(v_cFileName_x3f_1840_);
lean_inc(v_ileanFileName_x3f_1839_);
lean_inc(v_oleanFileName_x3f_1838_);
lean_inc(v_setupFileName_x3f_1837_);
lean_inc(v_rootDir_x3f_1836_);
lean_inc(v_opts_1833_);
lean_inc(v_forwardedArgs_1826_);
lean_inc(v_leanOpts_1825_);
lean_dec(v_opts_932_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1856_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_leanOpts_1825_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v_forwardedArgs_1826_);
lean_ctor_set(v_reuseFailAlloc_1855_, 2, v_opts_1833_);
lean_ctor_set(v_reuseFailAlloc_1855_, 3, v_rootDir_x3f_1836_);
lean_ctor_set(v_reuseFailAlloc_1855_, 4, v_setupFileName_x3f_1837_);
lean_ctor_set(v_reuseFailAlloc_1855_, 5, v_oleanFileName_x3f_1838_);
lean_ctor_set(v_reuseFailAlloc_1855_, 6, v_ileanFileName_x3f_1839_);
lean_ctor_set(v_reuseFailAlloc_1855_, 7, v_cFileName_x3f_1840_);
lean_ctor_set(v_reuseFailAlloc_1855_, 8, v_bcFileName_x3f_1841_);
lean_ctor_set(v_reuseFailAlloc_1855_, 9, v_errorOnKinds_1843_);
lean_ctor_set(v_reuseFailAlloc_1855_, 10, v_incrSaveFileName_x3f_1846_);
lean_ctor_set(v_reuseFailAlloc_1855_, 11, v_incrLoadFileName_x3f_1847_);
lean_ctor_set(v_reuseFailAlloc_1855_, 12, v_incrHeaderSaveFileName_x3f_1848_);
lean_ctor_set_uint8(v_reuseFailAlloc_1855_, sizeof(void*)*13 + 8, v_component_1827_);
lean_ctor_set_uint8(v_reuseFailAlloc_1855_, sizeof(void*)*13 + 10, v_printLibDir_1828_);
lean_ctor_set_uint8(v_reuseFailAlloc_1855_, sizeof(void*)*13 + 11, v_useStdin_1829_);
lean_ctor_set_uint8(v_reuseFailAlloc_1855_, sizeof(void*)*13 + 12, v_onlyDeps_1830_);
lean_ctor_set_uint8(v_reuseFailAlloc_1855_, sizeof(void*)*13 + 13, v_onlySrcDeps_1831_);
lean_ctor_set_uint8(v_reuseFailAlloc_1855_, sizeof(void*)*13 + 14, v_depsJson_1832_);
lean_ctor_set_uint32(v_reuseFailAlloc_1855_, sizeof(void*)*13, v_trustLevel_1834_);
lean_ctor_set_uint32(v_reuseFailAlloc_1855_, sizeof(void*)*13 + 4, v_numThreads_1835_);
lean_ctor_set_uint8(v_reuseFailAlloc_1855_, sizeof(void*)*13 + 15, v_jsonOutput_1842_);
lean_ctor_set_uint8(v_reuseFailAlloc_1855_, sizeof(void*)*13 + 16, v_printStats_1844_);
lean_ctor_set_uint8(v_reuseFailAlloc_1855_, sizeof(void*)*13 + 17, v_run_1845_);
v___x_1853_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1854_; 
lean_ctor_set_uint8(v___x_1853_, sizeof(void*)*13 + 9, v___x_1203_);
v___x_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
return v___x_1854_;
}
}
}
}
else
{
lean_object* v_leanOpts_1857_; lean_object* v_forwardedArgs_1858_; uint8_t v_component_1859_; uint8_t v_printPrefix_1860_; uint8_t v_printLibDir_1861_; uint8_t v_useStdin_1862_; uint8_t v_onlyDeps_1863_; uint8_t v_onlySrcDeps_1864_; uint8_t v_depsJson_1865_; lean_object* v_opts_1866_; uint32_t v_trustLevel_1867_; uint32_t v_numThreads_1868_; lean_object* v_rootDir_x3f_1869_; lean_object* v_setupFileName_x3f_1870_; lean_object* v_oleanFileName_x3f_1871_; lean_object* v_ileanFileName_x3f_1872_; lean_object* v_cFileName_x3f_1873_; lean_object* v_bcFileName_x3f_1874_; uint8_t v_jsonOutput_1875_; lean_object* v_errorOnKinds_1876_; uint8_t v_run_1877_; lean_object* v_incrSaveFileName_x3f_1878_; lean_object* v_incrLoadFileName_x3f_1879_; lean_object* v_incrHeaderSaveFileName_x3f_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1888_; 
lean_dec(v_optArg_x3f_934_);
v_leanOpts_1857_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_1858_ = lean_ctor_get(v_opts_932_, 1);
v_component_1859_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_1860_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_1861_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_1862_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_1863_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1864_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_1865_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_1866_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_1867_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_1868_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1869_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_1870_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_1871_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_1872_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_1873_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_1874_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_1875_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_1876_ = lean_ctor_get(v_opts_932_, 9);
v_run_1877_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1878_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_1879_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_1880_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_1888_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1882_ = v_opts_932_;
v_isShared_1883_ = v_isSharedCheck_1888_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1880_);
lean_inc(v_incrLoadFileName_x3f_1879_);
lean_inc(v_incrSaveFileName_x3f_1878_);
lean_inc(v_errorOnKinds_1876_);
lean_inc(v_bcFileName_x3f_1874_);
lean_inc(v_cFileName_x3f_1873_);
lean_inc(v_ileanFileName_x3f_1872_);
lean_inc(v_oleanFileName_x3f_1871_);
lean_inc(v_setupFileName_x3f_1870_);
lean_inc(v_rootDir_x3f_1869_);
lean_inc(v_opts_1866_);
lean_inc(v_forwardedArgs_1858_);
lean_inc(v_leanOpts_1857_);
lean_dec(v_opts_932_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1888_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_leanOpts_1857_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v_forwardedArgs_1858_);
lean_ctor_set(v_reuseFailAlloc_1887_, 2, v_opts_1866_);
lean_ctor_set(v_reuseFailAlloc_1887_, 3, v_rootDir_x3f_1869_);
lean_ctor_set(v_reuseFailAlloc_1887_, 4, v_setupFileName_x3f_1870_);
lean_ctor_set(v_reuseFailAlloc_1887_, 5, v_oleanFileName_x3f_1871_);
lean_ctor_set(v_reuseFailAlloc_1887_, 6, v_ileanFileName_x3f_1872_);
lean_ctor_set(v_reuseFailAlloc_1887_, 7, v_cFileName_x3f_1873_);
lean_ctor_set(v_reuseFailAlloc_1887_, 8, v_bcFileName_x3f_1874_);
lean_ctor_set(v_reuseFailAlloc_1887_, 9, v_errorOnKinds_1876_);
lean_ctor_set(v_reuseFailAlloc_1887_, 10, v_incrSaveFileName_x3f_1878_);
lean_ctor_set(v_reuseFailAlloc_1887_, 11, v_incrLoadFileName_x3f_1879_);
lean_ctor_set(v_reuseFailAlloc_1887_, 12, v_incrHeaderSaveFileName_x3f_1880_);
lean_ctor_set_uint8(v_reuseFailAlloc_1887_, sizeof(void*)*13 + 8, v_component_1859_);
lean_ctor_set_uint8(v_reuseFailAlloc_1887_, sizeof(void*)*13 + 9, v_printPrefix_1860_);
lean_ctor_set_uint8(v_reuseFailAlloc_1887_, sizeof(void*)*13 + 10, v_printLibDir_1861_);
lean_ctor_set_uint8(v_reuseFailAlloc_1887_, sizeof(void*)*13 + 11, v_useStdin_1862_);
lean_ctor_set_uint8(v_reuseFailAlloc_1887_, sizeof(void*)*13 + 12, v_onlyDeps_1863_);
lean_ctor_set_uint8(v_reuseFailAlloc_1887_, sizeof(void*)*13 + 13, v_onlySrcDeps_1864_);
lean_ctor_set_uint8(v_reuseFailAlloc_1887_, sizeof(void*)*13 + 14, v_depsJson_1865_);
lean_ctor_set_uint32(v_reuseFailAlloc_1887_, sizeof(void*)*13, v_trustLevel_1867_);
lean_ctor_set_uint32(v_reuseFailAlloc_1887_, sizeof(void*)*13 + 4, v_numThreads_1868_);
lean_ctor_set_uint8(v_reuseFailAlloc_1887_, sizeof(void*)*13 + 15, v_jsonOutput_1875_);
lean_ctor_set_uint8(v_reuseFailAlloc_1887_, sizeof(void*)*13 + 17, v_run_1877_);
v___x_1885_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1886_; 
lean_ctor_set_uint8(v___x_1885_, sizeof(void*)*13 + 16, v___x_1201_);
v___x_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
return v___x_1886_;
}
}
}
}
else
{
lean_object* v_leanOpts_1889_; lean_object* v_forwardedArgs_1890_; uint8_t v_component_1891_; uint8_t v_printPrefix_1892_; uint8_t v_printLibDir_1893_; uint8_t v_useStdin_1894_; uint8_t v_onlyDeps_1895_; uint8_t v_onlySrcDeps_1896_; uint8_t v_depsJson_1897_; lean_object* v_opts_1898_; uint32_t v_trustLevel_1899_; uint32_t v_numThreads_1900_; lean_object* v_rootDir_x3f_1901_; lean_object* v_setupFileName_x3f_1902_; lean_object* v_oleanFileName_x3f_1903_; lean_object* v_ileanFileName_x3f_1904_; lean_object* v_cFileName_x3f_1905_; lean_object* v_bcFileName_x3f_1906_; lean_object* v_errorOnKinds_1907_; uint8_t v_printStats_1908_; uint8_t v_run_1909_; lean_object* v_incrSaveFileName_x3f_1910_; lean_object* v_incrLoadFileName_x3f_1911_; lean_object* v_incrHeaderSaveFileName_x3f_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1920_; 
lean_dec(v_optArg_x3f_934_);
v_leanOpts_1889_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_1890_ = lean_ctor_get(v_opts_932_, 1);
v_component_1891_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_1892_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_1893_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_1894_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_1895_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1896_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_1897_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_1898_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_1899_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_1900_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1901_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_1902_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_1903_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_1904_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_1905_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_1906_ = lean_ctor_get(v_opts_932_, 8);
v_errorOnKinds_1907_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_1908_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_1909_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1910_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_1911_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_1912_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1914_ = v_opts_932_;
v_isShared_1915_ = v_isSharedCheck_1920_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1912_);
lean_inc(v_incrLoadFileName_x3f_1911_);
lean_inc(v_incrSaveFileName_x3f_1910_);
lean_inc(v_errorOnKinds_1907_);
lean_inc(v_bcFileName_x3f_1906_);
lean_inc(v_cFileName_x3f_1905_);
lean_inc(v_ileanFileName_x3f_1904_);
lean_inc(v_oleanFileName_x3f_1903_);
lean_inc(v_setupFileName_x3f_1902_);
lean_inc(v_rootDir_x3f_1901_);
lean_inc(v_opts_1898_);
lean_inc(v_forwardedArgs_1890_);
lean_inc(v_leanOpts_1889_);
lean_dec(v_opts_932_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1920_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_leanOpts_1889_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_forwardedArgs_1890_);
lean_ctor_set(v_reuseFailAlloc_1919_, 2, v_opts_1898_);
lean_ctor_set(v_reuseFailAlloc_1919_, 3, v_rootDir_x3f_1901_);
lean_ctor_set(v_reuseFailAlloc_1919_, 4, v_setupFileName_x3f_1902_);
lean_ctor_set(v_reuseFailAlloc_1919_, 5, v_oleanFileName_x3f_1903_);
lean_ctor_set(v_reuseFailAlloc_1919_, 6, v_ileanFileName_x3f_1904_);
lean_ctor_set(v_reuseFailAlloc_1919_, 7, v_cFileName_x3f_1905_);
lean_ctor_set(v_reuseFailAlloc_1919_, 8, v_bcFileName_x3f_1906_);
lean_ctor_set(v_reuseFailAlloc_1919_, 9, v_errorOnKinds_1907_);
lean_ctor_set(v_reuseFailAlloc_1919_, 10, v_incrSaveFileName_x3f_1910_);
lean_ctor_set(v_reuseFailAlloc_1919_, 11, v_incrLoadFileName_x3f_1911_);
lean_ctor_set(v_reuseFailAlloc_1919_, 12, v_incrHeaderSaveFileName_x3f_1912_);
lean_ctor_set_uint8(v_reuseFailAlloc_1919_, sizeof(void*)*13 + 8, v_component_1891_);
lean_ctor_set_uint8(v_reuseFailAlloc_1919_, sizeof(void*)*13 + 9, v_printPrefix_1892_);
lean_ctor_set_uint8(v_reuseFailAlloc_1919_, sizeof(void*)*13 + 10, v_printLibDir_1893_);
lean_ctor_set_uint8(v_reuseFailAlloc_1919_, sizeof(void*)*13 + 11, v_useStdin_1894_);
lean_ctor_set_uint8(v_reuseFailAlloc_1919_, sizeof(void*)*13 + 12, v_onlyDeps_1895_);
lean_ctor_set_uint8(v_reuseFailAlloc_1919_, sizeof(void*)*13 + 13, v_onlySrcDeps_1896_);
lean_ctor_set_uint8(v_reuseFailAlloc_1919_, sizeof(void*)*13 + 14, v_depsJson_1897_);
lean_ctor_set_uint32(v_reuseFailAlloc_1919_, sizeof(void*)*13, v_trustLevel_1899_);
lean_ctor_set_uint32(v_reuseFailAlloc_1919_, sizeof(void*)*13 + 4, v_numThreads_1900_);
lean_ctor_set_uint8(v_reuseFailAlloc_1919_, sizeof(void*)*13 + 16, v_printStats_1908_);
lean_ctor_set_uint8(v_reuseFailAlloc_1919_, sizeof(void*)*13 + 17, v_run_1909_);
v___x_1917_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
lean_object* v___x_1918_; 
lean_ctor_set_uint8(v___x_1917_, sizeof(void*)*13 + 15, v___x_1199_);
v___x_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1917_);
return v___x_1918_;
}
}
}
}
else
{
lean_object* v_leanOpts_1921_; lean_object* v_forwardedArgs_1922_; uint8_t v_component_1923_; uint8_t v_printPrefix_1924_; uint8_t v_printLibDir_1925_; uint8_t v_useStdin_1926_; uint8_t v_onlySrcDeps_1927_; lean_object* v_opts_1928_; uint32_t v_trustLevel_1929_; uint32_t v_numThreads_1930_; lean_object* v_rootDir_x3f_1931_; lean_object* v_setupFileName_x3f_1932_; lean_object* v_oleanFileName_x3f_1933_; lean_object* v_ileanFileName_x3f_1934_; lean_object* v_cFileName_x3f_1935_; lean_object* v_bcFileName_x3f_1936_; uint8_t v_jsonOutput_1937_; lean_object* v_errorOnKinds_1938_; uint8_t v_printStats_1939_; uint8_t v_run_1940_; lean_object* v_incrSaveFileName_x3f_1941_; lean_object* v_incrLoadFileName_x3f_1942_; lean_object* v_incrHeaderSaveFileName_x3f_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1951_; 
lean_dec(v_optArg_x3f_934_);
v_leanOpts_1921_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_1922_ = lean_ctor_get(v_opts_932_, 1);
v_component_1923_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_1924_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_1925_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_1926_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlySrcDeps_1927_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_opts_1928_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_1929_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_1930_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1931_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_1932_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_1933_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_1934_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_1935_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_1936_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_1937_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_1938_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_1939_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_1940_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1941_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_1942_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_1943_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1945_ = v_opts_932_;
v_isShared_1946_ = v_isSharedCheck_1951_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1943_);
lean_inc(v_incrLoadFileName_x3f_1942_);
lean_inc(v_incrSaveFileName_x3f_1941_);
lean_inc(v_errorOnKinds_1938_);
lean_inc(v_bcFileName_x3f_1936_);
lean_inc(v_cFileName_x3f_1935_);
lean_inc(v_ileanFileName_x3f_1934_);
lean_inc(v_oleanFileName_x3f_1933_);
lean_inc(v_setupFileName_x3f_1932_);
lean_inc(v_rootDir_x3f_1931_);
lean_inc(v_opts_1928_);
lean_inc(v_forwardedArgs_1922_);
lean_inc(v_leanOpts_1921_);
lean_dec(v_opts_932_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1951_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_leanOpts_1921_);
lean_ctor_set(v_reuseFailAlloc_1950_, 1, v_forwardedArgs_1922_);
lean_ctor_set(v_reuseFailAlloc_1950_, 2, v_opts_1928_);
lean_ctor_set(v_reuseFailAlloc_1950_, 3, v_rootDir_x3f_1931_);
lean_ctor_set(v_reuseFailAlloc_1950_, 4, v_setupFileName_x3f_1932_);
lean_ctor_set(v_reuseFailAlloc_1950_, 5, v_oleanFileName_x3f_1933_);
lean_ctor_set(v_reuseFailAlloc_1950_, 6, v_ileanFileName_x3f_1934_);
lean_ctor_set(v_reuseFailAlloc_1950_, 7, v_cFileName_x3f_1935_);
lean_ctor_set(v_reuseFailAlloc_1950_, 8, v_bcFileName_x3f_1936_);
lean_ctor_set(v_reuseFailAlloc_1950_, 9, v_errorOnKinds_1938_);
lean_ctor_set(v_reuseFailAlloc_1950_, 10, v_incrSaveFileName_x3f_1941_);
lean_ctor_set(v_reuseFailAlloc_1950_, 11, v_incrLoadFileName_x3f_1942_);
lean_ctor_set(v_reuseFailAlloc_1950_, 12, v_incrHeaderSaveFileName_x3f_1943_);
lean_ctor_set_uint8(v_reuseFailAlloc_1950_, sizeof(void*)*13 + 8, v_component_1923_);
lean_ctor_set_uint8(v_reuseFailAlloc_1950_, sizeof(void*)*13 + 9, v_printPrefix_1924_);
lean_ctor_set_uint8(v_reuseFailAlloc_1950_, sizeof(void*)*13 + 10, v_printLibDir_1925_);
lean_ctor_set_uint8(v_reuseFailAlloc_1950_, sizeof(void*)*13 + 11, v_useStdin_1926_);
lean_ctor_set_uint8(v_reuseFailAlloc_1950_, sizeof(void*)*13 + 13, v_onlySrcDeps_1927_);
lean_ctor_set_uint32(v_reuseFailAlloc_1950_, sizeof(void*)*13, v_trustLevel_1929_);
lean_ctor_set_uint32(v_reuseFailAlloc_1950_, sizeof(void*)*13 + 4, v_numThreads_1930_);
lean_ctor_set_uint8(v_reuseFailAlloc_1950_, sizeof(void*)*13 + 15, v_jsonOutput_1937_);
lean_ctor_set_uint8(v_reuseFailAlloc_1950_, sizeof(void*)*13 + 16, v_printStats_1939_);
lean_ctor_set_uint8(v_reuseFailAlloc_1950_, sizeof(void*)*13 + 17, v_run_1940_);
v___x_1948_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
lean_object* v___x_1949_; 
lean_ctor_set_uint8(v___x_1948_, sizeof(void*)*13 + 12, v___x_1197_);
lean_ctor_set_uint8(v___x_1948_, sizeof(void*)*13 + 14, v___x_1197_);
v___x_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
return v___x_1949_;
}
}
}
}
else
{
lean_object* v_leanOpts_1952_; lean_object* v_forwardedArgs_1953_; uint8_t v_component_1954_; uint8_t v_printPrefix_1955_; uint8_t v_printLibDir_1956_; uint8_t v_useStdin_1957_; uint8_t v_onlyDeps_1958_; uint8_t v_depsJson_1959_; lean_object* v_opts_1960_; uint32_t v_trustLevel_1961_; uint32_t v_numThreads_1962_; lean_object* v_rootDir_x3f_1963_; lean_object* v_setupFileName_x3f_1964_; lean_object* v_oleanFileName_x3f_1965_; lean_object* v_ileanFileName_x3f_1966_; lean_object* v_cFileName_x3f_1967_; lean_object* v_bcFileName_x3f_1968_; uint8_t v_jsonOutput_1969_; lean_object* v_errorOnKinds_1970_; uint8_t v_printStats_1971_; uint8_t v_run_1972_; lean_object* v_incrSaveFileName_x3f_1973_; lean_object* v_incrLoadFileName_x3f_1974_; lean_object* v_incrHeaderSaveFileName_x3f_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1983_; 
lean_dec(v_optArg_x3f_934_);
v_leanOpts_1952_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_1953_ = lean_ctor_get(v_opts_932_, 1);
v_component_1954_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_1955_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_1956_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_1957_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_1958_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_depsJson_1959_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_1960_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_1961_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_1962_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1963_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_1964_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_1965_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_1966_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_1967_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_1968_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_1969_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_1970_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_1971_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_1972_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1973_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_1974_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_1975_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1977_ = v_opts_932_;
v_isShared_1978_ = v_isSharedCheck_1983_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1975_);
lean_inc(v_incrLoadFileName_x3f_1974_);
lean_inc(v_incrSaveFileName_x3f_1973_);
lean_inc(v_errorOnKinds_1970_);
lean_inc(v_bcFileName_x3f_1968_);
lean_inc(v_cFileName_x3f_1967_);
lean_inc(v_ileanFileName_x3f_1966_);
lean_inc(v_oleanFileName_x3f_1965_);
lean_inc(v_setupFileName_x3f_1964_);
lean_inc(v_rootDir_x3f_1963_);
lean_inc(v_opts_1960_);
lean_inc(v_forwardedArgs_1953_);
lean_inc(v_leanOpts_1952_);
lean_dec(v_opts_932_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1983_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_leanOpts_1952_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_forwardedArgs_1953_);
lean_ctor_set(v_reuseFailAlloc_1982_, 2, v_opts_1960_);
lean_ctor_set(v_reuseFailAlloc_1982_, 3, v_rootDir_x3f_1963_);
lean_ctor_set(v_reuseFailAlloc_1982_, 4, v_setupFileName_x3f_1964_);
lean_ctor_set(v_reuseFailAlloc_1982_, 5, v_oleanFileName_x3f_1965_);
lean_ctor_set(v_reuseFailAlloc_1982_, 6, v_ileanFileName_x3f_1966_);
lean_ctor_set(v_reuseFailAlloc_1982_, 7, v_cFileName_x3f_1967_);
lean_ctor_set(v_reuseFailAlloc_1982_, 8, v_bcFileName_x3f_1968_);
lean_ctor_set(v_reuseFailAlloc_1982_, 9, v_errorOnKinds_1970_);
lean_ctor_set(v_reuseFailAlloc_1982_, 10, v_incrSaveFileName_x3f_1973_);
lean_ctor_set(v_reuseFailAlloc_1982_, 11, v_incrLoadFileName_x3f_1974_);
lean_ctor_set(v_reuseFailAlloc_1982_, 12, v_incrHeaderSaveFileName_x3f_1975_);
lean_ctor_set_uint8(v_reuseFailAlloc_1982_, sizeof(void*)*13 + 8, v_component_1954_);
lean_ctor_set_uint8(v_reuseFailAlloc_1982_, sizeof(void*)*13 + 9, v_printPrefix_1955_);
lean_ctor_set_uint8(v_reuseFailAlloc_1982_, sizeof(void*)*13 + 10, v_printLibDir_1956_);
lean_ctor_set_uint8(v_reuseFailAlloc_1982_, sizeof(void*)*13 + 11, v_useStdin_1957_);
lean_ctor_set_uint8(v_reuseFailAlloc_1982_, sizeof(void*)*13 + 12, v_onlyDeps_1958_);
lean_ctor_set_uint8(v_reuseFailAlloc_1982_, sizeof(void*)*13 + 14, v_depsJson_1959_);
lean_ctor_set_uint32(v_reuseFailAlloc_1982_, sizeof(void*)*13, v_trustLevel_1961_);
lean_ctor_set_uint32(v_reuseFailAlloc_1982_, sizeof(void*)*13 + 4, v_numThreads_1962_);
lean_ctor_set_uint8(v_reuseFailAlloc_1982_, sizeof(void*)*13 + 15, v_jsonOutput_1969_);
lean_ctor_set_uint8(v_reuseFailAlloc_1982_, sizeof(void*)*13 + 16, v_printStats_1971_);
lean_ctor_set_uint8(v_reuseFailAlloc_1982_, sizeof(void*)*13 + 17, v_run_1972_);
v___x_1980_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
lean_object* v___x_1981_; 
lean_ctor_set_uint8(v___x_1980_, sizeof(void*)*13 + 13, v___x_1195_);
v___x_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
return v___x_1981_;
}
}
}
}
else
{
lean_object* v_leanOpts_1984_; lean_object* v_forwardedArgs_1985_; uint8_t v_component_1986_; uint8_t v_printPrefix_1987_; uint8_t v_printLibDir_1988_; uint8_t v_useStdin_1989_; uint8_t v_onlySrcDeps_1990_; uint8_t v_depsJson_1991_; lean_object* v_opts_1992_; uint32_t v_trustLevel_1993_; uint32_t v_numThreads_1994_; lean_object* v_rootDir_x3f_1995_; lean_object* v_setupFileName_x3f_1996_; lean_object* v_oleanFileName_x3f_1997_; lean_object* v_ileanFileName_x3f_1998_; lean_object* v_cFileName_x3f_1999_; lean_object* v_bcFileName_x3f_2000_; uint8_t v_jsonOutput_2001_; lean_object* v_errorOnKinds_2002_; uint8_t v_printStats_2003_; uint8_t v_run_2004_; lean_object* v_incrSaveFileName_x3f_2005_; lean_object* v_incrLoadFileName_x3f_2006_; lean_object* v_incrHeaderSaveFileName_x3f_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2015_; 
lean_dec(v_optArg_x3f_934_);
v_leanOpts_1984_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_1985_ = lean_ctor_get(v_opts_932_, 1);
v_component_1986_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_1987_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_1988_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_1989_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlySrcDeps_1990_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_1991_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_1992_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_1993_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_1994_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1995_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_1996_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_1997_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_1998_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_1999_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_2000_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_2001_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_2002_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_2003_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_2004_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2005_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_2006_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_2007_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2009_ = v_opts_932_;
v_isShared_2010_ = v_isSharedCheck_2015_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2007_);
lean_inc(v_incrLoadFileName_x3f_2006_);
lean_inc(v_incrSaveFileName_x3f_2005_);
lean_inc(v_errorOnKinds_2002_);
lean_inc(v_bcFileName_x3f_2000_);
lean_inc(v_cFileName_x3f_1999_);
lean_inc(v_ileanFileName_x3f_1998_);
lean_inc(v_oleanFileName_x3f_1997_);
lean_inc(v_setupFileName_x3f_1996_);
lean_inc(v_rootDir_x3f_1995_);
lean_inc(v_opts_1992_);
lean_inc(v_forwardedArgs_1985_);
lean_inc(v_leanOpts_1984_);
lean_dec(v_opts_932_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2015_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_leanOpts_1984_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_forwardedArgs_1985_);
lean_ctor_set(v_reuseFailAlloc_2014_, 2, v_opts_1992_);
lean_ctor_set(v_reuseFailAlloc_2014_, 3, v_rootDir_x3f_1995_);
lean_ctor_set(v_reuseFailAlloc_2014_, 4, v_setupFileName_x3f_1996_);
lean_ctor_set(v_reuseFailAlloc_2014_, 5, v_oleanFileName_x3f_1997_);
lean_ctor_set(v_reuseFailAlloc_2014_, 6, v_ileanFileName_x3f_1998_);
lean_ctor_set(v_reuseFailAlloc_2014_, 7, v_cFileName_x3f_1999_);
lean_ctor_set(v_reuseFailAlloc_2014_, 8, v_bcFileName_x3f_2000_);
lean_ctor_set(v_reuseFailAlloc_2014_, 9, v_errorOnKinds_2002_);
lean_ctor_set(v_reuseFailAlloc_2014_, 10, v_incrSaveFileName_x3f_2005_);
lean_ctor_set(v_reuseFailAlloc_2014_, 11, v_incrLoadFileName_x3f_2006_);
lean_ctor_set(v_reuseFailAlloc_2014_, 12, v_incrHeaderSaveFileName_x3f_2007_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*13 + 8, v_component_1986_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*13 + 9, v_printPrefix_1987_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*13 + 10, v_printLibDir_1988_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*13 + 11, v_useStdin_1989_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*13 + 13, v_onlySrcDeps_1990_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*13 + 14, v_depsJson_1991_);
lean_ctor_set_uint32(v_reuseFailAlloc_2014_, sizeof(void*)*13, v_trustLevel_1993_);
lean_ctor_set_uint32(v_reuseFailAlloc_2014_, sizeof(void*)*13 + 4, v_numThreads_1994_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*13 + 15, v_jsonOutput_2001_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*13 + 16, v_printStats_2003_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*13 + 17, v_run_2004_);
v___x_2012_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2013_; 
lean_ctor_set_uint8(v___x_2012_, sizeof(void*)*13 + 12, v___x_1193_);
v___x_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
return v___x_2013_;
}
}
}
}
else
{
lean_object* v_leanOpts_2016_; lean_object* v_forwardedArgs_2017_; uint8_t v_component_2018_; uint8_t v_printPrefix_2019_; uint8_t v_printLibDir_2020_; uint8_t v_useStdin_2021_; uint8_t v_onlyDeps_2022_; uint8_t v_onlySrcDeps_2023_; uint8_t v_depsJson_2024_; lean_object* v_opts_2025_; uint32_t v_trustLevel_2026_; uint32_t v_numThreads_2027_; lean_object* v_rootDir_x3f_2028_; lean_object* v_setupFileName_x3f_2029_; lean_object* v_oleanFileName_x3f_2030_; lean_object* v_ileanFileName_x3f_2031_; lean_object* v_cFileName_x3f_2032_; lean_object* v_bcFileName_x3f_2033_; uint8_t v_jsonOutput_2034_; lean_object* v_errorOnKinds_2035_; uint8_t v_printStats_2036_; uint8_t v_run_2037_; lean_object* v_incrSaveFileName_x3f_2038_; lean_object* v_incrLoadFileName_x3f_2039_; lean_object* v_incrHeaderSaveFileName_x3f_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2050_; 
lean_dec(v_optArg_x3f_934_);
v_leanOpts_2016_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_2017_ = lean_ctor_get(v_opts_932_, 1);
v_component_2018_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_2019_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_2020_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_2021_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_2022_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2023_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_2024_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_2025_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_2026_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_2027_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2028_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_2029_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_2030_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_2031_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_2032_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_2033_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_2034_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_2035_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_2036_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_2037_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2038_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_2039_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_2040_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2042_ = v_opts_932_;
v_isShared_2043_ = v_isSharedCheck_2050_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2040_);
lean_inc(v_incrLoadFileName_x3f_2039_);
lean_inc(v_incrSaveFileName_x3f_2038_);
lean_inc(v_errorOnKinds_2035_);
lean_inc(v_bcFileName_x3f_2033_);
lean_inc(v_cFileName_x3f_2032_);
lean_inc(v_ileanFileName_x3f_2031_);
lean_inc(v_oleanFileName_x3f_2030_);
lean_inc(v_setupFileName_x3f_2029_);
lean_inc(v_rootDir_x3f_2028_);
lean_inc(v_opts_2025_);
lean_inc(v_forwardedArgs_2017_);
lean_inc(v_leanOpts_2016_);
lean_dec(v_opts_932_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2050_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2047_; 
v___x_2044_ = l___private_Lean_Shell_0__Lean_verbose;
v___x_2045_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_2016_, v___x_2044_, v___x_1189_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2045_);
v___x_2047_ = v___x_2042_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2045_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_forwardedArgs_2017_);
lean_ctor_set(v_reuseFailAlloc_2049_, 2, v_opts_2025_);
lean_ctor_set(v_reuseFailAlloc_2049_, 3, v_rootDir_x3f_2028_);
lean_ctor_set(v_reuseFailAlloc_2049_, 4, v_setupFileName_x3f_2029_);
lean_ctor_set(v_reuseFailAlloc_2049_, 5, v_oleanFileName_x3f_2030_);
lean_ctor_set(v_reuseFailAlloc_2049_, 6, v_ileanFileName_x3f_2031_);
lean_ctor_set(v_reuseFailAlloc_2049_, 7, v_cFileName_x3f_2032_);
lean_ctor_set(v_reuseFailAlloc_2049_, 8, v_bcFileName_x3f_2033_);
lean_ctor_set(v_reuseFailAlloc_2049_, 9, v_errorOnKinds_2035_);
lean_ctor_set(v_reuseFailAlloc_2049_, 10, v_incrSaveFileName_x3f_2038_);
lean_ctor_set(v_reuseFailAlloc_2049_, 11, v_incrLoadFileName_x3f_2039_);
lean_ctor_set(v_reuseFailAlloc_2049_, 12, v_incrHeaderSaveFileName_x3f_2040_);
lean_ctor_set_uint8(v_reuseFailAlloc_2049_, sizeof(void*)*13 + 8, v_component_2018_);
lean_ctor_set_uint8(v_reuseFailAlloc_2049_, sizeof(void*)*13 + 9, v_printPrefix_2019_);
lean_ctor_set_uint8(v_reuseFailAlloc_2049_, sizeof(void*)*13 + 10, v_printLibDir_2020_);
lean_ctor_set_uint8(v_reuseFailAlloc_2049_, sizeof(void*)*13 + 11, v_useStdin_2021_);
lean_ctor_set_uint8(v_reuseFailAlloc_2049_, sizeof(void*)*13 + 12, v_onlyDeps_2022_);
lean_ctor_set_uint8(v_reuseFailAlloc_2049_, sizeof(void*)*13 + 13, v_onlySrcDeps_2023_);
lean_ctor_set_uint8(v_reuseFailAlloc_2049_, sizeof(void*)*13 + 14, v_depsJson_2024_);
lean_ctor_set_uint32(v_reuseFailAlloc_2049_, sizeof(void*)*13, v_trustLevel_2026_);
lean_ctor_set_uint32(v_reuseFailAlloc_2049_, sizeof(void*)*13 + 4, v_numThreads_2027_);
lean_ctor_set_uint8(v_reuseFailAlloc_2049_, sizeof(void*)*13 + 15, v_jsonOutput_2034_);
lean_ctor_set_uint8(v_reuseFailAlloc_2049_, sizeof(void*)*13 + 16, v_printStats_2036_);
lean_ctor_set_uint8(v_reuseFailAlloc_2049_, sizeof(void*)*13 + 17, v_run_2037_);
v___x_2047_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
lean_object* v___x_2048_; 
v___x_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
return v___x_2048_;
}
}
}
}
else
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13));
v___x_2052_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2051_, v_optArg_x3f_934_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2106_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2055_ = v___x_2052_;
v_isShared_2056_ = v_isSharedCheck_2106_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2052_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2106_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2057_ = lean_unsigned_to_nat(0u);
v___x_2058_ = lean_string_utf8_byte_size(v_a_2053_);
lean_inc(v_a_2053_);
v___x_2059_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2059_, 0, v_a_2053_);
lean_ctor_set(v___x_2059_, 1, v___x_2057_);
lean_ctor_set(v___x_2059_, 2, v___x_2058_);
v___x_2060_ = l_String_Slice_toNat_x3f(v___x_2059_);
lean_dec_ref_known(v___x_2059_, 3);
if (lean_obj_tag(v___x_2060_) == 1)
{
lean_object* v_val_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
v_val_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_val_2061_);
lean_dec_ref_known(v___x_2060_, 1);
v___x_2062_ = lean_cstr_to_nat("4294967296");
v___x_2063_ = lean_nat_dec_lt(v_val_2061_, v___x_2062_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
lean_dec(v_val_2061_);
lean_del_object(v___x_2055_);
lean_dec(v_a_2053_);
lean_dec_ref(v_opts_932_);
v___x_2064_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14));
v___x_2065_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2064_);
lean_dec_ref(v___x_2065_);
goto v___jp_1002_;
}
else
{
lean_object* v_leanOpts_2066_; lean_object* v_forwardedArgs_2067_; uint8_t v_component_2068_; uint8_t v_printPrefix_2069_; uint8_t v_printLibDir_2070_; uint8_t v_useStdin_2071_; uint8_t v_onlyDeps_2072_; uint8_t v_onlySrcDeps_2073_; uint8_t v_depsJson_2074_; lean_object* v_opts_2075_; uint32_t v_numThreads_2076_; lean_object* v_rootDir_x3f_2077_; lean_object* v_setupFileName_x3f_2078_; lean_object* v_oleanFileName_x3f_2079_; lean_object* v_ileanFileName_x3f_2080_; lean_object* v_cFileName_x3f_2081_; lean_object* v_bcFileName_x3f_2082_; uint8_t v_jsonOutput_2083_; lean_object* v_errorOnKinds_2084_; uint8_t v_printStats_2085_; uint8_t v_run_2086_; lean_object* v_incrSaveFileName_x3f_2087_; lean_object* v_incrLoadFileName_x3f_2088_; lean_object* v_incrHeaderSaveFileName_x3f_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2103_; 
v_leanOpts_2066_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_2067_ = lean_ctor_get(v_opts_932_, 1);
v_component_2068_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_2069_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_2070_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_2071_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_2072_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2073_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_2074_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_2075_ = lean_ctor_get(v_opts_932_, 2);
v_numThreads_2076_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2077_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_2078_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_2079_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_2080_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_2081_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_2082_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_2083_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_2084_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_2085_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_2086_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2087_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_2088_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_2089_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2091_ = v_opts_932_;
v_isShared_2092_ = v_isSharedCheck_2103_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2089_);
lean_inc(v_incrLoadFileName_x3f_2088_);
lean_inc(v_incrSaveFileName_x3f_2087_);
lean_inc(v_errorOnKinds_2084_);
lean_inc(v_bcFileName_x3f_2082_);
lean_inc(v_cFileName_x3f_2081_);
lean_inc(v_ileanFileName_x3f_2080_);
lean_inc(v_oleanFileName_x3f_2079_);
lean_inc(v_setupFileName_x3f_2078_);
lean_inc(v_rootDir_x3f_2077_);
lean_inc(v_opts_2075_);
lean_inc(v_forwardedArgs_2067_);
lean_inc(v_leanOpts_2066_);
lean_dec(v_opts_932_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2103_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
uint32_t v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2098_; 
v___x_2093_ = lean_uint32_of_nat(v_val_2061_);
lean_dec(v_val_2061_);
v___x_2094_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15));
v___x_2095_ = lean_string_append(v___x_2094_, v_a_2053_);
lean_dec(v_a_2053_);
v___x_2096_ = lean_array_push(v_forwardedArgs_2067_, v___x_2095_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 1, v___x_2096_);
v___x_2098_ = v___x_2091_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_leanOpts_2066_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v___x_2096_);
lean_ctor_set(v_reuseFailAlloc_2102_, 2, v_opts_2075_);
lean_ctor_set(v_reuseFailAlloc_2102_, 3, v_rootDir_x3f_2077_);
lean_ctor_set(v_reuseFailAlloc_2102_, 4, v_setupFileName_x3f_2078_);
lean_ctor_set(v_reuseFailAlloc_2102_, 5, v_oleanFileName_x3f_2079_);
lean_ctor_set(v_reuseFailAlloc_2102_, 6, v_ileanFileName_x3f_2080_);
lean_ctor_set(v_reuseFailAlloc_2102_, 7, v_cFileName_x3f_2081_);
lean_ctor_set(v_reuseFailAlloc_2102_, 8, v_bcFileName_x3f_2082_);
lean_ctor_set(v_reuseFailAlloc_2102_, 9, v_errorOnKinds_2084_);
lean_ctor_set(v_reuseFailAlloc_2102_, 10, v_incrSaveFileName_x3f_2087_);
lean_ctor_set(v_reuseFailAlloc_2102_, 11, v_incrLoadFileName_x3f_2088_);
lean_ctor_set(v_reuseFailAlloc_2102_, 12, v_incrHeaderSaveFileName_x3f_2089_);
lean_ctor_set_uint8(v_reuseFailAlloc_2102_, sizeof(void*)*13 + 8, v_component_2068_);
lean_ctor_set_uint8(v_reuseFailAlloc_2102_, sizeof(void*)*13 + 9, v_printPrefix_2069_);
lean_ctor_set_uint8(v_reuseFailAlloc_2102_, sizeof(void*)*13 + 10, v_printLibDir_2070_);
lean_ctor_set_uint8(v_reuseFailAlloc_2102_, sizeof(void*)*13 + 11, v_useStdin_2071_);
lean_ctor_set_uint8(v_reuseFailAlloc_2102_, sizeof(void*)*13 + 12, v_onlyDeps_2072_);
lean_ctor_set_uint8(v_reuseFailAlloc_2102_, sizeof(void*)*13 + 13, v_onlySrcDeps_2073_);
lean_ctor_set_uint8(v_reuseFailAlloc_2102_, sizeof(void*)*13 + 14, v_depsJson_2074_);
lean_ctor_set_uint32(v_reuseFailAlloc_2102_, sizeof(void*)*13 + 4, v_numThreads_2076_);
lean_ctor_set_uint8(v_reuseFailAlloc_2102_, sizeof(void*)*13 + 15, v_jsonOutput_2083_);
lean_ctor_set_uint8(v_reuseFailAlloc_2102_, sizeof(void*)*13 + 16, v_printStats_2085_);
lean_ctor_set_uint8(v_reuseFailAlloc_2102_, sizeof(void*)*13 + 17, v_run_2086_);
v___x_2098_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2100_; 
lean_ctor_set_uint32(v___x_2098_, sizeof(void*)*13, v___x_2093_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 0, v___x_2098_);
v___x_2100_ = v___x_2055_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2098_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
}
else
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
lean_dec(v___x_2060_);
lean_del_object(v___x_2055_);
lean_dec(v_a_2053_);
lean_dec_ref(v_opts_932_);
v___x_2104_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16));
v___x_2105_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2104_);
lean_dec_ref(v___x_2105_);
goto v___jp_999_;
}
}
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
lean_dec_ref(v_opts_932_);
v_a_2107_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2107_);
lean_dec_ref_known(v___x_2052_, 1);
v___x_2111_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2112_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2111_);
lean_dec_ref(v___x_2112_);
goto v___jp_2108_;
v___jp_2108_:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = lean_io_error_to_string(v_a_2107_);
v___x_2110_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2109_);
lean_dec_ref(v___x_2110_);
goto v___jp_996_;
}
}
}
}
else
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17));
v___x_2114_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2113_, v_optArg_x3f_934_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2166_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2117_ = v___x_2114_;
v_isShared_2118_ = v_isSharedCheck_2166_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2114_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2166_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2119_ = lean_unsigned_to_nat(0u);
v___x_2120_ = lean_string_utf8_byte_size(v_a_2115_);
lean_inc(v_a_2115_);
v___x_2121_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2121_, 0, v_a_2115_);
lean_ctor_set(v___x_2121_, 1, v___x_2119_);
lean_ctor_set(v___x_2121_, 2, v___x_2120_);
v___x_2122_ = l_String_Slice_toNat_x3f(v___x_2121_);
lean_dec_ref_known(v___x_2121_, 3);
if (lean_obj_tag(v___x_2122_) == 1)
{
lean_object* v_val_2123_; lean_object* v_leanOpts_2124_; lean_object* v_forwardedArgs_2125_; uint8_t v_component_2126_; uint8_t v_printPrefix_2127_; uint8_t v_printLibDir_2128_; uint8_t v_useStdin_2129_; uint8_t v_onlyDeps_2130_; uint8_t v_onlySrcDeps_2131_; uint8_t v_depsJson_2132_; lean_object* v_opts_2133_; uint32_t v_trustLevel_2134_; uint32_t v_numThreads_2135_; lean_object* v_rootDir_x3f_2136_; lean_object* v_setupFileName_x3f_2137_; lean_object* v_oleanFileName_x3f_2138_; lean_object* v_ileanFileName_x3f_2139_; lean_object* v_cFileName_x3f_2140_; lean_object* v_bcFileName_x3f_2141_; uint8_t v_jsonOutput_2142_; lean_object* v_errorOnKinds_2143_; uint8_t v_printStats_2144_; uint8_t v_run_2145_; lean_object* v_incrSaveFileName_x3f_2146_; lean_object* v_incrLoadFileName_x3f_2147_; lean_object* v_incrHeaderSaveFileName_x3f_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2163_; 
v_val_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_val_2123_);
lean_dec_ref_known(v___x_2122_, 1);
v_leanOpts_2124_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_2125_ = lean_ctor_get(v_opts_932_, 1);
v_component_2126_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_2127_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_2128_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_2129_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_2130_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2131_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_2132_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_2133_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_2134_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_2135_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2136_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_2137_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_2138_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_2139_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_2140_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_2141_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_2142_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_2143_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_2144_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_2145_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2146_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_2147_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_2148_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2150_ = v_opts_932_;
v_isShared_2151_ = v_isSharedCheck_2163_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2148_);
lean_inc(v_incrLoadFileName_x3f_2147_);
lean_inc(v_incrSaveFileName_x3f_2146_);
lean_inc(v_errorOnKinds_2143_);
lean_inc(v_bcFileName_x3f_2141_);
lean_inc(v_cFileName_x3f_2140_);
lean_inc(v_ileanFileName_x3f_2139_);
lean_inc(v_oleanFileName_x3f_2138_);
lean_inc(v_setupFileName_x3f_2137_);
lean_inc(v_rootDir_x3f_2136_);
lean_inc(v_opts_2133_);
lean_inc(v_forwardedArgs_2125_);
lean_inc(v_leanOpts_2124_);
lean_dec(v_opts_932_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2163_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2158_; 
v___x_2152_ = l___private_Lean_Shell_0__Lean_timeout;
v___x_2153_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_2124_, v___x_2152_, v_val_2123_);
v___x_2154_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18));
v___x_2155_ = lean_string_append(v___x_2154_, v_a_2115_);
lean_dec(v_a_2115_);
v___x_2156_ = lean_array_push(v_forwardedArgs_2125_, v___x_2155_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 1, v___x_2156_);
lean_ctor_set(v___x_2150_, 0, v___x_2153_);
v___x_2158_ = v___x_2150_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2153_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2162_, 2, v_opts_2133_);
lean_ctor_set(v_reuseFailAlloc_2162_, 3, v_rootDir_x3f_2136_);
lean_ctor_set(v_reuseFailAlloc_2162_, 4, v_setupFileName_x3f_2137_);
lean_ctor_set(v_reuseFailAlloc_2162_, 5, v_oleanFileName_x3f_2138_);
lean_ctor_set(v_reuseFailAlloc_2162_, 6, v_ileanFileName_x3f_2139_);
lean_ctor_set(v_reuseFailAlloc_2162_, 7, v_cFileName_x3f_2140_);
lean_ctor_set(v_reuseFailAlloc_2162_, 8, v_bcFileName_x3f_2141_);
lean_ctor_set(v_reuseFailAlloc_2162_, 9, v_errorOnKinds_2143_);
lean_ctor_set(v_reuseFailAlloc_2162_, 10, v_incrSaveFileName_x3f_2146_);
lean_ctor_set(v_reuseFailAlloc_2162_, 11, v_incrLoadFileName_x3f_2147_);
lean_ctor_set(v_reuseFailAlloc_2162_, 12, v_incrHeaderSaveFileName_x3f_2148_);
lean_ctor_set_uint8(v_reuseFailAlloc_2162_, sizeof(void*)*13 + 8, v_component_2126_);
lean_ctor_set_uint8(v_reuseFailAlloc_2162_, sizeof(void*)*13 + 9, v_printPrefix_2127_);
lean_ctor_set_uint8(v_reuseFailAlloc_2162_, sizeof(void*)*13 + 10, v_printLibDir_2128_);
lean_ctor_set_uint8(v_reuseFailAlloc_2162_, sizeof(void*)*13 + 11, v_useStdin_2129_);
lean_ctor_set_uint8(v_reuseFailAlloc_2162_, sizeof(void*)*13 + 12, v_onlyDeps_2130_);
lean_ctor_set_uint8(v_reuseFailAlloc_2162_, sizeof(void*)*13 + 13, v_onlySrcDeps_2131_);
lean_ctor_set_uint8(v_reuseFailAlloc_2162_, sizeof(void*)*13 + 14, v_depsJson_2132_);
lean_ctor_set_uint32(v_reuseFailAlloc_2162_, sizeof(void*)*13, v_trustLevel_2134_);
lean_ctor_set_uint32(v_reuseFailAlloc_2162_, sizeof(void*)*13 + 4, v_numThreads_2135_);
lean_ctor_set_uint8(v_reuseFailAlloc_2162_, sizeof(void*)*13 + 15, v_jsonOutput_2142_);
lean_ctor_set_uint8(v_reuseFailAlloc_2162_, sizeof(void*)*13 + 16, v_printStats_2144_);
lean_ctor_set_uint8(v_reuseFailAlloc_2162_, sizeof(void*)*13 + 17, v_run_2145_);
v___x_2158_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2160_; 
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 0, v___x_2158_);
v___x_2160_ = v___x_2117_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
else
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
lean_dec(v___x_2122_);
lean_del_object(v___x_2117_);
lean_dec(v_a_2115_);
lean_dec_ref(v_opts_932_);
v___x_2164_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19));
v___x_2165_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2164_);
lean_dec_ref(v___x_2165_);
goto v___jp_1109_;
}
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
lean_dec_ref(v_opts_932_);
v_a_2167_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2167_);
lean_dec_ref_known(v___x_2114_, 1);
v___x_2171_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2172_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2171_);
lean_dec_ref(v___x_2172_);
goto v___jp_2168_;
v___jp_2168_:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2169_ = lean_io_error_to_string(v_a_2167_);
v___x_2170_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2169_);
lean_dec_ref(v___x_2170_);
goto v___jp_1115_;
}
}
}
}
else
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20));
v___x_2174_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2173_, v_optArg_x3f_934_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2226_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2177_ = v___x_2174_;
v_isShared_2178_ = v_isSharedCheck_2226_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2174_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2226_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2179_ = lean_unsigned_to_nat(0u);
v___x_2180_ = lean_string_utf8_byte_size(v_a_2175_);
lean_inc(v_a_2175_);
v___x_2181_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2181_, 0, v_a_2175_);
lean_ctor_set(v___x_2181_, 1, v___x_2179_);
lean_ctor_set(v___x_2181_, 2, v___x_2180_);
v___x_2182_ = l_String_Slice_toNat_x3f(v___x_2181_);
lean_dec_ref_known(v___x_2181_, 3);
if (lean_obj_tag(v___x_2182_) == 1)
{
lean_object* v_val_2183_; lean_object* v_leanOpts_2184_; lean_object* v_forwardedArgs_2185_; uint8_t v_component_2186_; uint8_t v_printPrefix_2187_; uint8_t v_printLibDir_2188_; uint8_t v_useStdin_2189_; uint8_t v_onlyDeps_2190_; uint8_t v_onlySrcDeps_2191_; uint8_t v_depsJson_2192_; lean_object* v_opts_2193_; uint32_t v_trustLevel_2194_; uint32_t v_numThreads_2195_; lean_object* v_rootDir_x3f_2196_; lean_object* v_setupFileName_x3f_2197_; lean_object* v_oleanFileName_x3f_2198_; lean_object* v_ileanFileName_x3f_2199_; lean_object* v_cFileName_x3f_2200_; lean_object* v_bcFileName_x3f_2201_; uint8_t v_jsonOutput_2202_; lean_object* v_errorOnKinds_2203_; uint8_t v_printStats_2204_; uint8_t v_run_2205_; lean_object* v_incrSaveFileName_x3f_2206_; lean_object* v_incrLoadFileName_x3f_2207_; lean_object* v_incrHeaderSaveFileName_x3f_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2223_; 
v_val_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_val_2183_);
lean_dec_ref_known(v___x_2182_, 1);
v_leanOpts_2184_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_2185_ = lean_ctor_get(v_opts_932_, 1);
v_component_2186_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_2187_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_2188_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_2189_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_2190_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2191_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_2192_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_2193_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_2194_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_2195_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2196_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_2197_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_2198_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_2199_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_2200_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_2201_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_2202_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_2203_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_2204_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_2205_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2206_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_2207_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_2208_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2210_ = v_opts_932_;
v_isShared_2211_ = v_isSharedCheck_2223_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2208_);
lean_inc(v_incrLoadFileName_x3f_2207_);
lean_inc(v_incrSaveFileName_x3f_2206_);
lean_inc(v_errorOnKinds_2203_);
lean_inc(v_bcFileName_x3f_2201_);
lean_inc(v_cFileName_x3f_2200_);
lean_inc(v_ileanFileName_x3f_2199_);
lean_inc(v_oleanFileName_x3f_2198_);
lean_inc(v_setupFileName_x3f_2197_);
lean_inc(v_rootDir_x3f_2196_);
lean_inc(v_opts_2193_);
lean_inc(v_forwardedArgs_2185_);
lean_inc(v_leanOpts_2184_);
lean_dec(v_opts_932_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2223_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2218_; 
v___x_2212_ = l___private_Lean_Shell_0__Lean_maxMemory;
v___x_2213_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_2184_, v___x_2212_, v_val_2183_);
v___x_2214_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21));
v___x_2215_ = lean_string_append(v___x_2214_, v_a_2175_);
lean_dec(v_a_2175_);
v___x_2216_ = lean_array_push(v_forwardedArgs_2185_, v___x_2215_);
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 1, v___x_2216_);
lean_ctor_set(v___x_2210_, 0, v___x_2213_);
v___x_2218_ = v___x_2210_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v___x_2216_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v_opts_2193_);
lean_ctor_set(v_reuseFailAlloc_2222_, 3, v_rootDir_x3f_2196_);
lean_ctor_set(v_reuseFailAlloc_2222_, 4, v_setupFileName_x3f_2197_);
lean_ctor_set(v_reuseFailAlloc_2222_, 5, v_oleanFileName_x3f_2198_);
lean_ctor_set(v_reuseFailAlloc_2222_, 6, v_ileanFileName_x3f_2199_);
lean_ctor_set(v_reuseFailAlloc_2222_, 7, v_cFileName_x3f_2200_);
lean_ctor_set(v_reuseFailAlloc_2222_, 8, v_bcFileName_x3f_2201_);
lean_ctor_set(v_reuseFailAlloc_2222_, 9, v_errorOnKinds_2203_);
lean_ctor_set(v_reuseFailAlloc_2222_, 10, v_incrSaveFileName_x3f_2206_);
lean_ctor_set(v_reuseFailAlloc_2222_, 11, v_incrLoadFileName_x3f_2207_);
lean_ctor_set(v_reuseFailAlloc_2222_, 12, v_incrHeaderSaveFileName_x3f_2208_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*13 + 8, v_component_2186_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*13 + 9, v_printPrefix_2187_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*13 + 10, v_printLibDir_2188_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*13 + 11, v_useStdin_2189_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*13 + 12, v_onlyDeps_2190_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*13 + 13, v_onlySrcDeps_2191_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*13 + 14, v_depsJson_2192_);
lean_ctor_set_uint32(v_reuseFailAlloc_2222_, sizeof(void*)*13, v_trustLevel_2194_);
lean_ctor_set_uint32(v_reuseFailAlloc_2222_, sizeof(void*)*13 + 4, v_numThreads_2195_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*13 + 15, v_jsonOutput_2202_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*13 + 16, v_printStats_2204_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*13 + 17, v_run_2205_);
v___x_2218_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
lean_object* v___x_2220_; 
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___x_2218_);
v___x_2220_ = v___x_2177_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
else
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
lean_dec(v___x_2182_);
lean_del_object(v___x_2177_);
lean_dec(v_a_2175_);
lean_dec_ref(v_opts_932_);
v___x_2224_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22));
v___x_2225_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2224_);
lean_dec_ref(v___x_2225_);
goto v___jp_990_;
}
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
lean_dec_ref(v_opts_932_);
v_a_2227_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2227_);
lean_dec_ref_known(v___x_2174_, 1);
v___x_2231_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2232_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2231_);
lean_dec_ref(v___x_2232_);
goto v___jp_2228_;
v___jp_2228_:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = lean_io_error_to_string(v_a_2227_);
v___x_2230_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2229_);
lean_dec_ref(v___x_2230_);
goto v___jp_987_;
}
}
}
}
else
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23));
v___x_2234_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2233_, v_optArg_x3f_934_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2278_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2237_ = v___x_2234_;
v_isShared_2238_ = v_isSharedCheck_2278_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2234_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2278_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v_leanOpts_2239_; lean_object* v_forwardedArgs_2240_; uint8_t v_component_2241_; uint8_t v_printPrefix_2242_; uint8_t v_printLibDir_2243_; uint8_t v_useStdin_2244_; uint8_t v_onlyDeps_2245_; uint8_t v_onlySrcDeps_2246_; uint8_t v_depsJson_2247_; lean_object* v_opts_2248_; uint32_t v_trustLevel_2249_; uint32_t v_numThreads_2250_; lean_object* v_setupFileName_x3f_2251_; lean_object* v_oleanFileName_x3f_2252_; lean_object* v_ileanFileName_x3f_2253_; lean_object* v_cFileName_x3f_2254_; lean_object* v_bcFileName_x3f_2255_; uint8_t v_jsonOutput_2256_; lean_object* v_errorOnKinds_2257_; uint8_t v_printStats_2258_; uint8_t v_run_2259_; lean_object* v_incrSaveFileName_x3f_2260_; lean_object* v_incrLoadFileName_x3f_2261_; lean_object* v_incrHeaderSaveFileName_x3f_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2276_; 
v_leanOpts_2239_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_2240_ = lean_ctor_get(v_opts_932_, 1);
v_component_2241_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_2242_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_2243_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_2244_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_2245_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2246_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_2247_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_2248_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_2249_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_2250_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_setupFileName_x3f_2251_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_2252_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_2253_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_2254_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_2255_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_2256_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_2257_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_2258_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_2259_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2260_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_2261_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_2262_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_2276_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_2276_ == 0)
{
lean_object* v_unused_2277_; 
v_unused_2277_ = lean_ctor_get(v_opts_932_, 3);
lean_dec(v_unused_2277_);
v___x_2264_ = v_opts_932_;
v_isShared_2265_ = v_isSharedCheck_2276_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2262_);
lean_inc(v_incrLoadFileName_x3f_2261_);
lean_inc(v_incrSaveFileName_x3f_2260_);
lean_inc(v_errorOnKinds_2257_);
lean_inc(v_bcFileName_x3f_2255_);
lean_inc(v_cFileName_x3f_2254_);
lean_inc(v_ileanFileName_x3f_2253_);
lean_inc(v_oleanFileName_x3f_2252_);
lean_inc(v_setupFileName_x3f_2251_);
lean_inc(v_opts_2248_);
lean_inc(v_forwardedArgs_2240_);
lean_inc(v_leanOpts_2239_);
lean_dec(v_opts_932_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2276_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2271_; 
v___x_2266_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24));
v___x_2267_ = lean_string_append(v___x_2266_, v_a_2235_);
v___x_2268_ = lean_array_push(v_forwardedArgs_2240_, v___x_2267_);
v___x_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2269_, 0, v_a_2235_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 3, v___x_2269_);
lean_ctor_set(v___x_2264_, 1, v___x_2268_);
v___x_2271_ = v___x_2264_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_leanOpts_2239_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v___x_2268_);
lean_ctor_set(v_reuseFailAlloc_2275_, 2, v_opts_2248_);
lean_ctor_set(v_reuseFailAlloc_2275_, 3, v___x_2269_);
lean_ctor_set(v_reuseFailAlloc_2275_, 4, v_setupFileName_x3f_2251_);
lean_ctor_set(v_reuseFailAlloc_2275_, 5, v_oleanFileName_x3f_2252_);
lean_ctor_set(v_reuseFailAlloc_2275_, 6, v_ileanFileName_x3f_2253_);
lean_ctor_set(v_reuseFailAlloc_2275_, 7, v_cFileName_x3f_2254_);
lean_ctor_set(v_reuseFailAlloc_2275_, 8, v_bcFileName_x3f_2255_);
lean_ctor_set(v_reuseFailAlloc_2275_, 9, v_errorOnKinds_2257_);
lean_ctor_set(v_reuseFailAlloc_2275_, 10, v_incrSaveFileName_x3f_2260_);
lean_ctor_set(v_reuseFailAlloc_2275_, 11, v_incrLoadFileName_x3f_2261_);
lean_ctor_set(v_reuseFailAlloc_2275_, 12, v_incrHeaderSaveFileName_x3f_2262_);
lean_ctor_set_uint8(v_reuseFailAlloc_2275_, sizeof(void*)*13 + 8, v_component_2241_);
lean_ctor_set_uint8(v_reuseFailAlloc_2275_, sizeof(void*)*13 + 9, v_printPrefix_2242_);
lean_ctor_set_uint8(v_reuseFailAlloc_2275_, sizeof(void*)*13 + 10, v_printLibDir_2243_);
lean_ctor_set_uint8(v_reuseFailAlloc_2275_, sizeof(void*)*13 + 11, v_useStdin_2244_);
lean_ctor_set_uint8(v_reuseFailAlloc_2275_, sizeof(void*)*13 + 12, v_onlyDeps_2245_);
lean_ctor_set_uint8(v_reuseFailAlloc_2275_, sizeof(void*)*13 + 13, v_onlySrcDeps_2246_);
lean_ctor_set_uint8(v_reuseFailAlloc_2275_, sizeof(void*)*13 + 14, v_depsJson_2247_);
lean_ctor_set_uint32(v_reuseFailAlloc_2275_, sizeof(void*)*13, v_trustLevel_2249_);
lean_ctor_set_uint32(v_reuseFailAlloc_2275_, sizeof(void*)*13 + 4, v_numThreads_2250_);
lean_ctor_set_uint8(v_reuseFailAlloc_2275_, sizeof(void*)*13 + 15, v_jsonOutput_2256_);
lean_ctor_set_uint8(v_reuseFailAlloc_2275_, sizeof(void*)*13 + 16, v_printStats_2258_);
lean_ctor_set_uint8(v_reuseFailAlloc_2275_, sizeof(void*)*13 + 17, v_run_2259_);
v___x_2271_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
lean_object* v___x_2273_; 
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 0, v___x_2271_);
v___x_2273_ = v___x_2237_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
lean_dec_ref(v_opts_932_);
v_a_2279_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2234_, 1);
v___x_2283_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2284_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2283_);
lean_dec_ref(v___x_2284_);
goto v___jp_2280_;
v___jp_2280_:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = lean_io_error_to_string(v_a_2279_);
v___x_2282_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2281_);
lean_dec_ref(v___x_2282_);
goto v___jp_1121_;
}
}
}
}
else
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25));
v___x_2286_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2285_, v_optArg_x3f_934_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2327_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2289_ = v___x_2286_;
v_isShared_2290_ = v_isSharedCheck_2327_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2286_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2327_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v_leanOpts_2291_; lean_object* v_forwardedArgs_2292_; uint8_t v_component_2293_; uint8_t v_printPrefix_2294_; uint8_t v_printLibDir_2295_; uint8_t v_useStdin_2296_; uint8_t v_onlyDeps_2297_; uint8_t v_onlySrcDeps_2298_; uint8_t v_depsJson_2299_; lean_object* v_opts_2300_; uint32_t v_trustLevel_2301_; uint32_t v_numThreads_2302_; lean_object* v_rootDir_x3f_2303_; lean_object* v_setupFileName_x3f_2304_; lean_object* v_oleanFileName_x3f_2305_; lean_object* v_cFileName_x3f_2306_; lean_object* v_bcFileName_x3f_2307_; uint8_t v_jsonOutput_2308_; lean_object* v_errorOnKinds_2309_; uint8_t v_printStats_2310_; uint8_t v_run_2311_; lean_object* v_incrSaveFileName_x3f_2312_; lean_object* v_incrLoadFileName_x3f_2313_; lean_object* v_incrHeaderSaveFileName_x3f_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2325_; 
v_leanOpts_2291_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_2292_ = lean_ctor_get(v_opts_932_, 1);
v_component_2293_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_2294_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_2295_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_2296_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_2297_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2298_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_2299_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_2300_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_2301_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_2302_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2303_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_2304_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_2305_ = lean_ctor_get(v_opts_932_, 5);
v_cFileName_x3f_2306_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_2307_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_2308_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_2309_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_2310_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_2311_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2312_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_2313_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_2314_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_2325_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_2325_ == 0)
{
lean_object* v_unused_2326_; 
v_unused_2326_ = lean_ctor_get(v_opts_932_, 6);
lean_dec(v_unused_2326_);
v___x_2316_ = v_opts_932_;
v_isShared_2317_ = v_isSharedCheck_2325_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2314_);
lean_inc(v_incrLoadFileName_x3f_2313_);
lean_inc(v_incrSaveFileName_x3f_2312_);
lean_inc(v_errorOnKinds_2309_);
lean_inc(v_bcFileName_x3f_2307_);
lean_inc(v_cFileName_x3f_2306_);
lean_inc(v_oleanFileName_x3f_2305_);
lean_inc(v_setupFileName_x3f_2304_);
lean_inc(v_rootDir_x3f_2303_);
lean_inc(v_opts_2300_);
lean_inc(v_forwardedArgs_2292_);
lean_inc(v_leanOpts_2291_);
lean_dec(v_opts_932_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2325_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2318_; lean_object* v___x_2320_; 
v___x_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2318_, 0, v_a_2287_);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 6, v___x_2318_);
v___x_2320_ = v___x_2316_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_leanOpts_2291_);
lean_ctor_set(v_reuseFailAlloc_2324_, 1, v_forwardedArgs_2292_);
lean_ctor_set(v_reuseFailAlloc_2324_, 2, v_opts_2300_);
lean_ctor_set(v_reuseFailAlloc_2324_, 3, v_rootDir_x3f_2303_);
lean_ctor_set(v_reuseFailAlloc_2324_, 4, v_setupFileName_x3f_2304_);
lean_ctor_set(v_reuseFailAlloc_2324_, 5, v_oleanFileName_x3f_2305_);
lean_ctor_set(v_reuseFailAlloc_2324_, 6, v___x_2318_);
lean_ctor_set(v_reuseFailAlloc_2324_, 7, v_cFileName_x3f_2306_);
lean_ctor_set(v_reuseFailAlloc_2324_, 8, v_bcFileName_x3f_2307_);
lean_ctor_set(v_reuseFailAlloc_2324_, 9, v_errorOnKinds_2309_);
lean_ctor_set(v_reuseFailAlloc_2324_, 10, v_incrSaveFileName_x3f_2312_);
lean_ctor_set(v_reuseFailAlloc_2324_, 11, v_incrLoadFileName_x3f_2313_);
lean_ctor_set(v_reuseFailAlloc_2324_, 12, v_incrHeaderSaveFileName_x3f_2314_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, sizeof(void*)*13 + 8, v_component_2293_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, sizeof(void*)*13 + 9, v_printPrefix_2294_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, sizeof(void*)*13 + 10, v_printLibDir_2295_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, sizeof(void*)*13 + 11, v_useStdin_2296_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, sizeof(void*)*13 + 12, v_onlyDeps_2297_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, sizeof(void*)*13 + 13, v_onlySrcDeps_2298_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, sizeof(void*)*13 + 14, v_depsJson_2299_);
lean_ctor_set_uint32(v_reuseFailAlloc_2324_, sizeof(void*)*13, v_trustLevel_2301_);
lean_ctor_set_uint32(v_reuseFailAlloc_2324_, sizeof(void*)*13 + 4, v_numThreads_2302_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, sizeof(void*)*13 + 15, v_jsonOutput_2308_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, sizeof(void*)*13 + 16, v_printStats_2310_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, sizeof(void*)*13 + 17, v_run_2311_);
v___x_2320_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
lean_object* v___x_2322_; 
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 0, v___x_2320_);
v___x_2322_ = v___x_2289_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v___x_2320_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
lean_dec_ref(v_opts_932_);
v_a_2328_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2328_);
lean_dec_ref_known(v___x_2286_, 1);
v___x_2332_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2333_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2332_);
lean_dec_ref(v___x_2333_);
goto v___jp_2329_;
v___jp_2329_:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2330_ = lean_io_error_to_string(v_a_2328_);
v___x_2331_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2330_);
lean_dec_ref(v___x_2331_);
goto v___jp_981_;
}
}
}
}
else
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26));
v___x_2335_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2334_, v_optArg_x3f_934_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2376_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2338_ = v___x_2335_;
v_isShared_2339_ = v_isSharedCheck_2376_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2335_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2376_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v_leanOpts_2340_; lean_object* v_forwardedArgs_2341_; uint8_t v_component_2342_; uint8_t v_printPrefix_2343_; uint8_t v_printLibDir_2344_; uint8_t v_useStdin_2345_; uint8_t v_onlyDeps_2346_; uint8_t v_onlySrcDeps_2347_; uint8_t v_depsJson_2348_; lean_object* v_opts_2349_; uint32_t v_trustLevel_2350_; uint32_t v_numThreads_2351_; lean_object* v_rootDir_x3f_2352_; lean_object* v_setupFileName_x3f_2353_; lean_object* v_ileanFileName_x3f_2354_; lean_object* v_cFileName_x3f_2355_; lean_object* v_bcFileName_x3f_2356_; uint8_t v_jsonOutput_2357_; lean_object* v_errorOnKinds_2358_; uint8_t v_printStats_2359_; uint8_t v_run_2360_; lean_object* v_incrSaveFileName_x3f_2361_; lean_object* v_incrLoadFileName_x3f_2362_; lean_object* v_incrHeaderSaveFileName_x3f_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2374_; 
v_leanOpts_2340_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_2341_ = lean_ctor_get(v_opts_932_, 1);
v_component_2342_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_2343_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_2344_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_2345_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_2346_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2347_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_2348_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_2349_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_2350_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_2351_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2352_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_2353_ = lean_ctor_get(v_opts_932_, 4);
v_ileanFileName_x3f_2354_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_2355_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_2356_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_2357_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_2358_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_2359_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_2360_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2361_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_2362_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_2363_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_2374_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_2374_ == 0)
{
lean_object* v_unused_2375_; 
v_unused_2375_ = lean_ctor_get(v_opts_932_, 5);
lean_dec(v_unused_2375_);
v___x_2365_ = v_opts_932_;
v_isShared_2366_ = v_isSharedCheck_2374_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2363_);
lean_inc(v_incrLoadFileName_x3f_2362_);
lean_inc(v_incrSaveFileName_x3f_2361_);
lean_inc(v_errorOnKinds_2358_);
lean_inc(v_bcFileName_x3f_2356_);
lean_inc(v_cFileName_x3f_2355_);
lean_inc(v_ileanFileName_x3f_2354_);
lean_inc(v_setupFileName_x3f_2353_);
lean_inc(v_rootDir_x3f_2352_);
lean_inc(v_opts_2349_);
lean_inc(v_forwardedArgs_2341_);
lean_inc(v_leanOpts_2340_);
lean_dec(v_opts_932_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2374_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2367_, 0, v_a_2336_);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 5, v___x_2367_);
v___x_2369_ = v___x_2365_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_leanOpts_2340_);
lean_ctor_set(v_reuseFailAlloc_2373_, 1, v_forwardedArgs_2341_);
lean_ctor_set(v_reuseFailAlloc_2373_, 2, v_opts_2349_);
lean_ctor_set(v_reuseFailAlloc_2373_, 3, v_rootDir_x3f_2352_);
lean_ctor_set(v_reuseFailAlloc_2373_, 4, v_setupFileName_x3f_2353_);
lean_ctor_set(v_reuseFailAlloc_2373_, 5, v___x_2367_);
lean_ctor_set(v_reuseFailAlloc_2373_, 6, v_ileanFileName_x3f_2354_);
lean_ctor_set(v_reuseFailAlloc_2373_, 7, v_cFileName_x3f_2355_);
lean_ctor_set(v_reuseFailAlloc_2373_, 8, v_bcFileName_x3f_2356_);
lean_ctor_set(v_reuseFailAlloc_2373_, 9, v_errorOnKinds_2358_);
lean_ctor_set(v_reuseFailAlloc_2373_, 10, v_incrSaveFileName_x3f_2361_);
lean_ctor_set(v_reuseFailAlloc_2373_, 11, v_incrLoadFileName_x3f_2362_);
lean_ctor_set(v_reuseFailAlloc_2373_, 12, v_incrHeaderSaveFileName_x3f_2363_);
lean_ctor_set_uint8(v_reuseFailAlloc_2373_, sizeof(void*)*13 + 8, v_component_2342_);
lean_ctor_set_uint8(v_reuseFailAlloc_2373_, sizeof(void*)*13 + 9, v_printPrefix_2343_);
lean_ctor_set_uint8(v_reuseFailAlloc_2373_, sizeof(void*)*13 + 10, v_printLibDir_2344_);
lean_ctor_set_uint8(v_reuseFailAlloc_2373_, sizeof(void*)*13 + 11, v_useStdin_2345_);
lean_ctor_set_uint8(v_reuseFailAlloc_2373_, sizeof(void*)*13 + 12, v_onlyDeps_2346_);
lean_ctor_set_uint8(v_reuseFailAlloc_2373_, sizeof(void*)*13 + 13, v_onlySrcDeps_2347_);
lean_ctor_set_uint8(v_reuseFailAlloc_2373_, sizeof(void*)*13 + 14, v_depsJson_2348_);
lean_ctor_set_uint32(v_reuseFailAlloc_2373_, sizeof(void*)*13, v_trustLevel_2350_);
lean_ctor_set_uint32(v_reuseFailAlloc_2373_, sizeof(void*)*13 + 4, v_numThreads_2351_);
lean_ctor_set_uint8(v_reuseFailAlloc_2373_, sizeof(void*)*13 + 15, v_jsonOutput_2357_);
lean_ctor_set_uint8(v_reuseFailAlloc_2373_, sizeof(void*)*13 + 16, v_printStats_2359_);
lean_ctor_set_uint8(v_reuseFailAlloc_2373_, sizeof(void*)*13 + 17, v_run_2360_);
v___x_2369_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2371_; 
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 0, v___x_2369_);
v___x_2371_ = v___x_2338_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2369_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
lean_dec_ref(v_opts_932_);
v_a_2377_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2377_);
lean_dec_ref_known(v___x_2335_, 1);
v___x_2381_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2382_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2381_);
lean_dec_ref(v___x_2382_);
goto v___jp_2378_;
v___jp_2378_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = lean_io_error_to_string(v_a_2377_);
v___x_2380_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2379_);
lean_dec_ref(v___x_2380_);
goto v___jp_1127_;
}
}
}
}
else
{
lean_object* v_leanOpts_2383_; lean_object* v_forwardedArgs_2384_; uint8_t v_component_2385_; uint8_t v_printPrefix_2386_; uint8_t v_printLibDir_2387_; uint8_t v_useStdin_2388_; uint8_t v_onlyDeps_2389_; uint8_t v_onlySrcDeps_2390_; uint8_t v_depsJson_2391_; lean_object* v_opts_2392_; uint32_t v_trustLevel_2393_; uint32_t v_numThreads_2394_; lean_object* v_rootDir_x3f_2395_; lean_object* v_setupFileName_x3f_2396_; lean_object* v_oleanFileName_x3f_2397_; lean_object* v_ileanFileName_x3f_2398_; lean_object* v_cFileName_x3f_2399_; lean_object* v_bcFileName_x3f_2400_; uint8_t v_jsonOutput_2401_; lean_object* v_errorOnKinds_2402_; uint8_t v_printStats_2403_; lean_object* v_incrSaveFileName_x3f_2404_; lean_object* v_incrLoadFileName_x3f_2405_; lean_object* v_incrHeaderSaveFileName_x3f_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2416_; 
lean_dec(v_optArg_x3f_934_);
v_leanOpts_2383_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_2384_ = lean_ctor_get(v_opts_932_, 1);
v_component_2385_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_2386_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_2387_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_2388_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_2389_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2390_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_2391_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_2392_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_2393_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_2394_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2395_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_2396_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_2397_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_2398_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_2399_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_2400_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_2401_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_2402_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_2403_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_incrSaveFileName_x3f_2404_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_2405_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_2406_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_2416_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2408_ = v_opts_932_;
v_isShared_2409_ = v_isSharedCheck_2416_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2406_);
lean_inc(v_incrLoadFileName_x3f_2405_);
lean_inc(v_incrSaveFileName_x3f_2404_);
lean_inc(v_errorOnKinds_2402_);
lean_inc(v_bcFileName_x3f_2400_);
lean_inc(v_cFileName_x3f_2399_);
lean_inc(v_ileanFileName_x3f_2398_);
lean_inc(v_oleanFileName_x3f_2397_);
lean_inc(v_setupFileName_x3f_2396_);
lean_inc(v_rootDir_x3f_2395_);
lean_inc(v_opts_2392_);
lean_inc(v_forwardedArgs_2384_);
lean_inc(v_leanOpts_2383_);
lean_dec(v_opts_932_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2416_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2413_; 
v___x_2410_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_2411_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_2383_, v___x_2410_, v___x_1175_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 0, v___x_2411_);
v___x_2413_ = v___x_2408_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2415_, 1, v_forwardedArgs_2384_);
lean_ctor_set(v_reuseFailAlloc_2415_, 2, v_opts_2392_);
lean_ctor_set(v_reuseFailAlloc_2415_, 3, v_rootDir_x3f_2395_);
lean_ctor_set(v_reuseFailAlloc_2415_, 4, v_setupFileName_x3f_2396_);
lean_ctor_set(v_reuseFailAlloc_2415_, 5, v_oleanFileName_x3f_2397_);
lean_ctor_set(v_reuseFailAlloc_2415_, 6, v_ileanFileName_x3f_2398_);
lean_ctor_set(v_reuseFailAlloc_2415_, 7, v_cFileName_x3f_2399_);
lean_ctor_set(v_reuseFailAlloc_2415_, 8, v_bcFileName_x3f_2400_);
lean_ctor_set(v_reuseFailAlloc_2415_, 9, v_errorOnKinds_2402_);
lean_ctor_set(v_reuseFailAlloc_2415_, 10, v_incrSaveFileName_x3f_2404_);
lean_ctor_set(v_reuseFailAlloc_2415_, 11, v_incrLoadFileName_x3f_2405_);
lean_ctor_set(v_reuseFailAlloc_2415_, 12, v_incrHeaderSaveFileName_x3f_2406_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, sizeof(void*)*13 + 8, v_component_2385_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, sizeof(void*)*13 + 9, v_printPrefix_2386_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, sizeof(void*)*13 + 10, v_printLibDir_2387_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, sizeof(void*)*13 + 11, v_useStdin_2388_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, sizeof(void*)*13 + 12, v_onlyDeps_2389_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, sizeof(void*)*13 + 13, v_onlySrcDeps_2390_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, sizeof(void*)*13 + 14, v_depsJson_2391_);
lean_ctor_set_uint32(v_reuseFailAlloc_2415_, sizeof(void*)*13, v_trustLevel_2393_);
lean_ctor_set_uint32(v_reuseFailAlloc_2415_, sizeof(void*)*13 + 4, v_numThreads_2394_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, sizeof(void*)*13 + 15, v_jsonOutput_2401_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, sizeof(void*)*13 + 16, v_printStats_2403_);
v___x_2413_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
lean_object* v___x_2414_; 
lean_ctor_set_uint8(v___x_2413_, sizeof(void*)*13 + 17, v___x_1177_);
v___x_2414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2413_);
return v___x_2414_;
}
}
}
}
else
{
lean_object* v_leanOpts_2417_; lean_object* v_forwardedArgs_2418_; uint8_t v_component_2419_; uint8_t v_printPrefix_2420_; uint8_t v_printLibDir_2421_; uint8_t v_onlyDeps_2422_; uint8_t v_onlySrcDeps_2423_; uint8_t v_depsJson_2424_; lean_object* v_opts_2425_; uint32_t v_trustLevel_2426_; uint32_t v_numThreads_2427_; lean_object* v_rootDir_x3f_2428_; lean_object* v_setupFileName_x3f_2429_; lean_object* v_oleanFileName_x3f_2430_; lean_object* v_ileanFileName_x3f_2431_; lean_object* v_cFileName_x3f_2432_; lean_object* v_bcFileName_x3f_2433_; uint8_t v_jsonOutput_2434_; lean_object* v_errorOnKinds_2435_; uint8_t v_printStats_2436_; uint8_t v_run_2437_; lean_object* v_incrSaveFileName_x3f_2438_; lean_object* v_incrLoadFileName_x3f_2439_; lean_object* v_incrHeaderSaveFileName_x3f_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2448_; 
lean_dec(v_optArg_x3f_934_);
v_leanOpts_2417_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_2418_ = lean_ctor_get(v_opts_932_, 1);
v_component_2419_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_2420_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_2421_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_onlyDeps_2422_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2423_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_2424_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_2425_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_2426_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_2427_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2428_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_2429_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_2430_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_2431_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_2432_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_2433_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_2434_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_2435_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_2436_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_2437_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2438_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_2439_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_2440_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_2448_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2442_ = v_opts_932_;
v_isShared_2443_ = v_isSharedCheck_2448_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2440_);
lean_inc(v_incrLoadFileName_x3f_2439_);
lean_inc(v_incrSaveFileName_x3f_2438_);
lean_inc(v_errorOnKinds_2435_);
lean_inc(v_bcFileName_x3f_2433_);
lean_inc(v_cFileName_x3f_2432_);
lean_inc(v_ileanFileName_x3f_2431_);
lean_inc(v_oleanFileName_x3f_2430_);
lean_inc(v_setupFileName_x3f_2429_);
lean_inc(v_rootDir_x3f_2428_);
lean_inc(v_opts_2425_);
lean_inc(v_forwardedArgs_2418_);
lean_inc(v_leanOpts_2417_);
lean_dec(v_opts_932_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2448_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_leanOpts_2417_);
lean_ctor_set(v_reuseFailAlloc_2447_, 1, v_forwardedArgs_2418_);
lean_ctor_set(v_reuseFailAlloc_2447_, 2, v_opts_2425_);
lean_ctor_set(v_reuseFailAlloc_2447_, 3, v_rootDir_x3f_2428_);
lean_ctor_set(v_reuseFailAlloc_2447_, 4, v_setupFileName_x3f_2429_);
lean_ctor_set(v_reuseFailAlloc_2447_, 5, v_oleanFileName_x3f_2430_);
lean_ctor_set(v_reuseFailAlloc_2447_, 6, v_ileanFileName_x3f_2431_);
lean_ctor_set(v_reuseFailAlloc_2447_, 7, v_cFileName_x3f_2432_);
lean_ctor_set(v_reuseFailAlloc_2447_, 8, v_bcFileName_x3f_2433_);
lean_ctor_set(v_reuseFailAlloc_2447_, 9, v_errorOnKinds_2435_);
lean_ctor_set(v_reuseFailAlloc_2447_, 10, v_incrSaveFileName_x3f_2438_);
lean_ctor_set(v_reuseFailAlloc_2447_, 11, v_incrLoadFileName_x3f_2439_);
lean_ctor_set(v_reuseFailAlloc_2447_, 12, v_incrHeaderSaveFileName_x3f_2440_);
lean_ctor_set_uint8(v_reuseFailAlloc_2447_, sizeof(void*)*13 + 8, v_component_2419_);
lean_ctor_set_uint8(v_reuseFailAlloc_2447_, sizeof(void*)*13 + 9, v_printPrefix_2420_);
lean_ctor_set_uint8(v_reuseFailAlloc_2447_, sizeof(void*)*13 + 10, v_printLibDir_2421_);
lean_ctor_set_uint8(v_reuseFailAlloc_2447_, sizeof(void*)*13 + 12, v_onlyDeps_2422_);
lean_ctor_set_uint8(v_reuseFailAlloc_2447_, sizeof(void*)*13 + 13, v_onlySrcDeps_2423_);
lean_ctor_set_uint8(v_reuseFailAlloc_2447_, sizeof(void*)*13 + 14, v_depsJson_2424_);
lean_ctor_set_uint32(v_reuseFailAlloc_2447_, sizeof(void*)*13, v_trustLevel_2426_);
lean_ctor_set_uint32(v_reuseFailAlloc_2447_, sizeof(void*)*13 + 4, v_numThreads_2427_);
lean_ctor_set_uint8(v_reuseFailAlloc_2447_, sizeof(void*)*13 + 15, v_jsonOutput_2434_);
lean_ctor_set_uint8(v_reuseFailAlloc_2447_, sizeof(void*)*13 + 16, v_printStats_2436_);
lean_ctor_set_uint8(v_reuseFailAlloc_2447_, sizeof(void*)*13 + 17, v_run_2437_);
v___x_2445_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
lean_object* v___x_2446_; 
lean_ctor_set_uint8(v___x_2445_, sizeof(void*)*13 + 11, v___x_1175_);
v___x_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
return v___x_2446_;
}
}
}
}
else
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27));
v___x_2450_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2449_, v_optArg_x3f_934_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2512_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2453_ = v___x_2450_;
v_isShared_2454_ = v_isSharedCheck_2512_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2512_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2455_ = lean_unsigned_to_nat(0u);
v___x_2456_ = lean_string_utf8_byte_size(v_a_2451_);
lean_inc(v_a_2451_);
v___x_2457_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2457_, 0, v_a_2451_);
lean_ctor_set(v___x_2457_, 1, v___x_2455_);
lean_ctor_set(v___x_2457_, 2, v___x_2456_);
v___x_2458_ = l_String_Slice_toNat_x3f(v___x_2457_);
lean_dec_ref_known(v___x_2457_, 3);
if (lean_obj_tag(v___x_2458_) == 1)
{
lean_object* v_val_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; 
v_val_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_val_2459_);
lean_dec_ref_known(v___x_2458_, 1);
v___x_2460_ = lean_unsigned_to_nat(4u);
v___x_2461_ = lean_unsigned_to_nat(2u);
v___x_2462_ = lean_nat_shiftr(v_val_2459_, v___x_2461_);
lean_dec(v_val_2459_);
v___x_2463_ = lean_nat_mul(v___x_2462_, v___x_2460_);
lean_dec(v___x_2462_);
v___x_2464_ = lean_unsigned_to_nat(1024u);
v___x_2465_ = lean_nat_mul(v___x_2463_, v___x_2464_);
lean_dec(v___x_2463_);
v___x_2466_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28, &l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28_once, _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28);
v___x_2467_ = lean_nat_dec_lt(v___x_2465_, v___x_2466_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; lean_object* v___x_2469_; 
lean_dec(v___x_2465_);
lean_del_object(v___x_2453_);
lean_dec(v_a_2451_);
lean_dec_ref(v_opts_932_);
v___x_2468_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29));
v___x_2469_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2468_);
lean_dec_ref(v___x_2469_);
goto v___jp_975_;
}
else
{
size_t v___x_2470_; lean_object* v___x_2471_; lean_object* v_leanOpts_2472_; lean_object* v_forwardedArgs_2473_; uint8_t v_component_2474_; uint8_t v_printPrefix_2475_; uint8_t v_printLibDir_2476_; uint8_t v_useStdin_2477_; uint8_t v_onlyDeps_2478_; uint8_t v_onlySrcDeps_2479_; uint8_t v_depsJson_2480_; lean_object* v_opts_2481_; uint32_t v_trustLevel_2482_; uint32_t v_numThreads_2483_; lean_object* v_rootDir_x3f_2484_; lean_object* v_setupFileName_x3f_2485_; lean_object* v_oleanFileName_x3f_2486_; lean_object* v_ileanFileName_x3f_2487_; lean_object* v_cFileName_x3f_2488_; lean_object* v_bcFileName_x3f_2489_; uint8_t v_jsonOutput_2490_; lean_object* v_errorOnKinds_2491_; uint8_t v_printStats_2492_; uint8_t v_run_2493_; lean_object* v_incrSaveFileName_x3f_2494_; lean_object* v_incrLoadFileName_x3f_2495_; lean_object* v_incrHeaderSaveFileName_x3f_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2509_; 
v___x_2470_ = lean_usize_of_nat(v___x_2465_);
lean_dec(v___x_2465_);
v___x_2471_ = lean_internal_set_thread_stack_size(v___x_2470_);
v_leanOpts_2472_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_2473_ = lean_ctor_get(v_opts_932_, 1);
v_component_2474_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_2475_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_2476_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_2477_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_2478_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2479_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_2480_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_2481_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_2482_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_2483_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2484_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_2485_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_2486_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_2487_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_2488_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_2489_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_2490_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_2491_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_2492_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_2493_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2494_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_2495_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_2496_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_2509_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2498_ = v_opts_932_;
v_isShared_2499_ = v_isSharedCheck_2509_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2496_);
lean_inc(v_incrLoadFileName_x3f_2495_);
lean_inc(v_incrSaveFileName_x3f_2494_);
lean_inc(v_errorOnKinds_2491_);
lean_inc(v_bcFileName_x3f_2489_);
lean_inc(v_cFileName_x3f_2488_);
lean_inc(v_ileanFileName_x3f_2487_);
lean_inc(v_oleanFileName_x3f_2486_);
lean_inc(v_setupFileName_x3f_2485_);
lean_inc(v_rootDir_x3f_2484_);
lean_inc(v_opts_2481_);
lean_inc(v_forwardedArgs_2473_);
lean_inc(v_leanOpts_2472_);
lean_dec(v_opts_932_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2509_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2504_; 
v___x_2500_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30));
v___x_2501_ = lean_string_append(v___x_2500_, v_a_2451_);
lean_dec(v_a_2451_);
v___x_2502_ = lean_array_push(v_forwardedArgs_2473_, v___x_2501_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 1, v___x_2502_);
v___x_2504_ = v___x_2498_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_leanOpts_2472_);
lean_ctor_set(v_reuseFailAlloc_2508_, 1, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2508_, 2, v_opts_2481_);
lean_ctor_set(v_reuseFailAlloc_2508_, 3, v_rootDir_x3f_2484_);
lean_ctor_set(v_reuseFailAlloc_2508_, 4, v_setupFileName_x3f_2485_);
lean_ctor_set(v_reuseFailAlloc_2508_, 5, v_oleanFileName_x3f_2486_);
lean_ctor_set(v_reuseFailAlloc_2508_, 6, v_ileanFileName_x3f_2487_);
lean_ctor_set(v_reuseFailAlloc_2508_, 7, v_cFileName_x3f_2488_);
lean_ctor_set(v_reuseFailAlloc_2508_, 8, v_bcFileName_x3f_2489_);
lean_ctor_set(v_reuseFailAlloc_2508_, 9, v_errorOnKinds_2491_);
lean_ctor_set(v_reuseFailAlloc_2508_, 10, v_incrSaveFileName_x3f_2494_);
lean_ctor_set(v_reuseFailAlloc_2508_, 11, v_incrLoadFileName_x3f_2495_);
lean_ctor_set(v_reuseFailAlloc_2508_, 12, v_incrHeaderSaveFileName_x3f_2496_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, sizeof(void*)*13 + 8, v_component_2474_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, sizeof(void*)*13 + 9, v_printPrefix_2475_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, sizeof(void*)*13 + 10, v_printLibDir_2476_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, sizeof(void*)*13 + 11, v_useStdin_2477_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, sizeof(void*)*13 + 12, v_onlyDeps_2478_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, sizeof(void*)*13 + 13, v_onlySrcDeps_2479_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, sizeof(void*)*13 + 14, v_depsJson_2480_);
lean_ctor_set_uint32(v_reuseFailAlloc_2508_, sizeof(void*)*13, v_trustLevel_2482_);
lean_ctor_set_uint32(v_reuseFailAlloc_2508_, sizeof(void*)*13 + 4, v_numThreads_2483_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, sizeof(void*)*13 + 15, v_jsonOutput_2490_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, sizeof(void*)*13 + 16, v_printStats_2492_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, sizeof(void*)*13 + 17, v_run_2493_);
v___x_2504_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
lean_object* v___x_2506_; 
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2504_);
v___x_2506_ = v___x_2453_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2504_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
}
else
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
lean_dec(v___x_2458_);
lean_del_object(v___x_2453_);
lean_dec(v_a_2451_);
lean_dec_ref(v_opts_932_);
v___x_2510_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31));
v___x_2511_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2510_);
lean_dec_ref(v___x_2511_);
goto v___jp_972_;
}
}
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
lean_dec_ref(v_opts_932_);
v_a_2513_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_a_2513_);
lean_dec_ref_known(v___x_2450_, 1);
v___x_2517_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2518_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2517_);
lean_dec_ref(v___x_2518_);
goto v___jp_2514_;
v___jp_2514_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = lean_io_error_to_string(v_a_2513_);
v___x_2516_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2515_);
lean_dec_ref(v___x_2516_);
goto v___jp_969_;
}
}
}
}
else
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32));
v___x_2520_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2519_, v_optArg_x3f_934_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2561_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2523_ = v___x_2520_;
v_isShared_2524_ = v_isSharedCheck_2561_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2520_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2561_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v_leanOpts_2525_; lean_object* v_forwardedArgs_2526_; uint8_t v_component_2527_; uint8_t v_printPrefix_2528_; uint8_t v_printLibDir_2529_; uint8_t v_useStdin_2530_; uint8_t v_onlyDeps_2531_; uint8_t v_onlySrcDeps_2532_; uint8_t v_depsJson_2533_; lean_object* v_opts_2534_; uint32_t v_trustLevel_2535_; uint32_t v_numThreads_2536_; lean_object* v_rootDir_x3f_2537_; lean_object* v_setupFileName_x3f_2538_; lean_object* v_oleanFileName_x3f_2539_; lean_object* v_ileanFileName_x3f_2540_; lean_object* v_cFileName_x3f_2541_; uint8_t v_jsonOutput_2542_; lean_object* v_errorOnKinds_2543_; uint8_t v_printStats_2544_; uint8_t v_run_2545_; lean_object* v_incrSaveFileName_x3f_2546_; lean_object* v_incrLoadFileName_x3f_2547_; lean_object* v_incrHeaderSaveFileName_x3f_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2559_; 
v_leanOpts_2525_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_2526_ = lean_ctor_get(v_opts_932_, 1);
v_component_2527_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_2528_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_2529_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_2530_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_2531_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2532_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_2533_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_2534_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_2535_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_2536_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2537_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_2538_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_2539_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_2540_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_2541_ = lean_ctor_get(v_opts_932_, 7);
v_jsonOutput_2542_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_2543_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_2544_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_2545_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2546_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_2547_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_2548_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_2559_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_2559_ == 0)
{
lean_object* v_unused_2560_; 
v_unused_2560_ = lean_ctor_get(v_opts_932_, 8);
lean_dec(v_unused_2560_);
v___x_2550_ = v_opts_932_;
v_isShared_2551_ = v_isSharedCheck_2559_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2548_);
lean_inc(v_incrLoadFileName_x3f_2547_);
lean_inc(v_incrSaveFileName_x3f_2546_);
lean_inc(v_errorOnKinds_2543_);
lean_inc(v_cFileName_x3f_2541_);
lean_inc(v_ileanFileName_x3f_2540_);
lean_inc(v_oleanFileName_x3f_2539_);
lean_inc(v_setupFileName_x3f_2538_);
lean_inc(v_rootDir_x3f_2537_);
lean_inc(v_opts_2534_);
lean_inc(v_forwardedArgs_2526_);
lean_inc(v_leanOpts_2525_);
lean_dec(v_opts_932_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2559_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2552_; lean_object* v___x_2554_; 
v___x_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2552_, 0, v_a_2521_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 8, v___x_2552_);
v___x_2554_ = v___x_2550_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_leanOpts_2525_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v_forwardedArgs_2526_);
lean_ctor_set(v_reuseFailAlloc_2558_, 2, v_opts_2534_);
lean_ctor_set(v_reuseFailAlloc_2558_, 3, v_rootDir_x3f_2537_);
lean_ctor_set(v_reuseFailAlloc_2558_, 4, v_setupFileName_x3f_2538_);
lean_ctor_set(v_reuseFailAlloc_2558_, 5, v_oleanFileName_x3f_2539_);
lean_ctor_set(v_reuseFailAlloc_2558_, 6, v_ileanFileName_x3f_2540_);
lean_ctor_set(v_reuseFailAlloc_2558_, 7, v_cFileName_x3f_2541_);
lean_ctor_set(v_reuseFailAlloc_2558_, 8, v___x_2552_);
lean_ctor_set(v_reuseFailAlloc_2558_, 9, v_errorOnKinds_2543_);
lean_ctor_set(v_reuseFailAlloc_2558_, 10, v_incrSaveFileName_x3f_2546_);
lean_ctor_set(v_reuseFailAlloc_2558_, 11, v_incrLoadFileName_x3f_2547_);
lean_ctor_set(v_reuseFailAlloc_2558_, 12, v_incrHeaderSaveFileName_x3f_2548_);
lean_ctor_set_uint8(v_reuseFailAlloc_2558_, sizeof(void*)*13 + 8, v_component_2527_);
lean_ctor_set_uint8(v_reuseFailAlloc_2558_, sizeof(void*)*13 + 9, v_printPrefix_2528_);
lean_ctor_set_uint8(v_reuseFailAlloc_2558_, sizeof(void*)*13 + 10, v_printLibDir_2529_);
lean_ctor_set_uint8(v_reuseFailAlloc_2558_, sizeof(void*)*13 + 11, v_useStdin_2530_);
lean_ctor_set_uint8(v_reuseFailAlloc_2558_, sizeof(void*)*13 + 12, v_onlyDeps_2531_);
lean_ctor_set_uint8(v_reuseFailAlloc_2558_, sizeof(void*)*13 + 13, v_onlySrcDeps_2532_);
lean_ctor_set_uint8(v_reuseFailAlloc_2558_, sizeof(void*)*13 + 14, v_depsJson_2533_);
lean_ctor_set_uint32(v_reuseFailAlloc_2558_, sizeof(void*)*13, v_trustLevel_2535_);
lean_ctor_set_uint32(v_reuseFailAlloc_2558_, sizeof(void*)*13 + 4, v_numThreads_2536_);
lean_ctor_set_uint8(v_reuseFailAlloc_2558_, sizeof(void*)*13 + 15, v_jsonOutput_2542_);
lean_ctor_set_uint8(v_reuseFailAlloc_2558_, sizeof(void*)*13 + 16, v_printStats_2544_);
lean_ctor_set_uint8(v_reuseFailAlloc_2558_, sizeof(void*)*13 + 17, v_run_2545_);
v___x_2554_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
lean_object* v___x_2556_; 
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 0, v___x_2554_);
v___x_2556_ = v___x_2523_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2554_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
lean_dec_ref(v_opts_932_);
v_a_2562_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2562_);
lean_dec_ref_known(v___x_2520_, 1);
v___x_2566_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2567_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2566_);
lean_dec_ref(v___x_2567_);
goto v___jp_2563_;
v___jp_2563_:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2564_ = lean_io_error_to_string(v_a_2562_);
v___x_2565_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2564_);
lean_dec_ref(v___x_2565_);
goto v___jp_1133_;
}
}
}
}
else
{
lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2568_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33));
v___x_2569_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2568_, v_optArg_x3f_934_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2610_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2572_ = v___x_2569_;
v_isShared_2573_ = v_isSharedCheck_2610_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2569_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2610_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v_leanOpts_2574_; lean_object* v_forwardedArgs_2575_; uint8_t v_component_2576_; uint8_t v_printPrefix_2577_; uint8_t v_printLibDir_2578_; uint8_t v_useStdin_2579_; uint8_t v_onlyDeps_2580_; uint8_t v_onlySrcDeps_2581_; uint8_t v_depsJson_2582_; lean_object* v_opts_2583_; uint32_t v_trustLevel_2584_; uint32_t v_numThreads_2585_; lean_object* v_rootDir_x3f_2586_; lean_object* v_setupFileName_x3f_2587_; lean_object* v_oleanFileName_x3f_2588_; lean_object* v_ileanFileName_x3f_2589_; lean_object* v_bcFileName_x3f_2590_; uint8_t v_jsonOutput_2591_; lean_object* v_errorOnKinds_2592_; uint8_t v_printStats_2593_; uint8_t v_run_2594_; lean_object* v_incrSaveFileName_x3f_2595_; lean_object* v_incrLoadFileName_x3f_2596_; lean_object* v_incrHeaderSaveFileName_x3f_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2608_; 
v_leanOpts_2574_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_2575_ = lean_ctor_get(v_opts_932_, 1);
v_component_2576_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_2577_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_2578_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_2579_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_2580_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2581_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_2582_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_2583_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_2584_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_numThreads_2585_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2586_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_2587_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_2588_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_2589_ = lean_ctor_get(v_opts_932_, 6);
v_bcFileName_x3f_2590_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_2591_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_2592_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_2593_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_2594_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2595_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_2596_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_2597_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_2608_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_2608_ == 0)
{
lean_object* v_unused_2609_; 
v_unused_2609_ = lean_ctor_get(v_opts_932_, 7);
lean_dec(v_unused_2609_);
v___x_2599_ = v_opts_932_;
v_isShared_2600_ = v_isSharedCheck_2608_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2597_);
lean_inc(v_incrLoadFileName_x3f_2596_);
lean_inc(v_incrSaveFileName_x3f_2595_);
lean_inc(v_errorOnKinds_2592_);
lean_inc(v_bcFileName_x3f_2590_);
lean_inc(v_ileanFileName_x3f_2589_);
lean_inc(v_oleanFileName_x3f_2588_);
lean_inc(v_setupFileName_x3f_2587_);
lean_inc(v_rootDir_x3f_2586_);
lean_inc(v_opts_2583_);
lean_inc(v_forwardedArgs_2575_);
lean_inc(v_leanOpts_2574_);
lean_dec(v_opts_932_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2608_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2601_; lean_object* v___x_2603_; 
v___x_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2601_, 0, v_a_2570_);
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 7, v___x_2601_);
v___x_2603_ = v___x_2599_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_leanOpts_2574_);
lean_ctor_set(v_reuseFailAlloc_2607_, 1, v_forwardedArgs_2575_);
lean_ctor_set(v_reuseFailAlloc_2607_, 2, v_opts_2583_);
lean_ctor_set(v_reuseFailAlloc_2607_, 3, v_rootDir_x3f_2586_);
lean_ctor_set(v_reuseFailAlloc_2607_, 4, v_setupFileName_x3f_2587_);
lean_ctor_set(v_reuseFailAlloc_2607_, 5, v_oleanFileName_x3f_2588_);
lean_ctor_set(v_reuseFailAlloc_2607_, 6, v_ileanFileName_x3f_2589_);
lean_ctor_set(v_reuseFailAlloc_2607_, 7, v___x_2601_);
lean_ctor_set(v_reuseFailAlloc_2607_, 8, v_bcFileName_x3f_2590_);
lean_ctor_set(v_reuseFailAlloc_2607_, 9, v_errorOnKinds_2592_);
lean_ctor_set(v_reuseFailAlloc_2607_, 10, v_incrSaveFileName_x3f_2595_);
lean_ctor_set(v_reuseFailAlloc_2607_, 11, v_incrLoadFileName_x3f_2596_);
lean_ctor_set(v_reuseFailAlloc_2607_, 12, v_incrHeaderSaveFileName_x3f_2597_);
lean_ctor_set_uint8(v_reuseFailAlloc_2607_, sizeof(void*)*13 + 8, v_component_2576_);
lean_ctor_set_uint8(v_reuseFailAlloc_2607_, sizeof(void*)*13 + 9, v_printPrefix_2577_);
lean_ctor_set_uint8(v_reuseFailAlloc_2607_, sizeof(void*)*13 + 10, v_printLibDir_2578_);
lean_ctor_set_uint8(v_reuseFailAlloc_2607_, sizeof(void*)*13 + 11, v_useStdin_2579_);
lean_ctor_set_uint8(v_reuseFailAlloc_2607_, sizeof(void*)*13 + 12, v_onlyDeps_2580_);
lean_ctor_set_uint8(v_reuseFailAlloc_2607_, sizeof(void*)*13 + 13, v_onlySrcDeps_2581_);
lean_ctor_set_uint8(v_reuseFailAlloc_2607_, sizeof(void*)*13 + 14, v_depsJson_2582_);
lean_ctor_set_uint32(v_reuseFailAlloc_2607_, sizeof(void*)*13, v_trustLevel_2584_);
lean_ctor_set_uint32(v_reuseFailAlloc_2607_, sizeof(void*)*13 + 4, v_numThreads_2585_);
lean_ctor_set_uint8(v_reuseFailAlloc_2607_, sizeof(void*)*13 + 15, v_jsonOutput_2591_);
lean_ctor_set_uint8(v_reuseFailAlloc_2607_, sizeof(void*)*13 + 16, v_printStats_2593_);
lean_ctor_set_uint8(v_reuseFailAlloc_2607_, sizeof(void*)*13 + 17, v_run_2594_);
v___x_2603_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
lean_object* v___x_2605_; 
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v___x_2603_);
v___x_2605_ = v___x_2572_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2603_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
lean_dec_ref(v_opts_932_);
v_a_2611_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_a_2611_);
lean_dec_ref_known(v___x_2569_, 1);
v___x_2615_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2616_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2615_);
lean_dec_ref(v___x_2616_);
goto v___jp_2612_;
v___jp_2612_:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2613_ = lean_io_error_to_string(v_a_2611_);
v___x_2614_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2613_);
lean_dec_ref(v___x_2614_);
goto v___jp_963_;
}
}
}
}
else
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
lean_dec(v_optArg_x3f_934_);
lean_dec_ref(v_opts_932_);
v___x_2617_ = l___private_Lean_Shell_0__Lean_featuresString;
v___x_2618_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2617_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2626_; 
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2626_ == 0)
{
lean_object* v_unused_2627_; 
v_unused_2627_ = lean_ctor_get(v___x_2618_, 0);
lean_dec(v_unused_2627_);
v___x_2620_ = v___x_2618_;
v_isShared_2621_ = v_isSharedCheck_2626_;
goto v_resetjp_2619_;
}
else
{
lean_dec(v___x_2618_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2626_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2622_; lean_object* v___x_2624_; 
v___x_2622_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2621_ == 0)
{
lean_ctor_set_tag(v___x_2620_, 1);
lean_ctor_set(v___x_2620_, 0, v___x_2622_);
v___x_2624_ = v___x_2620_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2622_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v_a_2628_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2628_);
lean_dec_ref_known(v___x_2618_, 1);
v___x_2632_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2633_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2632_);
lean_dec_ref(v___x_2633_);
goto v___jp_2629_;
v___jp_2629_:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2630_ = lean_io_error_to_string(v_a_2628_);
v___x_2631_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2630_);
lean_dec_ref(v___x_2631_);
goto v___jp_1139_;
}
}
}
}
else
{
lean_object* v___x_2634_; 
lean_dec(v_optArg_x3f_934_);
lean_dec_ref(v_opts_932_);
v___x_2634_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1163_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2642_; 
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2642_ == 0)
{
lean_object* v_unused_2643_; 
v_unused_2643_ = lean_ctor_get(v___x_2634_, 0);
lean_dec(v_unused_2643_);
v___x_2636_ = v___x_2634_;
v_isShared_2637_ = v_isSharedCheck_2642_;
goto v_resetjp_2635_;
}
else
{
lean_dec(v___x_2634_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2642_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2638_; lean_object* v___x_2640_; 
v___x_2638_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2637_ == 0)
{
lean_ctor_set_tag(v___x_2636_, 1);
lean_ctor_set(v___x_2636_, 0, v___x_2638_);
v___x_2640_ = v___x_2636_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2638_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v_a_2644_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_a_2644_);
lean_dec_ref_known(v___x_2634_, 1);
v___x_2648_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2649_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2648_);
lean_dec_ref(v___x_2649_);
goto v___jp_2645_;
v___jp_2645_:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2646_ = lean_io_error_to_string(v_a_2644_);
v___x_2647_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2646_);
lean_dec_ref(v___x_2647_);
goto v___jp_957_;
}
}
}
}
else
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
lean_dec(v_optArg_x3f_934_);
lean_dec_ref(v_opts_932_);
v___x_2650_ = l_Lean_githash;
v___x_2651_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2650_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2659_; 
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2659_ == 0)
{
lean_object* v_unused_2660_; 
v_unused_2660_ = lean_ctor_get(v___x_2651_, 0);
lean_dec(v_unused_2660_);
v___x_2653_ = v___x_2651_;
v_isShared_2654_ = v_isSharedCheck_2659_;
goto v_resetjp_2652_;
}
else
{
lean_dec(v___x_2651_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2659_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2655_; lean_object* v___x_2657_; 
v___x_2655_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2654_ == 0)
{
lean_ctor_set_tag(v___x_2653_, 1);
lean_ctor_set(v___x_2653_, 0, v___x_2655_);
v___x_2657_ = v___x_2653_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v___x_2655_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v_a_2661_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2661_);
lean_dec_ref_known(v___x_2651_, 1);
v___x_2665_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2666_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2665_);
lean_dec_ref(v___x_2666_);
goto v___jp_2662_;
v___jp_2662_:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2663_ = lean_io_error_to_string(v_a_2661_);
v___x_2664_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2663_);
lean_dec_ref(v___x_2664_);
goto v___jp_1145_;
}
}
}
}
else
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
lean_dec(v_optArg_x3f_934_);
lean_dec_ref(v_opts_932_);
v___x_2667_ = l___private_Lean_Shell_0__Lean_shortVersionString;
v___x_2668_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2667_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2676_; 
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2676_ == 0)
{
lean_object* v_unused_2677_; 
v_unused_2677_ = lean_ctor_get(v___x_2668_, 0);
lean_dec(v_unused_2677_);
v___x_2670_ = v___x_2668_;
v_isShared_2671_ = v_isSharedCheck_2676_;
goto v_resetjp_2669_;
}
else
{
lean_dec(v___x_2668_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2676_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2672_; lean_object* v___x_2674_; 
v___x_2672_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2671_ == 0)
{
lean_ctor_set_tag(v___x_2670_, 1);
lean_ctor_set(v___x_2670_, 0, v___x_2672_);
v___x_2674_ = v___x_2670_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2672_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v_a_2678_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2678_);
lean_dec_ref_known(v___x_2668_, 1);
v___x_2682_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2683_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2682_);
lean_dec_ref(v___x_2683_);
goto v___jp_2679_;
v___jp_2679_:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2680_ = lean_io_error_to_string(v_a_2678_);
v___x_2681_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2680_);
lean_dec_ref(v___x_2681_);
goto v___jp_951_;
}
}
}
}
else
{
lean_object* v___x_2684_; lean_object* v___x_2685_; 
lean_dec(v_optArg_x3f_934_);
lean_dec_ref(v_opts_932_);
v___x_2684_ = l___private_Lean_Shell_0__Lean_versionHeader;
v___x_2685_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2684_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2693_; 
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2693_ == 0)
{
lean_object* v_unused_2694_; 
v_unused_2694_ = lean_ctor_get(v___x_2685_, 0);
lean_dec(v_unused_2694_);
v___x_2687_ = v___x_2685_;
v_isShared_2688_ = v_isSharedCheck_2693_;
goto v_resetjp_2686_;
}
else
{
lean_dec(v___x_2685_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2693_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2689_; lean_object* v___x_2691_; 
v___x_2689_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2688_ == 0)
{
lean_ctor_set_tag(v___x_2687_, 1);
lean_ctor_set(v___x_2687_, 0, v___x_2689_);
v___x_2691_ = v___x_2687_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2689_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v_a_2695_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2695_);
lean_dec_ref_known(v___x_2685_, 1);
v___x_2699_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2700_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2699_);
lean_dec_ref(v___x_2700_);
goto v___jp_2696_;
v___jp_2696_:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2697_ = lean_io_error_to_string(v_a_2695_);
v___x_2698_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2697_);
lean_dec_ref(v___x_2698_);
goto v___jp_1151_;
}
}
}
}
else
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34));
v___x_2702_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2701_, v_optArg_x3f_934_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2756_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2705_ = v___x_2702_;
v_isShared_2706_ = v_isSharedCheck_2756_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2702_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2756_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2707_ = lean_unsigned_to_nat(0u);
v___x_2708_ = lean_string_utf8_byte_size(v_a_2703_);
lean_inc(v_a_2703_);
v___x_2709_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2709_, 0, v_a_2703_);
lean_ctor_set(v___x_2709_, 1, v___x_2707_);
lean_ctor_set(v___x_2709_, 2, v___x_2708_);
v___x_2710_ = l_String_Slice_toNat_x3f(v___x_2709_);
lean_dec_ref_known(v___x_2709_, 3);
if (lean_obj_tag(v___x_2710_) == 1)
{
lean_object* v_val_2711_; lean_object* v___x_2712_; uint8_t v___x_2713_; 
v_val_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_val_2711_);
lean_dec_ref_known(v___x_2710_, 1);
v___x_2712_ = lean_cstr_to_nat("4294967296");
v___x_2713_ = lean_nat_dec_lt(v_val_2711_, v___x_2712_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
lean_dec(v_val_2711_);
lean_del_object(v___x_2705_);
lean_dec(v_a_2703_);
lean_dec_ref(v_opts_932_);
v___x_2714_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__35));
v___x_2715_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2714_);
lean_dec_ref(v___x_2715_);
goto v___jp_945_;
}
else
{
lean_object* v_leanOpts_2716_; lean_object* v_forwardedArgs_2717_; uint8_t v_component_2718_; uint8_t v_printPrefix_2719_; uint8_t v_printLibDir_2720_; uint8_t v_useStdin_2721_; uint8_t v_onlyDeps_2722_; uint8_t v_onlySrcDeps_2723_; uint8_t v_depsJson_2724_; lean_object* v_opts_2725_; uint32_t v_trustLevel_2726_; lean_object* v_rootDir_x3f_2727_; lean_object* v_setupFileName_x3f_2728_; lean_object* v_oleanFileName_x3f_2729_; lean_object* v_ileanFileName_x3f_2730_; lean_object* v_cFileName_x3f_2731_; lean_object* v_bcFileName_x3f_2732_; uint8_t v_jsonOutput_2733_; lean_object* v_errorOnKinds_2734_; uint8_t v_printStats_2735_; uint8_t v_run_2736_; lean_object* v_incrSaveFileName_x3f_2737_; lean_object* v_incrLoadFileName_x3f_2738_; lean_object* v_incrHeaderSaveFileName_x3f_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2753_; 
v_leanOpts_2716_ = lean_ctor_get(v_opts_932_, 0);
v_forwardedArgs_2717_ = lean_ctor_get(v_opts_932_, 1);
v_component_2718_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 8);
v_printPrefix_2719_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 9);
v_printLibDir_2720_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 10);
v_useStdin_2721_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 11);
v_onlyDeps_2722_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2723_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 13);
v_depsJson_2724_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 14);
v_opts_2725_ = lean_ctor_get(v_opts_932_, 2);
v_trustLevel_2726_ = lean_ctor_get_uint32(v_opts_932_, sizeof(void*)*13);
v_rootDir_x3f_2727_ = lean_ctor_get(v_opts_932_, 3);
v_setupFileName_x3f_2728_ = lean_ctor_get(v_opts_932_, 4);
v_oleanFileName_x3f_2729_ = lean_ctor_get(v_opts_932_, 5);
v_ileanFileName_x3f_2730_ = lean_ctor_get(v_opts_932_, 6);
v_cFileName_x3f_2731_ = lean_ctor_get(v_opts_932_, 7);
v_bcFileName_x3f_2732_ = lean_ctor_get(v_opts_932_, 8);
v_jsonOutput_2733_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 15);
v_errorOnKinds_2734_ = lean_ctor_get(v_opts_932_, 9);
v_printStats_2735_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 16);
v_run_2736_ = lean_ctor_get_uint8(v_opts_932_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2737_ = lean_ctor_get(v_opts_932_, 10);
v_incrLoadFileName_x3f_2738_ = lean_ctor_get(v_opts_932_, 11);
v_incrHeaderSaveFileName_x3f_2739_ = lean_ctor_get(v_opts_932_, 12);
v_isSharedCheck_2753_ = !lean_is_exclusive(v_opts_932_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2741_ = v_opts_932_;
v_isShared_2742_ = v_isSharedCheck_2753_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2739_);
lean_inc(v_incrLoadFileName_x3f_2738_);
lean_inc(v_incrSaveFileName_x3f_2737_);
lean_inc(v_errorOnKinds_2734_);
lean_inc(v_bcFileName_x3f_2732_);
lean_inc(v_cFileName_x3f_2731_);
lean_inc(v_ileanFileName_x3f_2730_);
lean_inc(v_oleanFileName_x3f_2729_);
lean_inc(v_setupFileName_x3f_2728_);
lean_inc(v_rootDir_x3f_2727_);
lean_inc(v_opts_2725_);
lean_inc(v_forwardedArgs_2717_);
lean_inc(v_leanOpts_2716_);
lean_dec(v_opts_932_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2753_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
uint32_t v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2748_; 
v___x_2743_ = lean_uint32_of_nat(v_val_2711_);
lean_dec(v_val_2711_);
v___x_2744_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__36));
v___x_2745_ = lean_string_append(v___x_2744_, v_a_2703_);
lean_dec(v_a_2703_);
v___x_2746_ = lean_array_push(v_forwardedArgs_2717_, v___x_2745_);
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 1, v___x_2746_);
v___x_2748_ = v___x_2741_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_leanOpts_2716_);
lean_ctor_set(v_reuseFailAlloc_2752_, 1, v___x_2746_);
lean_ctor_set(v_reuseFailAlloc_2752_, 2, v_opts_2725_);
lean_ctor_set(v_reuseFailAlloc_2752_, 3, v_rootDir_x3f_2727_);
lean_ctor_set(v_reuseFailAlloc_2752_, 4, v_setupFileName_x3f_2728_);
lean_ctor_set(v_reuseFailAlloc_2752_, 5, v_oleanFileName_x3f_2729_);
lean_ctor_set(v_reuseFailAlloc_2752_, 6, v_ileanFileName_x3f_2730_);
lean_ctor_set(v_reuseFailAlloc_2752_, 7, v_cFileName_x3f_2731_);
lean_ctor_set(v_reuseFailAlloc_2752_, 8, v_bcFileName_x3f_2732_);
lean_ctor_set(v_reuseFailAlloc_2752_, 9, v_errorOnKinds_2734_);
lean_ctor_set(v_reuseFailAlloc_2752_, 10, v_incrSaveFileName_x3f_2737_);
lean_ctor_set(v_reuseFailAlloc_2752_, 11, v_incrLoadFileName_x3f_2738_);
lean_ctor_set(v_reuseFailAlloc_2752_, 12, v_incrHeaderSaveFileName_x3f_2739_);
lean_ctor_set_uint8(v_reuseFailAlloc_2752_, sizeof(void*)*13 + 8, v_component_2718_);
lean_ctor_set_uint8(v_reuseFailAlloc_2752_, sizeof(void*)*13 + 9, v_printPrefix_2719_);
lean_ctor_set_uint8(v_reuseFailAlloc_2752_, sizeof(void*)*13 + 10, v_printLibDir_2720_);
lean_ctor_set_uint8(v_reuseFailAlloc_2752_, sizeof(void*)*13 + 11, v_useStdin_2721_);
lean_ctor_set_uint8(v_reuseFailAlloc_2752_, sizeof(void*)*13 + 12, v_onlyDeps_2722_);
lean_ctor_set_uint8(v_reuseFailAlloc_2752_, sizeof(void*)*13 + 13, v_onlySrcDeps_2723_);
lean_ctor_set_uint8(v_reuseFailAlloc_2752_, sizeof(void*)*13 + 14, v_depsJson_2724_);
lean_ctor_set_uint32(v_reuseFailAlloc_2752_, sizeof(void*)*13, v_trustLevel_2726_);
lean_ctor_set_uint8(v_reuseFailAlloc_2752_, sizeof(void*)*13 + 15, v_jsonOutput_2733_);
lean_ctor_set_uint8(v_reuseFailAlloc_2752_, sizeof(void*)*13 + 16, v_printStats_2735_);
lean_ctor_set_uint8(v_reuseFailAlloc_2752_, sizeof(void*)*13 + 17, v_run_2736_);
v___x_2748_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
lean_object* v___x_2750_; 
lean_ctor_set_uint32(v___x_2748_, sizeof(void*)*13 + 4, v___x_2743_);
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 0, v___x_2748_);
v___x_2750_ = v___x_2705_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v___x_2748_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
}
else
{
lean_object* v___x_2754_; lean_object* v___x_2755_; 
lean_dec(v___x_2710_);
lean_del_object(v___x_2705_);
lean_dec(v_a_2703_);
lean_dec_ref(v_opts_932_);
v___x_2754_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__37));
v___x_2755_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2754_);
lean_dec_ref(v___x_2755_);
goto v___jp_942_;
}
}
}
else
{
lean_object* v_a_2757_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
lean_dec_ref(v_opts_932_);
v_a_2757_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_a_2757_);
lean_dec_ref_known(v___x_2702_, 1);
v___x_2761_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2762_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2761_);
lean_dec_ref(v___x_2762_);
goto v___jp_2758_;
v___jp_2758_:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = lean_io_error_to_string(v_a_2757_);
v___x_2760_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2759_);
lean_dec_ref(v___x_2760_);
goto v___jp_939_;
}
}
}
}
else
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
lean_dec(v_optArg_x3f_934_);
v___x_2763_ = lean_internal_set_exit_on_panic(v___x_1155_);
v___x_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2764_, 0, v_opts_932_);
return v___x_2764_;
}
v___jp_936_:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
return v___x_938_;
}
v___jp_939_:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_941_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_940_);
lean_dec_ref(v___x_941_);
goto v___jp_936_;
}
v___jp_942_:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
return v___x_944_;
}
v___jp_945_:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
return v___x_947_;
}
v___jp_948_:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
return v___x_950_;
}
v___jp_951_:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_953_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_952_);
lean_dec_ref(v___x_953_);
goto v___jp_948_;
}
v___jp_954_:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
return v___x_956_;
}
v___jp_957_:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_959_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_958_);
lean_dec_ref(v___x_959_);
goto v___jp_954_;
}
v___jp_960_:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
return v___x_962_;
}
v___jp_963_:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_965_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_964_);
lean_dec_ref(v___x_965_);
goto v___jp_960_;
}
v___jp_966_:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
return v___x_968_;
}
v___jp_969_:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_971_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_970_);
lean_dec_ref(v___x_971_);
goto v___jp_966_;
}
v___jp_972_:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
return v___x_974_;
}
v___jp_975_:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
return v___x_977_;
}
v___jp_978_:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
return v___x_980_;
}
v___jp_981_:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_983_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_982_);
lean_dec_ref(v___x_983_);
goto v___jp_978_;
}
v___jp_984_:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
return v___x_986_;
}
v___jp_987_:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_989_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_988_);
lean_dec_ref(v___x_989_);
goto v___jp_984_;
}
v___jp_990_:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
return v___x_992_;
}
v___jp_993_:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
v___jp_996_:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_998_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_997_);
lean_dec_ref(v___x_998_);
goto v___jp_993_;
}
v___jp_999_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
return v___x_1001_;
}
v___jp_1002_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
return v___x_1004_;
}
v___jp_1005_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
return v___x_1007_;
}
v___jp_1008_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1010_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1009_);
lean_dec_ref(v___x_1010_);
goto v___jp_1005_;
}
v___jp_1011_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
return v___x_1013_;
}
v___jp_1014_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1016_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1015_);
lean_dec_ref(v___x_1016_);
goto v___jp_1011_;
}
v___jp_1017_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
return v___x_1019_;
}
v___jp_1020_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1022_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1021_);
lean_dec_ref(v___x_1022_);
goto v___jp_1017_;
}
v___jp_1023_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
return v___x_1025_;
}
v___jp_1026_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1028_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1027_);
lean_dec_ref(v___x_1028_);
goto v___jp_1023_;
}
v___jp_1029_:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
return v___x_1031_;
}
v___jp_1032_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1034_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1033_);
lean_dec_ref(v___x_1034_);
goto v___jp_1029_;
}
v___jp_1035_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
return v___x_1037_;
}
v___jp_1038_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1040_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1039_);
lean_dec_ref(v___x_1040_);
goto v___jp_1035_;
}
v___jp_1041_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
return v___x_1043_;
}
v___jp_1044_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1046_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1045_);
lean_dec_ref(v___x_1046_);
goto v___jp_1041_;
}
v___jp_1047_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lean_io_error_to_string(v___y_1048_);
v___x_1050_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1049_);
lean_dec_ref(v___x_1050_);
goto v___jp_1044_;
}
v___jp_1051_:
{
uint8_t v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = 1;
v___x_1053_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1052_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1061_; 
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1061_ == 0)
{
lean_object* v_unused_1062_; 
v_unused_1062_ = lean_ctor_get(v___x_1053_, 0);
lean_dec(v_unused_1062_);
v___x_1055_ = v___x_1053_;
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
else
{
lean_dec(v___x_1053_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1057_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_1056_ == 0)
{
lean_ctor_set_tag(v___x_1055_, 1);
lean_ctor_set(v___x_1055_, 0, v___x_1057_);
v___x_1059_ = v___x_1055_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v_a_1063_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1063_);
lean_dec_ref_known(v___x_1053_, 1);
v___x_1064_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1065_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1064_);
lean_dec_ref(v___x_1065_);
v___y_1048_ = v_a_1063_;
goto v___jp_1047_;
}
}
v___jp_1066_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__0));
v___x_1068_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1067_);
lean_dec_ref(v___x_1068_);
goto v___jp_1051_;
}
v___jp_1069_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
return v___x_1071_;
}
v___jp_1072_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1074_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1073_);
lean_dec_ref(v___x_1074_);
goto v___jp_1069_;
}
v___jp_1075_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
return v___x_1077_;
}
v___jp_1078_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1080_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1079_);
lean_dec_ref(v___x_1080_);
goto v___jp_1075_;
}
v___jp_1081_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
return v___x_1083_;
}
v___jp_1084_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1086_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1085_);
lean_dec_ref(v___x_1086_);
goto v___jp_1081_;
}
v___jp_1087_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
return v___x_1089_;
}
v___jp_1090_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1092_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1091_);
lean_dec_ref(v___x_1092_);
goto v___jp_1087_;
}
v___jp_1093_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = lean_io_error_to_string(v___y_1094_);
v___x_1096_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1095_);
lean_dec_ref(v___x_1096_);
goto v___jp_1090_;
}
v___jp_1097_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
return v___x_1099_;
}
v___jp_1100_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1102_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1101_);
lean_dec_ref(v___x_1102_);
goto v___jp_1097_;
}
v___jp_1103_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
return v___x_1105_;
}
v___jp_1106_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1108_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1107_);
lean_dec_ref(v___x_1108_);
goto v___jp_1103_;
}
v___jp_1109_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
return v___x_1111_;
}
v___jp_1112_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
return v___x_1114_;
}
v___jp_1115_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1117_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1116_);
lean_dec_ref(v___x_1117_);
goto v___jp_1112_;
}
v___jp_1118_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
return v___x_1120_;
}
v___jp_1121_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1123_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1122_);
lean_dec_ref(v___x_1123_);
goto v___jp_1118_;
}
v___jp_1124_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
return v___x_1126_;
}
v___jp_1127_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1129_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1128_);
lean_dec_ref(v___x_1129_);
goto v___jp_1124_;
}
v___jp_1130_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
return v___x_1132_;
}
v___jp_1133_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1135_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1134_);
lean_dec_ref(v___x_1135_);
goto v___jp_1130_;
}
v___jp_1136_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
return v___x_1138_;
}
v___jp_1139_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1141_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1140_);
lean_dec_ref(v___x_1141_);
goto v___jp_1136_;
}
v___jp_1142_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
return v___x_1144_;
}
v___jp_1145_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1147_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1146_);
lean_dec_ref(v___x_1147_);
goto v___jp_1142_;
}
v___jp_1148_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
return v___x_1150_;
}
v___jp_1151_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1153_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1152_);
lean_dec_ref(v___x_1153_);
goto v___jp_1148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed(lean_object* v_opts_2765_, lean_object* v_opt_2766_, lean_object* v_optArg_x3f_2767_, lean_object* v_a_2768_){
_start:
{
uint32_t v_opt_boxed_2769_; lean_object* v_res_2770_; 
v_opt_boxed_2769_ = lean_unbox_uint32(v_opt_2766_);
lean_dec(v_opt_2766_);
v_res_2770_ = lean_shell_options_process(v_opts_2765_, v_opt_boxed_2769_, v_optArg_x3f_2767_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically(lean_object* v_name_2772_, lean_object* v_f_2773_){
_start:
{
lean_object* v___x_2775_; 
v___x_2775_ = lean_uv_os_getpid();
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2811_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2778_ = v___x_2775_;
v_isShared_2779_ = v_isSharedCheck_2811_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2775_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2811_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2780_; uint64_t v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v_a_2787_; uint8_t v___x_2801_; lean_object* v___x_2802_; 
v___x_2780_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically___closed__0));
v___x_2781_ = lean_unbox_uint64(v_a_2776_);
lean_dec(v_a_2776_);
v___x_2782_ = lean_uint64_to_nat(v___x_2781_);
v___x_2783_ = l_Nat_reprFast(v___x_2782_);
v___x_2784_ = lean_string_append(v___x_2780_, v___x_2783_);
lean_dec_ref(v___x_2783_);
lean_inc_ref(v_name_2772_);
v___x_2785_ = l_System_FilePath_addExtension(v_name_2772_, v___x_2784_);
lean_dec_ref(v___x_2784_);
v___x_2801_ = 1;
v___x_2802_ = lean_io_prim_handle_mk(v___x_2785_, v___x_2801_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v___x_2804_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc_n(v_a_2803_, 2);
lean_dec_ref_known(v___x_2802_, 1);
v___x_2804_ = lean_apply_2(v_f_2773_, v_a_2803_, lean_box(0));
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v___x_2805_; 
lean_dec_ref_known(v___x_2804_, 1);
v___x_2805_ = lean_io_prim_handle_flush(v_a_2803_);
lean_dec(v_a_2803_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v___x_2806_; 
lean_dec_ref_known(v___x_2805_, 1);
v___x_2806_ = lean_io_rename(v___x_2785_, v_name_2772_);
lean_dec_ref(v_name_2772_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_dec_ref(v___x_2785_);
lean_del_object(v___x_2778_);
return v___x_2806_;
}
else
{
lean_object* v_a_2807_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2806_, 1);
v_a_2787_ = v_a_2807_;
goto v___jp_2786_;
}
}
else
{
lean_object* v_a_2808_; 
lean_dec_ref(v_name_2772_);
v_a_2808_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2805_, 1);
v_a_2787_ = v_a_2808_;
goto v___jp_2786_;
}
}
else
{
lean_object* v_a_2809_; 
lean_dec(v_a_2803_);
lean_dec_ref(v_name_2772_);
v_a_2809_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_a_2809_);
lean_dec_ref_known(v___x_2804_, 1);
v_a_2787_ = v_a_2809_;
goto v___jp_2786_;
}
}
else
{
lean_object* v_a_2810_; 
lean_dec_ref(v_f_2773_);
lean_dec_ref(v_name_2772_);
v_a_2810_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2810_);
lean_dec_ref_known(v___x_2802_, 1);
v_a_2787_ = v_a_2810_;
goto v___jp_2786_;
}
v___jp_2786_:
{
uint8_t v___x_2788_; 
v___x_2788_ = l_System_FilePath_pathExists(v___x_2785_);
if (v___x_2788_ == 0)
{
lean_object* v___x_2790_; 
lean_dec_ref(v___x_2785_);
if (v_isShared_2779_ == 0)
{
lean_ctor_set_tag(v___x_2778_, 1);
lean_ctor_set(v___x_2778_, 0, v_a_2787_);
v___x_2790_ = v___x_2778_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2787_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
else
{
lean_object* v___x_2792_; 
lean_del_object(v___x_2778_);
v___x_2792_ = lean_io_remove_file(v___x_2785_);
lean_dec_ref(v___x_2785_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2799_ == 0)
{
lean_object* v_unused_2800_; 
v_unused_2800_ = lean_ctor_get(v___x_2792_, 0);
lean_dec(v_unused_2800_);
v___x_2794_ = v___x_2792_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_dec(v___x_2792_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
lean_ctor_set_tag(v___x_2794_, 1);
lean_ctor_set(v___x_2794_, 0, v_a_2787_);
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2787_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
else
{
lean_dec(v_a_2787_);
return v___x_2792_;
}
}
}
}
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
lean_dec_ref(v_f_2773_);
lean_dec_ref(v_name_2772_);
v_a_2812_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2775_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2775_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically___boxed(lean_object* v_name_2820_, lean_object* v_f_2821_, lean_object* v_a_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically(v_name_2820_, v_f_2821_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object* v_opts_2824_, lean_object* v_opt_2825_){
_start:
{
lean_object* v_name_2826_; lean_object* v_defValue_2827_; lean_object* v_map_2828_; lean_object* v___x_2829_; 
v_name_2826_ = lean_ctor_get(v_opt_2825_, 0);
v_defValue_2827_ = lean_ctor_get(v_opt_2825_, 1);
v_map_2828_ = lean_ctor_get(v_opts_2824_, 0);
v___x_2829_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2828_, v_name_2826_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_inc(v_defValue_2827_);
return v_defValue_2827_;
}
else
{
lean_object* v_val_2830_; 
v_val_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_val_2830_);
lean_dec_ref_known(v___x_2829_, 1);
if (lean_obj_tag(v_val_2830_) == 3)
{
lean_object* v_v_2831_; 
v_v_2831_ = lean_ctor_get(v_val_2830_, 0);
lean_inc(v_v_2831_);
lean_dec_ref_known(v_val_2830_, 1);
return v_v_2831_;
}
else
{
lean_dec(v_val_2830_);
lean_inc(v_defValue_2827_);
return v_defValue_2827_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___boxed(lean_object* v_opts_2832_, lean_object* v_opt_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v_opts_2832_, v_opt_2833_);
lean_dec_ref(v_opt_2833_);
lean_dec_ref(v_opts_2832_);
return v_res_2834_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2837_ = lean_string_utf8_byte_size(v___x_2836_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(lean_object* v_s_2838_){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; uint8_t v___x_2842_; 
v___x_2839_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2840_ = lean_string_utf8_byte_size(v_s_2838_);
v___x_2841_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1);
v___x_2842_ = lean_nat_dec_le(v___x_2841_, v___x_2840_);
if (v___x_2842_ == 0)
{
lean_object* v___x_2843_; 
lean_dec_ref(v_s_2838_);
v___x_2843_ = lean_box(0);
return v___x_2843_;
}
else
{
lean_object* v___x_2844_; uint8_t v___x_2845_; 
v___x_2844_ = lean_unsigned_to_nat(0u);
v___x_2845_ = lean_string_memcmp(v_s_2838_, v___x_2839_, v___x_2844_, v___x_2844_, v___x_2841_);
if (v___x_2845_ == 0)
{
lean_object* v___x_2846_; 
lean_dec_ref(v_s_2838_);
v___x_2846_ = lean_box(0);
return v___x_2846_;
}
else
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
lean_inc_ref(v_s_2838_);
v___x_2847_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2847_, 0, v_s_2838_);
lean_ctor_set(v___x_2847_, 1, v___x_2844_);
lean_ctor_set(v___x_2847_, 2, v___x_2840_);
v___x_2848_ = l_String_Slice_pos_x21(v___x_2847_, v___x_2841_);
lean_dec_ref_known(v___x_2847_, 3);
v___x_2849_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2849_, 0, v_s_2838_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
lean_ctor_set(v___x_2849_, 2, v___x_2840_);
v___x_2850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
return v___x_2850_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(lean_object* v_s_2851_, lean_object* v_pat_2852_){
_start:
{
lean_object* v___x_2853_; 
v___x_2853_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v_s_2851_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___boxed(lean_object* v_s_2854_, lean_object* v_pat_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(v_s_2854_, v_pat_2855_);
lean_dec_ref(v_pat_2855_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object* v_x_2857_, lean_object* v_x_2858_, lean_object* v_v_2859_){
_start:
{
lean_inc_ref(v_v_2859_);
return v_v_2859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object* v_x_2860_, lean_object* v_x_2861_, lean_object* v_v_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l___private_Lean_Shell_0__Lean_shellMain___lam__0(v_x_2860_, v_x_2861_, v_v_2862_);
lean_dec_ref(v_v_2862_);
lean_dec_ref(v_x_2861_);
lean_dec(v_x_2860_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1(lean_object* v___x_2867_, lean_object* v_fileName_2868_, lean_object* v___x_2869_, lean_object* v___x_2870_, lean_object* v___x_2871_, lean_object* v___x_2872_, lean_object* v_mainModuleName_2873_, lean_object* v_out_2874_, uint8_t v___x_2875_, lean_object* v___x_2876_, lean_object* v___x_2877_, lean_object* v___x_2878_, lean_object* v___x_2879_, lean_object* v___x_2880_, lean_object* v___x_2881_, uint8_t v_run_2882_){
_start:
{
lean_object* v_a_2885_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v_env_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; uint8_t v___x_2896_; lean_object* v_toCold_2898_; lean_object* v_currRecDepth_2899_; lean_object* v_ref_2900_; lean_object* v_currNamespace_2901_; lean_object* v_openDecls_2902_; lean_object* v_initHeartbeats_2903_; lean_object* v_maxHeartbeats_2904_; lean_object* v_currMacroScope_2905_; uint8_t v_suppressElabErrors_2906_; lean_object* v___y_2907_; uint8_t v___y_2939_; uint8_t v___x_2959_; 
v___x_2888_ = lean_io_get_num_heartbeats();
v___x_2889_ = lean_st_mk_ref(v___x_2867_);
v___x_2890_ = l_Lean_inheritedTraceOptions;
v___x_2891_ = lean_st_ref_get(v___x_2890_);
v___x_2892_ = lean_st_ref_get(v___x_2889_);
v_env_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc_ref(v_env_2893_);
lean_dec(v___x_2892_);
lean_inc(v___x_2870_);
v___x_2894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2894_, 0, v_fileName_2868_);
lean_ctor_set(v___x_2894_, 1, v___x_2869_);
lean_ctor_set(v___x_2894_, 2, v___x_2870_);
lean_ctor_set(v___x_2894_, 3, v___x_2871_);
lean_ctor_set(v___x_2894_, 4, v___x_2891_);
v___x_2895_ = l_Lean_diagnostics;
v___x_2896_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v___x_2872_, v___x_2895_);
v___x_2959_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2893_);
lean_dec_ref(v_env_2893_);
if (v___x_2896_ == 0)
{
if (v___x_2959_ == 0)
{
lean_dec_ref(v___x_2876_);
lean_inc(v___x_2889_);
v_toCold_2898_ = v___x_2894_;
v_currRecDepth_2899_ = v___x_2877_;
v_ref_2900_ = v___x_2878_;
v_currNamespace_2901_ = v___x_2870_;
v_openDecls_2902_ = v___x_2879_;
v_initHeartbeats_2903_ = v___x_2888_;
v_maxHeartbeats_2904_ = v___x_2880_;
v_currMacroScope_2905_ = v___x_2881_;
v_suppressElabErrors_2906_ = v_run_2882_;
v___y_2907_ = v___x_2889_;
goto v___jp_2897_;
}
else
{
v___y_2939_ = v___x_2896_;
goto v___jp_2938_;
}
}
else
{
v___y_2939_ = v___x_2959_;
goto v___jp_2938_;
}
v___jp_2884_:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = lean_mk_io_user_error(v_a_2885_);
v___x_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
return v___x_2887_;
}
v___jp_2897_:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2908_ = l_Lean_maxRecDepth;
v___x_2909_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_2872_, v___x_2908_);
v___x_2910_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2910_, 0, v_toCold_2898_);
lean_ctor_set(v___x_2910_, 1, v___x_2872_);
lean_ctor_set(v___x_2910_, 2, v_currRecDepth_2899_);
lean_ctor_set(v___x_2910_, 3, v___x_2909_);
lean_ctor_set(v___x_2910_, 4, v_ref_2900_);
lean_ctor_set(v___x_2910_, 5, v_currNamespace_2901_);
lean_ctor_set(v___x_2910_, 6, v_openDecls_2902_);
lean_ctor_set(v___x_2910_, 7, v_initHeartbeats_2903_);
lean_ctor_set(v___x_2910_, 8, v_maxHeartbeats_2904_);
lean_ctor_set(v___x_2910_, 9, v_currMacroScope_2905_);
lean_ctor_set_uint8(v___x_2910_, sizeof(void*)*10, v___x_2896_);
lean_ctor_set_uint8(v___x_2910_, sizeof(void*)*10 + 1, v_suppressElabErrors_2906_);
v___x_2911_ = l_Lean_Compiler_LCNF_emitC(v_mainModuleName_2873_, v___x_2910_, v___y_2907_);
lean_dec(v___y_2907_);
lean_dec_ref_known(v___x_2910_, 10);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_a_2912_);
lean_dec_ref_known(v___x_2911_, 1);
v___x_2913_ = lean_st_ref_get(v___x_2889_);
lean_dec(v___x_2889_);
lean_dec(v___x_2913_);
v___x_2914_ = lean_string_to_utf8(v_a_2912_);
lean_dec(v_a_2912_);
v___x_2915_ = lean_io_prim_handle_write(v_out_2874_, v___x_2914_);
lean_dec_ref(v___x_2914_);
return v___x_2915_;
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2937_; 
lean_dec(v___x_2889_);
v_a_2916_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2918_ = v___x_2911_;
v_isShared_2919_ = v_isSharedCheck_2937_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2911_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2937_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
if (lean_obj_tag(v_a_2916_) == 0)
{
lean_object* v_msg_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2924_; 
v_msg_2920_ = lean_ctor_get(v_a_2916_, 1);
lean_inc_ref(v_msg_2920_);
lean_dec_ref_known(v_a_2916_, 2);
v___x_2921_ = l_Lean_MessageData_toString(v_msg_2920_);
v___x_2922_ = lean_mk_io_user_error(v___x_2921_);
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 0, v___x_2922_);
v___x_2924_ = v___x_2918_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2922_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
else
{
lean_object* v_id_2926_; lean_object* v___x_2927_; 
lean_del_object(v___x_2918_);
v_id_2926_ = lean_ctor_get(v_a_2916_, 0);
lean_inc(v_id_2926_);
lean_dec_ref_known(v_a_2916_, 2);
v___x_2927_ = l_Lean_InternalExceptionId_getName(v_id_2926_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
lean_dec(v_id_2926_);
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_a_2928_);
lean_dec_ref_known(v___x_2927_, 1);
v___x_2929_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__0));
v___x_2930_ = l_Lean_Name_toString(v_a_2928_, v___x_2875_);
v___x_2931_ = lean_string_append(v___x_2929_, v___x_2930_);
lean_dec_ref(v___x_2930_);
v_a_2885_ = v___x_2931_;
goto v___jp_2884_;
}
else
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
lean_dec_ref_known(v___x_2927_, 1);
v___x_2932_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__1));
v___x_2933_ = l_Nat_reprFast(v_id_2926_);
v___x_2934_ = lean_string_append(v___x_2932_, v___x_2933_);
lean_dec_ref(v___x_2933_);
v___x_2935_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__2));
v___x_2936_ = lean_string_append(v___x_2934_, v___x_2935_);
v_a_2885_ = v___x_2936_;
goto v___jp_2884_;
}
}
}
}
}
v___jp_2938_:
{
if (v___y_2939_ == 0)
{
lean_object* v___x_2940_; lean_object* v_env_2941_; lean_object* v_nextMacroScope_2942_; lean_object* v_ngen_2943_; lean_object* v_auxDeclNGen_2944_; lean_object* v_traceState_2945_; lean_object* v_messages_2946_; lean_object* v_infoState_2947_; lean_object* v_snapshotTasks_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2957_; 
v___x_2940_ = lean_st_ref_take(v___x_2889_);
v_env_2941_ = lean_ctor_get(v___x_2940_, 0);
v_nextMacroScope_2942_ = lean_ctor_get(v___x_2940_, 1);
v_ngen_2943_ = lean_ctor_get(v___x_2940_, 2);
v_auxDeclNGen_2944_ = lean_ctor_get(v___x_2940_, 3);
v_traceState_2945_ = lean_ctor_get(v___x_2940_, 4);
v_messages_2946_ = lean_ctor_get(v___x_2940_, 6);
v_infoState_2947_ = lean_ctor_get(v___x_2940_, 7);
v_snapshotTasks_2948_ = lean_ctor_get(v___x_2940_, 8);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2957_ == 0)
{
lean_object* v_unused_2958_; 
v_unused_2958_ = lean_ctor_get(v___x_2940_, 5);
lean_dec(v_unused_2958_);
v___x_2950_ = v___x_2940_;
v_isShared_2951_ = v_isSharedCheck_2957_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_snapshotTasks_2948_);
lean_inc(v_infoState_2947_);
lean_inc(v_messages_2946_);
lean_inc(v_traceState_2945_);
lean_inc(v_auxDeclNGen_2944_);
lean_inc(v_ngen_2943_);
lean_inc(v_nextMacroScope_2942_);
lean_inc(v_env_2941_);
lean_dec(v___x_2940_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2957_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2952_; lean_object* v___x_2954_; 
v___x_2952_ = l_Lean_Kernel_enableDiag(v_env_2941_, v___x_2896_);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 5, v___x_2876_);
lean_ctor_set(v___x_2950_, 0, v___x_2952_);
v___x_2954_ = v___x_2950_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v___x_2952_);
lean_ctor_set(v_reuseFailAlloc_2956_, 1, v_nextMacroScope_2942_);
lean_ctor_set(v_reuseFailAlloc_2956_, 2, v_ngen_2943_);
lean_ctor_set(v_reuseFailAlloc_2956_, 3, v_auxDeclNGen_2944_);
lean_ctor_set(v_reuseFailAlloc_2956_, 4, v_traceState_2945_);
lean_ctor_set(v_reuseFailAlloc_2956_, 5, v___x_2876_);
lean_ctor_set(v_reuseFailAlloc_2956_, 6, v_messages_2946_);
lean_ctor_set(v_reuseFailAlloc_2956_, 7, v_infoState_2947_);
lean_ctor_set(v_reuseFailAlloc_2956_, 8, v_snapshotTasks_2948_);
v___x_2954_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2955_; 
v___x_2955_ = lean_st_ref_put(v___x_2889_, v___x_2954_);
lean_inc(v___x_2889_);
v_toCold_2898_ = v___x_2894_;
v_currRecDepth_2899_ = v___x_2877_;
v_ref_2900_ = v___x_2878_;
v_currNamespace_2901_ = v___x_2870_;
v_openDecls_2902_ = v___x_2879_;
v_initHeartbeats_2903_ = v___x_2888_;
v_maxHeartbeats_2904_ = v___x_2880_;
v_currMacroScope_2905_ = v___x_2881_;
v_suppressElabErrors_2906_ = v_run_2882_;
v___y_2907_ = v___x_2889_;
goto v___jp_2897_;
}
}
}
else
{
lean_dec_ref(v___x_2876_);
lean_inc(v___x_2889_);
v_toCold_2898_ = v___x_2894_;
v_currRecDepth_2899_ = v___x_2877_;
v_ref_2900_ = v___x_2878_;
v_currNamespace_2901_ = v___x_2870_;
v_openDecls_2902_ = v___x_2879_;
v_initHeartbeats_2903_ = v___x_2888_;
v_maxHeartbeats_2904_ = v___x_2880_;
v_currMacroScope_2905_ = v___x_2881_;
v_suppressElabErrors_2906_ = v_run_2882_;
v___y_2907_ = v___x_2889_;
goto v___jp_2897_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed(lean_object** _args){
lean_object* v___x_2960_ = _args[0];
lean_object* v_fileName_2961_ = _args[1];
lean_object* v___x_2962_ = _args[2];
lean_object* v___x_2963_ = _args[3];
lean_object* v___x_2964_ = _args[4];
lean_object* v___x_2965_ = _args[5];
lean_object* v_mainModuleName_2966_ = _args[6];
lean_object* v_out_2967_ = _args[7];
lean_object* v___x_2968_ = _args[8];
lean_object* v___x_2969_ = _args[9];
lean_object* v___x_2970_ = _args[10];
lean_object* v___x_2971_ = _args[11];
lean_object* v___x_2972_ = _args[12];
lean_object* v___x_2973_ = _args[13];
lean_object* v___x_2974_ = _args[14];
lean_object* v_run_2975_ = _args[15];
lean_object* v___y_2976_ = _args[16];
_start:
{
uint8_t v___x_12464__boxed_2977_; uint8_t v_run_boxed_2978_; lean_object* v_res_2979_; 
v___x_12464__boxed_2977_ = lean_unbox(v___x_2968_);
v_run_boxed_2978_ = lean_unbox(v_run_2975_);
v_res_2979_ = l___private_Lean_Shell_0__Lean_shellMain___lam__1(v___x_2960_, v_fileName_2961_, v___x_2962_, v___x_2963_, v___x_2964_, v___x_2965_, v_mainModuleName_2966_, v_out_2967_, v___x_12464__boxed_2977_, v___x_2969_, v___x_2970_, v___x_2971_, v___x_2972_, v___x_2973_, v___x_2974_, v_run_boxed_2978_);
lean_dec(v_out_2967_);
return v_res_2979_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2981_ = l_Lean_Options_empty;
v___x_2982_ = l_Lean_Core_getMaxHeartbeats(v___x_2981_);
return v___x_2982_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2983_ = lean_unsigned_to_nat(1u);
v___x_2984_ = l_Lean_firstFrontendMacroScope;
v___x_2985_ = lean_nat_add(v___x_2984_, v___x_2983_);
return v___x_2985_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__7(void){
_start:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2996_ = lean_unsigned_to_nat(32u);
v___x_2997_ = lean_mk_empty_array_with_capacity(v___x_2996_);
v___x_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
return v___x_2998_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__8(void){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2999_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9(void){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_3000_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__8, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__8_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__8);
v___x_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
return v___x_3001_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__10(void){
_start:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3002_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9);
v___x_3003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
lean_ctor_set(v___x_3003_, 1, v___x_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2(lean_object* v___x_3004_, uint8_t v___x_3005_, lean_object* v_val_3006_, lean_object* v_fileName_3007_, lean_object* v_mainModuleName_3008_, uint8_t v_run_3009_, lean_object* v___x_3010_, lean_object* v_out_3011_){
_start:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; uint64_t v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; size_t v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___f_3041_; lean_object* v___x_3042_; 
v___x_3013_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__0));
v___x_3014_ = l_Lean_instInhabitedFileMap_default;
v___x_3015_ = lean_box(0);
v___x_3016_ = lean_box(0);
v___x_3017_ = l_Lean_Options_empty;
v___x_3018_ = lean_box(0);
v___x_3019_ = lean_box(0);
v___x_3020_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__1, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__1_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__1);
v___x_3021_ = l_Lean_firstFrontendMacroScope;
v___x_3022_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__2, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__2_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__2);
v___x_3023_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__5));
v___x_3024_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__6));
v___x_3025_ = 0ULL;
v___x_3026_ = lean_unsigned_to_nat(32u);
v___x_3027_ = lean_mk_empty_array_with_capacity(v___x_3026_);
v___x_3028_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__7, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__7_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__7);
v___x_3029_ = ((size_t)5ULL);
lean_inc_n(v___x_3004_, 2);
v___x_3030_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3030_, 0, v___x_3028_);
lean_ctor_set(v___x_3030_, 1, v___x_3027_);
lean_ctor_set(v___x_3030_, 2, v___x_3004_);
lean_ctor_set(v___x_3030_, 3, v___x_3004_);
lean_ctor_set_usize(v___x_3030_, 4, v___x_3029_);
lean_inc_ref_n(v___x_3030_, 3);
v___x_3031_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3031_, 0, v___x_3030_);
lean_ctor_set_uint64(v___x_3031_, sizeof(void*)*1, v___x_3025_);
v___x_3032_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9);
v___x_3033_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__10, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__10_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__10);
v___x_3034_ = l_Lean_NameSet_empty;
v___x_3035_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3030_);
lean_ctor_set(v___x_3035_, 1, v___x_3030_);
lean_ctor_set(v___x_3035_, 2, v___x_3034_);
v___x_3036_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3036_, 0, v___x_3032_);
lean_ctor_set(v___x_3036_, 1, v___x_3032_);
lean_ctor_set(v___x_3036_, 2, v___x_3030_);
lean_ctor_set_uint8(v___x_3036_, sizeof(void*)*3, v___x_3005_);
v___x_3037_ = lean_mk_empty_array_with_capacity(v___x_3004_);
v___x_3038_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3038_, 0, v_val_3006_);
lean_ctor_set(v___x_3038_, 1, v___x_3022_);
lean_ctor_set(v___x_3038_, 2, v___x_3023_);
lean_ctor_set(v___x_3038_, 3, v___x_3024_);
lean_ctor_set(v___x_3038_, 4, v___x_3031_);
lean_ctor_set(v___x_3038_, 5, v___x_3033_);
lean_ctor_set(v___x_3038_, 6, v___x_3035_);
lean_ctor_set(v___x_3038_, 7, v___x_3036_);
lean_ctor_set(v___x_3038_, 8, v___x_3037_);
v___x_3039_ = lean_box(v___x_3005_);
v___x_3040_ = lean_box(v_run_3009_);
v___f_3041_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed), 17, 16);
lean_closure_set(v___f_3041_, 0, v___x_3038_);
lean_closure_set(v___f_3041_, 1, v_fileName_3007_);
lean_closure_set(v___f_3041_, 2, v___x_3014_);
lean_closure_set(v___f_3041_, 3, v___x_3015_);
lean_closure_set(v___f_3041_, 4, v___x_3016_);
lean_closure_set(v___f_3041_, 5, v___x_3017_);
lean_closure_set(v___f_3041_, 6, v_mainModuleName_3008_);
lean_closure_set(v___f_3041_, 7, v_out_3011_);
lean_closure_set(v___f_3041_, 8, v___x_3039_);
lean_closure_set(v___f_3041_, 9, v___x_3033_);
lean_closure_set(v___f_3041_, 10, v___x_3004_);
lean_closure_set(v___f_3041_, 11, v___x_3018_);
lean_closure_set(v___f_3041_, 12, v___x_3019_);
lean_closure_set(v___f_3041_, 13, v___x_3020_);
lean_closure_set(v___f_3041_, 14, v___x_3021_);
lean_closure_set(v___f_3041_, 15, v___x_3040_);
v___x_3042_ = l_Lean_profileitIOUnsafe___redArg(v___x_3013_, v___x_3010_, v___f_3041_, v___x_3015_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2___boxed(lean_object* v___x_3043_, lean_object* v___x_3044_, lean_object* v_val_3045_, lean_object* v_fileName_3046_, lean_object* v_mainModuleName_3047_, lean_object* v_run_3048_, lean_object* v___x_3049_, lean_object* v_out_3050_, lean_object* v___y_3051_){
_start:
{
uint8_t v___x_12671__boxed_3052_; uint8_t v_run_boxed_3053_; lean_object* v_res_3054_; 
v___x_12671__boxed_3052_ = lean_unbox(v___x_3044_);
v_run_boxed_3053_ = lean_unbox(v_run_3048_);
v_res_3054_ = l___private_Lean_Shell_0__Lean_shellMain___lam__2(v___x_3043_, v___x_12671__boxed_3052_, v_val_3045_, v_fileName_3046_, v_mainModuleName_3047_, v_run_boxed_3053_, v___x_3049_, v_out_3050_);
lean_dec_ref(v___x_3049_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(lean_object* v_val_3055_, lean_object* v_a_3056_, lean_object* v_b_3057_){
_start:
{
lean_object* v_str_3058_; lean_object* v_startInclusive_3059_; lean_object* v_endExclusive_3060_; lean_object* v___x_3061_; uint8_t v_decide_3062_; 
v_str_3058_ = lean_ctor_get(v_val_3055_, 0);
v_startInclusive_3059_ = lean_ctor_get(v_val_3055_, 1);
v_endExclusive_3060_ = lean_ctor_get(v_val_3055_, 2);
v___x_3061_ = lean_nat_sub(v_endExclusive_3060_, v_startInclusive_3059_);
v_decide_3062_ = lean_nat_dec_eq(v_a_3056_, v___x_3061_);
lean_dec(v___x_3061_);
if (v_decide_3062_ == 0)
{
lean_object* v___x_3063_; uint32_t v___x_3064_; uint32_t v___x_3065_; uint8_t v___x_3066_; 
v___x_3063_ = lean_nat_add(v_startInclusive_3059_, v_a_3056_);
v___x_3064_ = lean_string_utf8_get_fast(v_str_3058_, v___x_3063_);
v___x_3065_ = 10;
v___x_3066_ = lean_uint32_dec_eq(v___x_3064_, v___x_3065_);
if (v___x_3066_ == 0)
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
lean_dec(v_a_3056_);
v___x_3067_ = lean_box(0);
v___x_3068_ = lean_string_utf8_next_fast(v_str_3058_, v___x_3063_);
lean_dec(v___x_3063_);
v___x_3069_ = lean_nat_sub(v___x_3068_, v_startInclusive_3059_);
v_a_3056_ = v___x_3069_;
v_b_3057_ = v___x_3067_;
goto _start;
}
else
{
lean_object* v___x_3071_; 
lean_dec(v___x_3063_);
v___x_3071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3071_, 0, v_a_3056_);
return v___x_3071_;
}
}
else
{
lean_dec(v_a_3056_);
lean_inc(v_b_3057_);
return v_b_3057_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg___boxed(lean_object* v_val_3072_, lean_object* v_a_3073_, lean_object* v_b_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3072_, v_a_3073_, v_b_3074_);
lean_dec(v_b_3074_);
lean_dec_ref(v_val_3072_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(lean_object* v_s_3076_){
_start:
{
uint32_t v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3078_ = 10;
v___x_3079_ = lean_string_push(v_s_3076_, v___x_3078_);
v___x_3080_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_3079_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___boxed(lean_object* v_s_3081_, lean_object* v_a_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_s_3081_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(lean_object* v_s_3084_){
_start:
{
uint32_t v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3086_ = 10;
v___x_3087_ = lean_string_push(v_s_3084_, v___x_3086_);
v___x_3088_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_3087_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4___boxed(lean_object* v_s_3089_, lean_object* v_a_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_s_3089_);
return v_res_3091_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shellMain___closed__1(void){
_start:
{
lean_object* v___x_3093_; uint8_t v___x_3094_; 
v___x_3093_ = lean_box(0);
v___x_3094_ = lean_internal_has_address_sanitizer(v___x_3093_);
return v___x_3094_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__2(void){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3095_ = lean_box(0);
v___x_3096_ = lean_internal_get_option_overrides(v___x_3095_);
return v___x_3096_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__9(void){
_start:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3105_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__8));
v___x_3106_ = lean_string_utf8_byte_size(v___x_3105_);
return v___x_3106_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10(void){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3107_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__9, &l___private_Lean_Shell_0__Lean_shellMain___closed__9_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__9);
v___x_3108_ = lean_unsigned_to_nat(0u);
v___x_3109_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__8));
v___x_3110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3109_);
lean_ctor_set(v___x_3110_, 1, v___x_3108_);
lean_ctor_set(v___x_3110_, 2, v___x_3107_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* lean_shell_main(lean_object* v_args_3113_, lean_object* v_opts_3114_){
_start:
{
lean_object* v_fns_3117_; uint8_t v_printPrefix_3142_; 
v_printPrefix_3142_ = lean_ctor_get_uint8(v_opts_3114_, sizeof(void*)*13 + 9);
if (v_printPrefix_3142_ == 0)
{
uint8_t v_printLibDir_3143_; 
v_printLibDir_3143_ = lean_ctor_get_uint8(v_opts_3114_, sizeof(void*)*13 + 10);
if (v_printLibDir_3143_ == 0)
{
lean_object* v_leanOpts_3144_; lean_object* v_forwardedArgs_3145_; uint8_t v_component_3146_; uint8_t v_useStdin_3147_; uint8_t v_onlyDeps_3148_; uint8_t v_onlySrcDeps_3149_; uint8_t v_depsJson_3150_; uint32_t v_trustLevel_3151_; lean_object* v_rootDir_x3f_3152_; lean_object* v_setupFileName_x3f_3153_; lean_object* v_oleanFileName_x3f_3154_; lean_object* v_ileanFileName_x3f_3155_; lean_object* v_cFileName_x3f_3156_; lean_object* v_bcFileName_x3f_3157_; uint8_t v_jsonOutput_3158_; lean_object* v_errorOnKinds_3159_; uint8_t v_printStats_3160_; uint8_t v_run_3161_; lean_object* v_incrSaveFileName_x3f_3162_; lean_object* v_incrLoadFileName_x3f_3163_; lean_object* v_incrHeaderSaveFileName_x3f_3164_; lean_object* v___f_3165_; lean_object* v___y_3167_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; uint8_t v___x_3209_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v_mainModuleName_3245_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v_contents_3304_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v_str_3333_; lean_object* v_startInclusive_3334_; lean_object* v_endExclusive_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v_fileName_3436_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3474_; lean_object* v___y_3475_; uint8_t v___y_3476_; uint8_t v___y_3479_; lean_object* v_fst_3480_; lean_object* v_snd_3481_; uint8_t v___y_3483_; lean_object* v___x_3513_; lean_object* v_maxMemory_3514_; lean_object* v___x_3515_; uint8_t v___x_3516_; 
v_leanOpts_3144_ = lean_ctor_get(v_opts_3114_, 0);
lean_inc_ref(v_leanOpts_3144_);
v_forwardedArgs_3145_ = lean_ctor_get(v_opts_3114_, 1);
lean_inc_ref(v_forwardedArgs_3145_);
v_component_3146_ = lean_ctor_get_uint8(v_opts_3114_, sizeof(void*)*13 + 8);
v_useStdin_3147_ = lean_ctor_get_uint8(v_opts_3114_, sizeof(void*)*13 + 11);
v_onlyDeps_3148_ = lean_ctor_get_uint8(v_opts_3114_, sizeof(void*)*13 + 12);
v_onlySrcDeps_3149_ = lean_ctor_get_uint8(v_opts_3114_, sizeof(void*)*13 + 13);
v_depsJson_3150_ = lean_ctor_get_uint8(v_opts_3114_, sizeof(void*)*13 + 14);
v_trustLevel_3151_ = lean_ctor_get_uint32(v_opts_3114_, sizeof(void*)*13);
v_rootDir_x3f_3152_ = lean_ctor_get(v_opts_3114_, 3);
lean_inc(v_rootDir_x3f_3152_);
v_setupFileName_x3f_3153_ = lean_ctor_get(v_opts_3114_, 4);
lean_inc(v_setupFileName_x3f_3153_);
v_oleanFileName_x3f_3154_ = lean_ctor_get(v_opts_3114_, 5);
lean_inc(v_oleanFileName_x3f_3154_);
v_ileanFileName_x3f_3155_ = lean_ctor_get(v_opts_3114_, 6);
lean_inc(v_ileanFileName_x3f_3155_);
v_cFileName_x3f_3156_ = lean_ctor_get(v_opts_3114_, 7);
lean_inc(v_cFileName_x3f_3156_);
v_bcFileName_x3f_3157_ = lean_ctor_get(v_opts_3114_, 8);
lean_inc(v_bcFileName_x3f_3157_);
v_jsonOutput_3158_ = lean_ctor_get_uint8(v_opts_3114_, sizeof(void*)*13 + 15);
v_errorOnKinds_3159_ = lean_ctor_get(v_opts_3114_, 9);
lean_inc_ref(v_errorOnKinds_3159_);
v_printStats_3160_ = lean_ctor_get_uint8(v_opts_3114_, sizeof(void*)*13 + 16);
v_run_3161_ = lean_ctor_get_uint8(v_opts_3114_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_3162_ = lean_ctor_get(v_opts_3114_, 10);
lean_inc(v_incrSaveFileName_x3f_3162_);
v_incrLoadFileName_x3f_3163_ = lean_ctor_get(v_opts_3114_, 11);
lean_inc(v_incrLoadFileName_x3f_3163_);
v_incrHeaderSaveFileName_x3f_3164_ = lean_ctor_get(v_opts_3114_, 12);
lean_inc(v_incrHeaderSaveFileName_x3f_3164_);
lean_dec_ref(v_opts_3114_);
v___f_3165_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__0));
v___x_3181_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__2, &l___private_Lean_Shell_0__Lean_shellMain___closed__2_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__2);
v___x_3182_ = l_Lean_Options_mergeBy(v___f_3165_, v_leanOpts_3144_, v___x_3181_);
v___x_3209_ = 1;
v___x_3513_ = l___private_Lean_Shell_0__Lean_maxMemory;
v_maxMemory_3514_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3182_, v___x_3513_);
v___x_3515_ = lean_unsigned_to_nat(0u);
v___x_3516_ = lean_nat_dec_eq(v_maxMemory_3514_, v___x_3515_);
if (v___x_3516_ == 0)
{
size_t v___x_3517_; size_t v___x_3518_; size_t v___x_3519_; size_t v___x_3520_; lean_object* v___x_3521_; 
v___x_3517_ = lean_usize_of_nat(v_maxMemory_3514_);
lean_dec(v_maxMemory_3514_);
v___x_3518_ = ((size_t)10ULL);
v___x_3519_ = lean_usize_shift_left(v___x_3517_, v___x_3518_);
v___x_3520_ = lean_usize_shift_left(v___x_3519_, v___x_3518_);
v___x_3521_ = lean_internal_set_max_memory(v___x_3520_);
goto v___jp_3504_;
}
else
{
lean_dec(v_maxMemory_3514_);
goto v___jp_3504_;
}
v___jp_3166_:
{
lean_object* v___x_3168_; uint8_t v___x_3169_; 
v___x_3168_ = lean_display_cumulative_profiling_times();
v___x_3169_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__1, &l___private_Lean_Shell_0__Lean_shellMain___closed__1_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__1);
if (v___x_3169_ == 0)
{
if (lean_obj_tag(v___y_3167_) == 0)
{
if (v___x_3169_ == 0)
{
uint8_t v___x_3170_; lean_object* v___x_3171_; 
v___x_3170_ = 1;
v___x_3171_ = lean_io_exit(v___x_3170_);
return v___x_3171_;
}
else
{
goto v___jp_3136_;
}
}
else
{
lean_dec_ref_known(v___y_3167_, 1);
goto v___jp_3136_;
}
}
else
{
if (lean_obj_tag(v___y_3167_) == 0)
{
goto v___jp_3139_;
}
else
{
lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3179_; 
v_isSharedCheck_3179_ = !lean_is_exclusive(v___y_3167_);
if (v_isSharedCheck_3179_ == 0)
{
lean_object* v_unused_3180_; 
v_unused_3180_ = lean_ctor_get(v___y_3167_, 0);
lean_dec(v_unused_3180_);
v___x_3173_ = v___y_3167_;
v_isShared_3174_ = v_isSharedCheck_3179_;
goto v_resetjp_3172_;
}
else
{
lean_dec(v___y_3167_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3179_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
if (v___x_3169_ == 0)
{
lean_del_object(v___x_3173_);
goto v___jp_3139_;
}
else
{
lean_object* v___x_3175_; lean_object* v___x_3177_; 
v___x_3175_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3174_ == 0)
{
lean_ctor_set_tag(v___x_3173_, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3175_);
v___x_3177_ = v___x_3173_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v___x_3175_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
}
}
v___jp_3183_:
{
if (lean_obj_tag(v_bcFileName_x3f_3157_) == 1)
{
lean_object* v_val_3187_; lean_object* v___x_3188_; 
v_val_3187_ = lean_ctor_get(v_bcFileName_x3f_3157_, 0);
lean_inc(v_val_3187_);
lean_dec_ref_known(v_bcFileName_x3f_3157_, 1);
v___x_3188_ = lean_init_llvm();
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
lean_dec_ref_known(v___x_3188_, 1);
v___x_3189_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__3));
v___x_3190_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_emitLLVM___boxed), 4, 3);
lean_closure_set(v___x_3190_, 0, v___y_3186_);
lean_closure_set(v___x_3190_, 1, v___y_3185_);
lean_closure_set(v___x_3190_, 2, v_val_3187_);
v___x_3191_ = lean_box(0);
v___x_3192_ = l_Lean_profileitIOUnsafe___redArg(v___x_3189_, v___x_3182_, v___x_3190_, v___x_3191_);
lean_dec_ref(v___x_3182_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_dec_ref_known(v___x_3192_, 1);
v___y_3167_ = v___y_3184_;
goto v___jp_3166_;
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
lean_dec(v___y_3184_);
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3192_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3192_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
else
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
lean_dec(v_val_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___x_3182_);
v_a_3201_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_3188_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3188_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
else
{
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___x_3182_);
lean_dec(v_bcFileName_x3f_3157_);
v___y_3167_ = v___y_3184_;
goto v___jp_3166_;
}
}
v___jp_3210_:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3211_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__4));
v___x_3212_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_3211_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v___x_3213_; 
lean_dec_ref_known(v___x_3212_, 1);
v___x_3213_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_3209_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3221_; 
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3221_ == 0)
{
lean_object* v_unused_3222_; 
v_unused_3222_ = lean_ctor_get(v___x_3213_, 0);
lean_dec(v_unused_3222_);
v___x_3215_ = v___x_3213_;
v_isShared_3216_ = v_isSharedCheck_3221_;
goto v_resetjp_3214_;
}
else
{
lean_dec(v___x_3213_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3221_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3217_; lean_object* v___x_3219_; 
v___x_3217_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 0, v___x_3217_);
v___x_3219_ = v___x_3215_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3217_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
else
{
lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3230_; 
v_a_3223_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3225_ = v___x_3213_;
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3213_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3228_; 
if (v_isShared_3226_ == 0)
{
v___x_3228_ = v___x_3225_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_a_3223_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
}
else
{
lean_object* v_a_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3238_; 
v_a_3231_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3233_ = v___x_3212_;
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_a_3231_);
lean_dec(v___x_3212_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3236_; 
if (v_isShared_3234_ == 0)
{
v___x_3236_ = v___x_3233_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_a_3231_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
}
v___jp_3239_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3246_ = lean_unsigned_to_nat(0u);
v___x_3247_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__5));
lean_inc(v_mainModuleName_3245_);
lean_inc_ref(v___x_3182_);
v___x_3248_ = l_Lean_Elab_runFrontend(v___y_3242_, v___x_3182_, v___y_3243_, v_mainModuleName_3245_, v_trustLevel_3151_, v_oleanFileName_x3f_3154_, v_ileanFileName_x3f_3155_, v_jsonOutput_3158_, v_errorOnKinds_3159_, v___x_3247_, v_printStats_3160_, v___y_3244_, v_incrSaveFileName_x3f_3162_, v_incrLoadFileName_x3f_3163_, v_incrHeaderSaveFileName_x3f_3164_);
lean_dec_ref(v_errorOnKinds_3159_);
lean_dec(v_ileanFileName_x3f_3155_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3274_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3251_ = v___x_3248_;
v_isShared_3252_ = v_isSharedCheck_3274_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3248_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3274_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
if (lean_obj_tag(v_a_3249_) == 1)
{
if (v_run_3161_ == 0)
{
lean_del_object(v___x_3251_);
lean_dec(v___y_3241_);
if (lean_obj_tag(v_cFileName_x3f_3156_) == 1)
{
lean_object* v_val_3253_; lean_object* v_val_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___f_3257_; lean_object* v___x_3258_; 
v_val_3253_ = lean_ctor_get(v_a_3249_, 0);
lean_inc_n(v_val_3253_, 2);
v_val_3254_ = lean_ctor_get(v_cFileName_x3f_3156_, 0);
lean_inc(v_val_3254_);
lean_dec_ref_known(v_cFileName_x3f_3156_, 1);
v___x_3255_ = lean_box(v___x_3209_);
v___x_3256_ = lean_box(v_run_3161_);
lean_inc_ref(v___x_3182_);
lean_inc(v_mainModuleName_3245_);
v___f_3257_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__2___boxed), 9, 7);
lean_closure_set(v___f_3257_, 0, v___x_3246_);
lean_closure_set(v___f_3257_, 1, v___x_3255_);
lean_closure_set(v___f_3257_, 2, v_val_3253_);
lean_closure_set(v___f_3257_, 3, v___y_3240_);
lean_closure_set(v___f_3257_, 4, v_mainModuleName_3245_);
lean_closure_set(v___f_3257_, 5, v___x_3256_);
lean_closure_set(v___f_3257_, 6, v___x_3182_);
v___x_3258_ = l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically(v_val_3254_, v___f_3257_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_dec_ref_known(v___x_3258_, 1);
v___y_3184_ = v_a_3249_;
v___y_3185_ = v_mainModuleName_3245_;
v___y_3186_ = v_val_3253_;
goto v___jp_3183_;
}
else
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3266_; 
lean_dec(v_val_3253_);
lean_dec_ref_known(v_a_3249_, 1);
lean_dec(v_mainModuleName_3245_);
lean_dec_ref(v___x_3182_);
lean_dec(v_bcFileName_x3f_3157_);
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3261_ = v___x_3258_;
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3258_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3264_; 
if (v_isShared_3262_ == 0)
{
v___x_3264_ = v___x_3261_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_a_3259_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
else
{
lean_object* v_val_3267_; 
lean_dec_ref(v___y_3240_);
lean_dec(v_cFileName_x3f_3156_);
v_val_3267_ = lean_ctor_get(v_a_3249_, 0);
lean_inc(v_val_3267_);
v___y_3184_ = v_a_3249_;
v___y_3185_ = v_mainModuleName_3245_;
v___y_3186_ = v_val_3267_;
goto v___jp_3183_;
}
}
else
{
lean_object* v_val_3268_; uint32_t v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3272_; 
lean_dec(v_mainModuleName_3245_);
lean_dec_ref(v___y_3240_);
lean_dec(v_bcFileName_x3f_3157_);
lean_dec(v_cFileName_x3f_3156_);
v_val_3268_ = lean_ctor_get(v_a_3249_, 0);
lean_inc(v_val_3268_);
lean_dec_ref_known(v_a_3249_, 1);
v___x_3269_ = lean_eval_main(v_val_3268_, v___x_3182_, v___y_3241_);
lean_dec(v___y_3241_);
lean_dec_ref(v___x_3182_);
lean_dec(v_val_3268_);
v___x_3270_ = lean_box_uint32(v___x_3269_);
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 0, v___x_3270_);
v___x_3272_ = v___x_3251_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3270_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
else
{
lean_del_object(v___x_3251_);
lean_dec(v_mainModuleName_3245_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec_ref(v___x_3182_);
lean_dec(v_bcFileName_x3f_3157_);
lean_dec(v_cFileName_x3f_3156_);
v___y_3167_ = v_a_3249_;
goto v___jp_3166_;
}
}
}
else
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3282_; 
lean_dec(v_mainModuleName_3245_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec_ref(v___x_3182_);
lean_dec(v_bcFileName_x3f_3157_);
lean_dec(v_cFileName_x3f_3156_);
v_a_3275_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3277_ = v___x_3248_;
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3248_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3280_; 
if (v_isShared_3278_ == 0)
{
v___x_3280_ = v___x_3277_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3275_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
}
v___jp_3283_:
{
if (lean_obj_tag(v___y_3289_) == 0)
{
lean_object* v_a_3290_; 
v_a_3290_ = lean_ctor_get(v___y_3289_, 0);
lean_inc(v_a_3290_);
lean_dec_ref_known(v___y_3289_, 1);
v___y_3240_ = v___y_3284_;
v___y_3241_ = v___y_3285_;
v___y_3242_ = v___y_3286_;
v___y_3243_ = v___y_3287_;
v___y_3244_ = v___y_3288_;
v_mainModuleName_3245_ = v_a_3290_;
goto v___jp_3239_;
}
else
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3298_; 
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec_ref(v___x_3182_);
lean_dec(v_incrHeaderSaveFileName_x3f_3164_);
lean_dec(v_incrLoadFileName_x3f_3163_);
lean_dec(v_incrSaveFileName_x3f_3162_);
lean_dec_ref(v_errorOnKinds_3159_);
lean_dec(v_bcFileName_x3f_3157_);
lean_dec(v_cFileName_x3f_3156_);
lean_dec(v_ileanFileName_x3f_3155_);
lean_dec(v_oleanFileName_x3f_3154_);
v_a_3291_ = lean_ctor_get(v___y_3289_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___y_3289_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3293_ = v___y_3289_;
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___y_3289_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3296_; 
if (v_isShared_3294_ == 0)
{
v___x_3296_ = v___x_3293_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3291_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
}
}
v___jp_3299_:
{
if (lean_obj_tag(v_setupFileName_x3f_3153_) == 0)
{
lean_object* v___x_3305_; 
v___x_3305_ = lean_box(0);
if (lean_obj_tag(v___y_3302_) == 1)
{
lean_object* v_val_3306_; lean_object* v___x_3307_; 
v_val_3306_ = lean_ctor_get(v___y_3302_, 0);
lean_inc(v_val_3306_);
lean_dec_ref_known(v___y_3302_, 1);
v___x_3307_ = l_Lean_moduleNameOfFileName(v_val_3306_, v_rootDir_x3f_3152_);
if (lean_obj_tag(v___x_3307_) == 0)
{
v___y_3284_ = v___y_3300_;
v___y_3285_ = v___y_3301_;
v___y_3286_ = v_contents_3304_;
v___y_3287_ = v___y_3303_;
v___y_3288_ = v___x_3305_;
v___y_3289_ = v___x_3307_;
goto v___jp_3283_;
}
else
{
if (lean_obj_tag(v_oleanFileName_x3f_3154_) == 0)
{
if (lean_obj_tag(v_cFileName_x3f_3156_) == 0)
{
lean_object* v___x_3308_; 
lean_dec_ref_known(v___x_3307_, 1);
v___x_3308_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__7));
v___y_3240_ = v___y_3300_;
v___y_3241_ = v___y_3301_;
v___y_3242_ = v_contents_3304_;
v___y_3243_ = v___y_3303_;
v___y_3244_ = v___x_3305_;
v_mainModuleName_3245_ = v___x_3308_;
goto v___jp_3239_;
}
else
{
v___y_3284_ = v___y_3300_;
v___y_3285_ = v___y_3301_;
v___y_3286_ = v_contents_3304_;
v___y_3287_ = v___y_3303_;
v___y_3288_ = v___x_3305_;
v___y_3289_ = v___x_3307_;
goto v___jp_3283_;
}
}
else
{
v___y_3284_ = v___y_3300_;
v___y_3285_ = v___y_3301_;
v___y_3286_ = v_contents_3304_;
v___y_3287_ = v___y_3303_;
v___y_3288_ = v___x_3305_;
v___y_3289_ = v___x_3307_;
goto v___jp_3283_;
}
}
}
else
{
lean_object* v___x_3309_; 
lean_dec(v___y_3302_);
lean_dec(v_rootDir_x3f_3152_);
v___x_3309_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__7));
v___y_3240_ = v___y_3300_;
v___y_3241_ = v___y_3301_;
v___y_3242_ = v_contents_3304_;
v___y_3243_ = v___y_3303_;
v___y_3244_ = v___x_3305_;
v_mainModuleName_3245_ = v___x_3309_;
goto v___jp_3239_;
}
}
else
{
lean_object* v_val_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3328_; 
lean_dec(v___y_3302_);
lean_dec(v_rootDir_x3f_3152_);
v_val_3310_ = lean_ctor_get(v_setupFileName_x3f_3153_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v_setupFileName_x3f_3153_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3312_ = v_setupFileName_x3f_3153_;
v_isShared_3313_ = v_isSharedCheck_3328_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_val_3310_);
lean_dec(v_setupFileName_x3f_3153_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3328_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3314_; 
v___x_3314_ = l_Lean_ModuleSetup_load(v_val_3310_);
lean_dec(v_val_3310_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v_a_3315_; lean_object* v_name_3316_; lean_object* v___x_3318_; 
v_a_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc(v_a_3315_);
lean_dec_ref_known(v___x_3314_, 1);
v_name_3316_ = lean_ctor_get(v_a_3315_, 0);
lean_inc(v_name_3316_);
if (v_isShared_3313_ == 0)
{
lean_ctor_set(v___x_3312_, 0, v_a_3315_);
v___x_3318_ = v___x_3312_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_a_3315_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
v___y_3240_ = v___y_3300_;
v___y_3241_ = v___y_3301_;
v___y_3242_ = v_contents_3304_;
v___y_3243_ = v___y_3303_;
v___y_3244_ = v___x_3318_;
v_mainModuleName_3245_ = v_name_3316_;
goto v___jp_3239_;
}
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
lean_del_object(v___x_3312_);
lean_dec_ref(v_contents_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec_ref(v___x_3182_);
lean_dec(v_incrHeaderSaveFileName_x3f_3164_);
lean_dec(v_incrLoadFileName_x3f_3163_);
lean_dec(v_incrSaveFileName_x3f_3162_);
lean_dec_ref(v_errorOnKinds_3159_);
lean_dec(v_bcFileName_x3f_3157_);
lean_dec(v_cFileName_x3f_3156_);
lean_dec(v_ileanFileName_x3f_3155_);
lean_dec(v_oleanFileName_x3f_3154_);
v_a_3320_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v___x_3314_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3314_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
}
}
v___jp_3329_:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; uint8_t v___x_3342_; 
v___x_3338_ = lean_nat_add(v_startInclusive_3334_, v___y_3337_);
lean_dec(v___y_3337_);
lean_inc(v___x_3338_);
lean_inc_ref(v_str_3333_);
v___x_3339_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3339_, 0, v_str_3333_);
lean_ctor_set(v___x_3339_, 1, v_startInclusive_3334_);
lean_ctor_set(v___x_3339_, 2, v___x_3338_);
v___x_3340_ = l_String_Slice_trimAscii(v___x_3339_);
v___x_3341_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__10, &l___private_Lean_Shell_0__Lean_shellMain___closed__10_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10);
v___x_3342_ = l_String_Slice_beq(v___x_3340_, v___x_3341_);
if (v___x_3342_ == 0)
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
lean_dec(v___x_3338_);
lean_dec_ref(v___y_3336_);
lean_dec(v_endExclusive_3335_);
lean_dec_ref(v_str_3333_);
lean_dec(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec_ref(v___x_3182_);
lean_dec(v_incrHeaderSaveFileName_x3f_3164_);
lean_dec(v_incrLoadFileName_x3f_3163_);
lean_dec(v_incrSaveFileName_x3f_3162_);
lean_dec_ref(v_errorOnKinds_3159_);
lean_dec(v_bcFileName_x3f_3157_);
lean_dec(v_cFileName_x3f_3156_);
lean_dec(v_ileanFileName_x3f_3155_);
lean_dec(v_oleanFileName_x3f_3154_);
lean_dec(v_setupFileName_x3f_3153_);
lean_dec(v_rootDir_x3f_3152_);
v___x_3343_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__11));
v___x_3344_ = l_String_Slice_toString(v___x_3340_);
lean_dec_ref(v___x_3340_);
v___x_3345_ = lean_string_append(v___x_3343_, v___x_3344_);
lean_dec_ref(v___x_3344_);
v___x_3346_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
v___x_3347_ = lean_string_append(v___x_3345_, v___x_3346_);
v___x_3348_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_3347_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3356_; 
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3356_ == 0)
{
lean_object* v_unused_3357_; 
v_unused_3357_ = lean_ctor_get(v___x_3348_, 0);
lean_dec(v_unused_3357_);
v___x_3350_ = v___x_3348_;
v_isShared_3351_ = v_isSharedCheck_3356_;
goto v_resetjp_3349_;
}
else
{
lean_dec(v___x_3348_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3356_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3352_; lean_object* v___x_3354_; 
v___x_3352_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3351_ == 0)
{
lean_ctor_set(v___x_3350_, 0, v___x_3352_);
v___x_3354_ = v___x_3350_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3352_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
else
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3365_; 
v_a_3358_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v___x_3348_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3348_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_a_3358_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
}
else
{
lean_object* v___x_3366_; 
lean_dec_ref(v___x_3340_);
v___x_3366_ = lean_string_utf8_extract_fast(v_str_3333_, v___x_3338_, v_endExclusive_3335_);
lean_dec(v_endExclusive_3335_);
lean_dec(v___x_3338_);
lean_dec_ref(v_str_3333_);
v___y_3300_ = v___y_3330_;
v___y_3301_ = v___y_3331_;
v___y_3302_ = v___y_3332_;
v___y_3303_ = v___y_3336_;
v_contents_3304_ = v___x_3366_;
goto v___jp_3299_;
}
}
v___jp_3367_:
{
if (lean_obj_tag(v___y_3371_) == 0)
{
lean_object* v_a_3372_; lean_object* v___x_3373_; 
v_a_3372_ = lean_ctor_get(v___y_3371_, 0);
lean_inc(v_a_3372_);
lean_dec_ref_known(v___y_3371_, 1);
v___x_3373_ = lean_decode_lossy_utf8(v_a_3372_);
lean_dec(v_a_3372_);
if (v_onlyDeps_3148_ == 0)
{
if (v_onlySrcDeps_3149_ == 0)
{
lean_object* v___x_3374_; 
lean_inc_ref(v___x_3373_);
v___x_3374_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v___x_3373_);
if (lean_obj_tag(v___x_3374_) == 1)
{
lean_object* v_val_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
lean_dec_ref(v___x_3373_);
v_val_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_val_3375_);
lean_dec_ref_known(v___x_3374_, 1);
v___x_3376_ = lean_unsigned_to_nat(0u);
v___x_3377_ = lean_box(0);
v___x_3378_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3375_, v___x_3376_, v___x_3377_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_str_3379_; lean_object* v_startInclusive_3380_; lean_object* v_endExclusive_3381_; lean_object* v___x_3382_; 
v_str_3379_ = lean_ctor_get(v_val_3375_, 0);
lean_inc_ref(v_str_3379_);
v_startInclusive_3380_ = lean_ctor_get(v_val_3375_, 1);
lean_inc(v_startInclusive_3380_);
v_endExclusive_3381_ = lean_ctor_get(v_val_3375_, 2);
lean_inc(v_endExclusive_3381_);
lean_dec(v_val_3375_);
v___x_3382_ = lean_nat_sub(v_endExclusive_3381_, v_startInclusive_3380_);
lean_inc_ref(v___y_3369_);
v___y_3330_ = v___y_3369_;
v___y_3331_ = v___y_3370_;
v___y_3332_ = v___y_3368_;
v_str_3333_ = v_str_3379_;
v_startInclusive_3334_ = v_startInclusive_3380_;
v_endExclusive_3335_ = v_endExclusive_3381_;
v___y_3336_ = v___y_3369_;
v___y_3337_ = v___x_3382_;
goto v___jp_3329_;
}
else
{
lean_object* v_val_3383_; lean_object* v_str_3384_; lean_object* v_startInclusive_3385_; lean_object* v_endExclusive_3386_; 
v_val_3383_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_val_3383_);
lean_dec_ref_known(v___x_3378_, 1);
v_str_3384_ = lean_ctor_get(v_val_3375_, 0);
lean_inc_ref(v_str_3384_);
v_startInclusive_3385_ = lean_ctor_get(v_val_3375_, 1);
lean_inc(v_startInclusive_3385_);
v_endExclusive_3386_ = lean_ctor_get(v_val_3375_, 2);
lean_inc(v_endExclusive_3386_);
lean_dec(v_val_3375_);
lean_inc_ref(v___y_3369_);
v___y_3330_ = v___y_3369_;
v___y_3331_ = v___y_3370_;
v___y_3332_ = v___y_3368_;
v_str_3333_ = v_str_3384_;
v_startInclusive_3334_ = v_startInclusive_3385_;
v_endExclusive_3335_ = v_endExclusive_3386_;
v___y_3336_ = v___y_3369_;
v___y_3337_ = v_val_3383_;
goto v___jp_3329_;
}
}
else
{
lean_dec(v___x_3374_);
lean_inc_ref(v___y_3369_);
v___y_3300_ = v___y_3369_;
v___y_3301_ = v___y_3370_;
v___y_3302_ = v___y_3368_;
v___y_3303_ = v___y_3369_;
v_contents_3304_ = v___x_3373_;
goto v___jp_3299_;
}
}
else
{
lean_object* v___x_3387_; lean_object* v___x_3388_; 
lean_dec(v___y_3370_);
lean_dec(v___y_3368_);
lean_dec_ref(v___x_3182_);
lean_dec(v_incrHeaderSaveFileName_x3f_3164_);
lean_dec(v_incrLoadFileName_x3f_3163_);
lean_dec(v_incrSaveFileName_x3f_3162_);
lean_dec_ref(v_errorOnKinds_3159_);
lean_dec(v_bcFileName_x3f_3157_);
lean_dec(v_cFileName_x3f_3156_);
lean_dec(v_ileanFileName_x3f_3155_);
lean_dec(v_oleanFileName_x3f_3154_);
lean_dec(v_setupFileName_x3f_3153_);
lean_dec(v_rootDir_x3f_3152_);
v___x_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3387_, 0, v___y_3369_);
v___x_3388_ = l_Lean_Elab_printImportSrcs(v___x_3373_, v___x_3387_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3396_; 
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3396_ == 0)
{
lean_object* v_unused_3397_; 
v_unused_3397_ = lean_ctor_get(v___x_3388_, 0);
lean_dec(v_unused_3397_);
v___x_3390_ = v___x_3388_;
v_isShared_3391_ = v_isSharedCheck_3396_;
goto v_resetjp_3389_;
}
else
{
lean_dec(v___x_3388_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3396_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3392_; lean_object* v___x_3394_; 
v___x_3392_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 0, v___x_3392_);
v___x_3394_ = v___x_3390_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3392_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
else
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3405_; 
v_a_3398_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3400_ = v___x_3388_;
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3388_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3403_; 
if (v_isShared_3401_ == 0)
{
v___x_3403_ = v___x_3400_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
}
}
else
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
lean_dec(v___y_3370_);
lean_dec(v___y_3368_);
lean_dec_ref(v___x_3182_);
lean_dec(v_incrHeaderSaveFileName_x3f_3164_);
lean_dec(v_incrLoadFileName_x3f_3163_);
lean_dec(v_incrSaveFileName_x3f_3162_);
lean_dec_ref(v_errorOnKinds_3159_);
lean_dec(v_bcFileName_x3f_3157_);
lean_dec(v_cFileName_x3f_3156_);
lean_dec(v_ileanFileName_x3f_3155_);
lean_dec(v_oleanFileName_x3f_3154_);
lean_dec(v_setupFileName_x3f_3153_);
lean_dec(v_rootDir_x3f_3152_);
v___x_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3406_, 0, v___y_3369_);
v___x_3407_ = l_Lean_Elab_printImports(v___x_3373_, v___x_3406_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3415_; 
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3415_ == 0)
{
lean_object* v_unused_3416_; 
v_unused_3416_ = lean_ctor_get(v___x_3407_, 0);
lean_dec(v_unused_3416_);
v___x_3409_ = v___x_3407_;
v_isShared_3410_ = v_isSharedCheck_3415_;
goto v_resetjp_3408_;
}
else
{
lean_dec(v___x_3407_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3415_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3411_; lean_object* v___x_3413_; 
v___x_3411_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v___x_3411_);
v___x_3413_ = v___x_3409_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v___x_3411_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
else
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
v_a_3417_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v___x_3407_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3407_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
}
else
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3432_; 
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec_ref(v___x_3182_);
lean_dec(v_incrHeaderSaveFileName_x3f_3164_);
lean_dec(v_incrLoadFileName_x3f_3163_);
lean_dec(v_incrSaveFileName_x3f_3162_);
lean_dec_ref(v_errorOnKinds_3159_);
lean_dec(v_bcFileName_x3f_3157_);
lean_dec(v_cFileName_x3f_3156_);
lean_dec(v_ileanFileName_x3f_3155_);
lean_dec(v_oleanFileName_x3f_3154_);
lean_dec(v_setupFileName_x3f_3153_);
lean_dec(v_rootDir_x3f_3152_);
v_a_3425_ = lean_ctor_get(v___y_3371_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___y_3371_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3427_ = v___y_3371_;
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v___y_3371_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3430_; 
if (v_isShared_3428_ == 0)
{
v___x_3430_ = v___x_3427_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_a_3425_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
}
v___jp_3433_:
{
if (v_useStdin_3147_ == 0)
{
lean_object* v___x_3437_; 
v___x_3437_ = l_IO_FS_readBinFile(v_fileName_3436_);
v___y_3368_ = v___y_3435_;
v___y_3369_ = v_fileName_3436_;
v___y_3370_ = v___y_3434_;
v___y_3371_ = v___x_3437_;
goto v___jp_3367_;
}
else
{
lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3438_ = lean_get_stdin();
v___x_3439_ = l_IO_FS_Stream_readBinToEnd(v___x_3438_);
v___y_3368_ = v___y_3435_;
v___y_3369_ = v_fileName_3436_;
v___y_3370_ = v___y_3434_;
v___y_3371_ = v___x_3439_;
goto v___jp_3367_;
}
}
v___jp_3440_:
{
if (lean_obj_tag(v___y_3442_) == 1)
{
lean_object* v_val_3443_; 
v_val_3443_ = lean_ctor_get(v___y_3442_, 0);
lean_inc(v_val_3443_);
v___y_3434_ = v___y_3441_;
v___y_3435_ = v___y_3442_;
v_fileName_3436_ = v_val_3443_;
goto v___jp_3433_;
}
else
{
if (v_useStdin_3147_ == 0)
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
lean_dec(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec_ref(v___x_3182_);
lean_dec(v_incrHeaderSaveFileName_x3f_3164_);
lean_dec(v_incrLoadFileName_x3f_3163_);
lean_dec(v_incrSaveFileName_x3f_3162_);
lean_dec_ref(v_errorOnKinds_3159_);
lean_dec(v_bcFileName_x3f_3157_);
lean_dec(v_cFileName_x3f_3156_);
lean_dec(v_ileanFileName_x3f_3155_);
lean_dec(v_oleanFileName_x3f_3154_);
lean_dec(v_setupFileName_x3f_3153_);
lean_dec(v_rootDir_x3f_3152_);
v___x_3444_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__4));
v___x_3445_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_3444_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v___x_3446_; 
lean_dec_ref_known(v___x_3445_, 1);
v___x_3446_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_3209_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3454_; 
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3454_ == 0)
{
lean_object* v_unused_3455_; 
v_unused_3455_ = lean_ctor_get(v___x_3446_, 0);
lean_dec(v_unused_3455_);
v___x_3448_ = v___x_3446_;
v_isShared_3449_ = v_isSharedCheck_3454_;
goto v_resetjp_3447_;
}
else
{
lean_dec(v___x_3446_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3454_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3450_; lean_object* v___x_3452_; 
v___x_3450_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 0, v___x_3450_);
v___x_3452_ = v___x_3448_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3450_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
else
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
v_a_3456_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3458_ = v___x_3446_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3446_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3456_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
v_a_3464_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3445_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3445_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
else
{
lean_object* v___x_3472_; 
v___x_3472_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__12));
v___y_3434_ = v___y_3441_;
v___y_3435_ = v___y_3442_;
v_fileName_3436_ = v___x_3472_;
goto v___jp_3433_;
}
}
}
v___jp_3473_:
{
uint8_t v___x_3477_; 
v___x_3477_ = l_List_isEmpty___redArg(v___y_3474_);
if (v___x_3477_ == 0)
{
lean_dec(v___y_3475_);
lean_dec(v___y_3474_);
lean_dec_ref(v___x_3182_);
lean_dec(v_incrHeaderSaveFileName_x3f_3164_);
lean_dec(v_incrLoadFileName_x3f_3163_);
lean_dec(v_incrSaveFileName_x3f_3162_);
lean_dec_ref(v_errorOnKinds_3159_);
lean_dec(v_bcFileName_x3f_3157_);
lean_dec(v_cFileName_x3f_3156_);
lean_dec(v_ileanFileName_x3f_3155_);
lean_dec(v_oleanFileName_x3f_3154_);
lean_dec(v_setupFileName_x3f_3153_);
lean_dec(v_rootDir_x3f_3152_);
goto v___jp_3210_;
}
else
{
if (v___y_3476_ == 0)
{
v___y_3441_ = v___y_3474_;
v___y_3442_ = v___y_3475_;
goto v___jp_3440_;
}
else
{
lean_dec(v___y_3475_);
lean_dec(v___y_3474_);
lean_dec_ref(v___x_3182_);
lean_dec(v_incrHeaderSaveFileName_x3f_3164_);
lean_dec(v_incrLoadFileName_x3f_3163_);
lean_dec(v_incrSaveFileName_x3f_3162_);
lean_dec_ref(v_errorOnKinds_3159_);
lean_dec(v_bcFileName_x3f_3157_);
lean_dec(v_cFileName_x3f_3156_);
lean_dec(v_ileanFileName_x3f_3155_);
lean_dec(v_oleanFileName_x3f_3154_);
lean_dec(v_setupFileName_x3f_3153_);
lean_dec(v_rootDir_x3f_3152_);
goto v___jp_3210_;
}
}
}
v___jp_3478_:
{
if (v_run_3161_ == 0)
{
v___y_3474_ = v_snd_3481_;
v___y_3475_ = v_fst_3480_;
v___y_3476_ = v___y_3479_;
goto v___jp_3473_;
}
else
{
if (v___y_3479_ == 0)
{
v___y_3441_ = v_snd_3481_;
v___y_3442_ = v_fst_3480_;
goto v___jp_3440_;
}
else
{
v___y_3474_ = v_snd_3481_;
v___y_3475_ = v_fst_3480_;
v___y_3476_ = v___y_3479_;
goto v___jp_3473_;
}
}
}
v___jp_3482_:
{
if (lean_obj_tag(v_args_3113_) == 0)
{
lean_object* v___x_3484_; 
v___x_3484_ = lean_box(0);
v___y_3479_ = v___y_3483_;
v_fst_3480_ = v___x_3484_;
v_snd_3481_ = v_args_3113_;
goto v___jp_3478_;
}
else
{
lean_object* v_head_3485_; lean_object* v_tail_3486_; lean_object* v___x_3487_; 
v_head_3485_ = lean_ctor_get(v_args_3113_, 0);
lean_inc(v_head_3485_);
v_tail_3486_ = lean_ctor_get(v_args_3113_, 1);
lean_inc(v_tail_3486_);
lean_dec_ref_known(v_args_3113_, 2);
v___x_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3487_, 0, v_head_3485_);
v___y_3479_ = v___y_3483_;
v_fst_3480_ = v___x_3487_;
v_snd_3481_ = v_tail_3486_;
goto v___jp_3478_;
}
}
v___jp_3488_:
{
switch(v_component_3146_)
{
case 0:
{
lean_dec_ref(v_forwardedArgs_3145_);
if (v_onlyDeps_3148_ == 0)
{
v___y_3483_ = v_printLibDir_3143_;
goto v___jp_3482_;
}
else
{
if (v_depsJson_3150_ == 0)
{
v___y_3483_ = v_depsJson_3150_;
goto v___jp_3482_;
}
else
{
lean_dec_ref(v___x_3182_);
lean_dec(v_incrHeaderSaveFileName_x3f_3164_);
lean_dec(v_incrLoadFileName_x3f_3163_);
lean_dec(v_incrSaveFileName_x3f_3162_);
lean_dec_ref(v_errorOnKinds_3159_);
lean_dec(v_bcFileName_x3f_3157_);
lean_dec(v_cFileName_x3f_3156_);
lean_dec(v_ileanFileName_x3f_3155_);
lean_dec(v_oleanFileName_x3f_3154_);
lean_dec(v_setupFileName_x3f_3153_);
lean_dec(v_rootDir_x3f_3152_);
if (v_useStdin_3147_ == 0)
{
lean_object* v___x_3489_; 
v___x_3489_ = lean_array_mk(v_args_3113_);
v_fns_3117_ = v___x_3489_;
goto v___jp_3116_;
}
else
{
lean_object* v___x_3490_; lean_object* v___x_3491_; 
lean_dec(v_args_3113_);
v___x_3490_ = lean_get_stdin();
v___x_3491_ = l_IO_FS_Stream_lines(v___x_3490_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3492_);
lean_dec_ref_known(v___x_3491_, 1);
v_fns_3117_ = v_a_3492_;
goto v___jp_3116_;
}
else
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
v_a_3493_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3495_ = v___x_3491_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3491_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_a_3493_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; 
lean_dec_ref(v___x_3182_);
lean_dec(v_incrHeaderSaveFileName_x3f_3164_);
lean_dec(v_incrLoadFileName_x3f_3163_);
lean_dec(v_incrSaveFileName_x3f_3162_);
lean_dec_ref(v_errorOnKinds_3159_);
lean_dec(v_bcFileName_x3f_3157_);
lean_dec(v_cFileName_x3f_3156_);
lean_dec(v_ileanFileName_x3f_3155_);
lean_dec(v_oleanFileName_x3f_3154_);
lean_dec(v_setupFileName_x3f_3153_);
lean_dec(v_rootDir_x3f_3152_);
lean_dec(v_args_3113_);
v___x_3501_ = lean_array_to_list(v_forwardedArgs_3145_);
v___x_3502_ = l_Lean_Server_Watchdog_watchdogMain(v___x_3501_);
return v___x_3502_;
}
default: 
{
lean_object* v___x_3503_; 
lean_dec(v_incrHeaderSaveFileName_x3f_3164_);
lean_dec(v_incrLoadFileName_x3f_3163_);
lean_dec(v_incrSaveFileName_x3f_3162_);
lean_dec_ref(v_errorOnKinds_3159_);
lean_dec(v_bcFileName_x3f_3157_);
lean_dec(v_cFileName_x3f_3156_);
lean_dec(v_ileanFileName_x3f_3155_);
lean_dec(v_oleanFileName_x3f_3154_);
lean_dec(v_setupFileName_x3f_3153_);
lean_dec(v_rootDir_x3f_3152_);
lean_dec_ref(v_forwardedArgs_3145_);
lean_dec(v_args_3113_);
v___x_3503_ = l_Lean_Server_FileWorker_workerMain(v___x_3182_);
return v___x_3503_;
}
}
}
v___jp_3504_:
{
lean_object* v___x_3505_; lean_object* v_timeout_3506_; lean_object* v___x_3507_; uint8_t v___x_3508_; 
v___x_3505_ = l___private_Lean_Shell_0__Lean_timeout;
v_timeout_3506_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3182_, v___x_3505_);
v___x_3507_ = lean_unsigned_to_nat(0u);
v___x_3508_ = lean_nat_dec_eq(v_timeout_3506_, v___x_3507_);
if (v___x_3508_ == 0)
{
size_t v___x_3509_; size_t v___x_3510_; size_t v___x_3511_; lean_object* v___x_3512_; 
v___x_3509_ = lean_usize_of_nat(v_timeout_3506_);
lean_dec(v_timeout_3506_);
v___x_3510_ = ((size_t)1000ULL);
v___x_3511_ = lean_usize_mul(v___x_3509_, v___x_3510_);
v___x_3512_ = lean_internal_set_max_heartbeat(v___x_3511_);
goto v___jp_3488_;
}
else
{
lean_dec(v_timeout_3506_);
goto v___jp_3488_;
}
}
}
else
{
lean_object* v___x_3522_; 
lean_dec_ref(v_opts_3114_);
lean_dec(v_args_3113_);
v___x_3522_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3523_; lean_object* v___x_3524_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_a_3523_);
lean_dec_ref_known(v___x_3522_, 1);
v___x_3524_ = l_Lean_getLibDir(v_a_3523_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v_a_3525_; lean_object* v___x_3526_; 
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_a_3525_);
lean_dec_ref_known(v___x_3524_, 1);
v___x_3526_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3525_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3534_; 
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3534_ == 0)
{
lean_object* v_unused_3535_; 
v_unused_3535_ = lean_ctor_get(v___x_3526_, 0);
lean_dec(v_unused_3535_);
v___x_3528_ = v___x_3526_;
v_isShared_3529_ = v_isSharedCheck_3534_;
goto v_resetjp_3527_;
}
else
{
lean_dec(v___x_3526_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3534_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3530_; lean_object* v___x_3532_; 
v___x_3530_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3530_);
v___x_3532_ = v___x_3528_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3530_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
else
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3543_; 
v_a_3536_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3538_ = v___x_3526_;
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3526_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3541_; 
if (v_isShared_3539_ == 0)
{
v___x_3541_ = v___x_3538_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
}
else
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3551_; 
v_a_3544_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3546_ = v___x_3524_;
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3524_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3549_; 
if (v_isShared_3547_ == 0)
{
v___x_3549_ = v___x_3546_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_a_3544_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
}
}
else
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3559_; 
v_a_3552_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3554_ = v___x_3522_;
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_3522_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3557_; 
if (v_isShared_3555_ == 0)
{
v___x_3557_ = v___x_3554_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_a_3552_);
v___x_3557_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
return v___x_3557_;
}
}
}
}
}
else
{
lean_object* v___x_3560_; 
lean_dec_ref(v_opts_3114_);
lean_dec(v_args_3113_);
v___x_3560_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_object* v_a_3561_; lean_object* v___x_3562_; 
v_a_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_a_3561_);
lean_dec_ref_known(v___x_3560_, 1);
v___x_3562_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3561_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3570_; 
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3570_ == 0)
{
lean_object* v_unused_3571_; 
v_unused_3571_ = lean_ctor_get(v___x_3562_, 0);
lean_dec(v_unused_3571_);
v___x_3564_ = v___x_3562_;
v_isShared_3565_ = v_isSharedCheck_3570_;
goto v_resetjp_3563_;
}
else
{
lean_dec(v___x_3562_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3570_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3566_; lean_object* v___x_3568_; 
v___x_3566_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 0, v___x_3566_);
v___x_3568_ = v___x_3564_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3566_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
else
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
v_a_3572_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3574_ = v___x_3562_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3562_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3577_; 
if (v_isShared_3575_ == 0)
{
v___x_3577_ = v___x_3574_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_a_3572_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
else
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
v_a_3580_ = lean_ctor_get(v___x_3560_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3582_ = v___x_3560_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v___x_3560_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
v___jp_3116_:
{
lean_object* v___x_3118_; 
v___x_3118_ = l_Lean_printImportsJson(v_fns_3117_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3126_; 
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3126_ == 0)
{
lean_object* v_unused_3127_; 
v_unused_3127_ = lean_ctor_get(v___x_3118_, 0);
lean_dec(v_unused_3127_);
v___x_3120_ = v___x_3118_;
v_isShared_3121_ = v_isSharedCheck_3126_;
goto v_resetjp_3119_;
}
else
{
lean_dec(v___x_3118_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3126_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3122_; lean_object* v___x_3124_; 
v___x_3122_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 0, v___x_3122_);
v___x_3124_ = v___x_3120_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3122_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
else
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
v_a_3128_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_3118_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3118_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3128_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
v___jp_3136_:
{
uint8_t v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = 0;
v___x_3138_ = lean_io_exit(v___x_3137_);
return v___x_3138_;
}
v___jp_3139_:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3140_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_3141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
return v___x_3141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object* v_args_3588_, lean_object* v_opts_3589_, lean_object* v_a_3590_){
_start:
{
lean_object* v_res_3591_; 
v_res_3591_ = lean_shell_main(v_args_3588_, v_opts_3589_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(lean_object* v_val_3592_, lean_object* v_inst_3593_, lean_object* v_R_3594_, lean_object* v_a_3595_, lean_object* v_b_3596_, lean_object* v_c_3597_){
_start:
{
lean_object* v___x_3598_; 
v___x_3598_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3592_, v_a_3595_, v_b_3596_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___boxed(lean_object* v_val_3599_, lean_object* v_inst_3600_, lean_object* v_R_3601_, lean_object* v_a_3602_, lean_object* v_b_3603_, lean_object* v_c_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(v_val_3599_, v_inst_3600_, v_R_3601_, v_a_3602_, v_b_3603_, v_c_3604_);
lean_dec(v_b_3603_);
lean_dec_ref(v_val_3599_);
return v_res_3605_;
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
