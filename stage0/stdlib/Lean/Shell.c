// Lean compiler output
// Module: Lean.Shell
// Imports: import Lean.Elab.Frontend import Lean.Elab.ParseImportsFast import Lean.Server.Watchdog import Lean.Server.FileWorker import Lean.Compiler.LCNF.EmitC import Init.System.Platform
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
extern lean_object* l_Lean_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
lean_object* l_IO_eprint___redArg(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stderr();
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecls();
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_toName(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_setOption(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
extern lean_object* l_Lean_version_specialDesc;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_versionStringCore;
lean_object* lean_string_append(lean_object*, lean_object*);
extern uint8_t l_Lean_version_isRelease;
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
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*);
extern lean_object* l_Lean_githash;
extern lean_object* l_System_Platform_target;
lean_object* lean_get_stdout();
lean_object* l_String_toName(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_load_dynlib(lean_object*);
lean_object* lean_load_plugin(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
extern lean_object* l_System_Platform_numBits;
lean_object* lean_nat_pow(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_internal_has_llvm_backend(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_io_exit(uint8_t);
lean_object* l_Lean_printImportsJson(lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_runFrontend(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedFileMap_default;
extern lean_object* l_Lean_NameSet_empty;
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
lean_object* l_Lean_getBuildDir();
lean_object* l_Lean_getLibDir(lean_object*);
lean_object* lean_decode_lossy_utf8(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_decodeLossyUTF8___boxed(lean_object*);
uint32_t lean_run_main(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_runMain___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_init_llvm();
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initLLVM___boxed(lean_object*);
lean_object* lean_emit_llvm(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_emitLLVM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_display_cumulative_profiling_times();
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayCumulativeProfilingTimes___boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "      --plugin=file      load and initialize Lean shared library for registering linters etc."};
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
static lean_once_cell_t l___private_Lean_Shell_0__Lean_displayHelp___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Shell_0__Lean_displayHelp___closed__12;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "      --debug=tag        enable assertions with the given tag"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__13 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__13_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Miscellaneous"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__14 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__14_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "  -h, --help             display this message"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__15 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__15_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "      --features         display features compiler provides (eg. LLVM support)"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__16 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__16_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "  -v, --version          display version information"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__17 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__17_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "  -V, --short-version    display short version number"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__18 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__18_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "  -g, --githash          display the git commit hash number used to build this binary"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__19 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__19_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 99, .m_capacity = 99, .m_length = 98, .m_data = "      --run <file>       call the 'main' definition in the given file with the remaining arguments"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__20 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__20_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "  -o, --o=oname          create olean file"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__21 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__21_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "  -i, --i=iname          create ilean file"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__22 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__22_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "  -c, --c=fname          name of the C output file"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__23 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__23_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "  -b, --bc=fname         name of the LLVM bitcode file"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__24 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__24_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "      --stdin            take input from stdin"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__25 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__25_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "  -R, --root=dir         set package root directory from which the module name\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__26 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__26_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "                         of the input file is calculated\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__27 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__27_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "                         (default: current working directory)\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__28 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__28_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "  -t, --trust=num        trust level (default: max) 0 means do not trust any macro,\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__29 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__29_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "                         and type check all imported modules\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__30 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__30_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "  -q, --quiet            do not print verbose messages"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__31 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__31_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "  -M, --memory=num       maximum amount of memory that should be used by Lean"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__32 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__32_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "                         (in megabytes)"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__33 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__33_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "  -T, --timeout=num      maximum number of memory allocations per task"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__34 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__34_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "                         this is a deterministic way of interrupting long running tasks"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__35 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__35_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_displayHelp___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Shell_0__Lean_displayHelp___closed__36;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "  -j, --threads=num      number of threads used to process lean files"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__37 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__37_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "  -s, --tstack=num       thread stack size in Kb"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__38 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__38_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "      --server           start lean in server mode"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__39 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__39_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "      --worker           start lean in server-worker mode"};
static const lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__40 = (const lean_object*)&l___private_Lean_Shell_0__Lean_displayHelp___closed__40_value;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHelp(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHelp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx___boxed(lean_object*);
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
lean_object* lean_internal_get_default_options(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultOptions___boxed(lean_object*);
uint32_t lean_internal_get_believer_trust_level(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getBelieverTrustLevel___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1;
LEAN_EXPORT uint32_t l___private_Lean_Shell_0__Lean_defaultTrustLevel;
uint32_t lean_internal_get_hardware_concurrency(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getHardwareCurrency___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0;
LEAN_EXPORT uint32_t l___private_Lean_Shell_0__Lean_defaultNumThreads;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0;
static const lean_array_object l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1 = (const lean_object*)&l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "E"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "u"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "l"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-l"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "p"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-p"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "B"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "D"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-D"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "t"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "error: argument value for '-t' is too large\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-t"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "error: expected numeric argument for option '-t'\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "T"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-T"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "error: expected numeric argument for option '-T'\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "M"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-M"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "error: expected numeric argument for option '-M'\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "R"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-R"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "i"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "o"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "error: argument value for '-s' is too large\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-s"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "error: expected numeric argument for option '-s'\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "c"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "j"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "error: argument value for '-j' is too large\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-j"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "error: expected numeric argument for option '-j'\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34_value;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
LEAN_EXPORT lean_object* lean_shell_options_process(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "#lang"};
static const lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0 = (const lean_object*)&l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Shell_0__Lean_shellMain___closed__0;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "LLVM code generation"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__1 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__1_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "C code generation"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__2 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__2_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__3;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__4;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__5 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__5_value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_shellMain___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__5_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__6 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__6_value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_shellMain___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__7 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__7_value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_shellMain___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__8 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__8_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__9;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__10;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__11;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__12;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__13;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__14;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__15;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__16;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "failed to create '"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__17 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__17_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_stdin"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__18 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__18_value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_shellMain___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__18_value),LEAN_SCALAR_PTR_LITERAL(37, 142, 62, 167, 41, 238, 22, 79)}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__19 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__19_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "lean4"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__20 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__20_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__21;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__22;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unknown language '"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__23 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__23_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Expected exactly one file name"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__24 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__24_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "<stdin>"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__25 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__25_value;
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
v_res_12_ = lean_run_main(v_env_8_, v_opts_9_, v_args_10_);
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
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayCumulativeProfilingTimes___boxed(lean_object* v_a_00___x40___internal___hyg_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lean_display_cumulative_profiling_times();
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_hasAddressSanitizer___boxed(lean_object* v_x_00___x40_Lean_Shell_2339721992____hygCtx___hyg_30_){
_start:
{
uint8_t v_res_31_; lean_object* v_r_32_; 
v_res_31_ = lean_internal_has_address_sanitizer(v_x_00___x40_Lean_Shell_2339721992____hygCtx___hyg_30_);
v_r_32_ = lean_box(v_res_31_);
return v_r_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_isMultiThread___boxed(lean_object* v_x_00___x40_Lean_Shell_3295292909____hygCtx___hyg_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = lean_internal_is_multi_thread(v_x_00___x40_Lean_Shell_3295292909____hygCtx___hyg_34_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_isDebug___boxed(lean_object* v_x_00___x40_Lean_Shell_97005966____hygCtx___hyg_38_){
_start:
{
uint8_t v_res_39_; lean_object* v_r_40_; 
v_res_39_ = lean_internal_is_debug(v_x_00___x40_Lean_Shell_97005966____hygCtx___hyg_38_);
v_r_40_ = lean_box(v_res_39_);
return v_r_40_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getBuildType___boxed(lean_object* v_x_00___x40_Lean_Shell_1721435280____hygCtx___hyg_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lean_internal_get_build_type(v_x_00___x40_Lean_Shell_1721435280____hygCtx___hyg_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultMaxMemory___boxed(lean_object* v_x_00___x40_Lean_Shell_1091001955____hygCtx___hyg_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = lean_internal_get_default_max_memory(v_x_00___x40_Lean_Shell_1091001955____hygCtx___hyg_45_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setMaxMemory___boxed(lean_object* v_max_49_, lean_object* v_a_00___x40___internal___hyg_50_){
_start:
{
size_t v_max_boxed_51_; lean_object* v_res_52_; 
v_max_boxed_51_ = lean_unbox_usize(v_max_49_);
lean_dec(v_max_49_);
v_res_52_ = lean_internal_set_max_memory(v_max_boxed_51_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultMaxHeartbeat___boxed(lean_object* v_x_00___x40_Lean_Shell_2736094960____hygCtx___hyg_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lean_internal_get_default_max_heartbeat(v_x_00___x40_Lean_Shell_2736094960____hygCtx___hyg_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setMaxHeartbeat___boxed(lean_object* v_max_58_, lean_object* v_a_00___x40___internal___hyg_59_){
_start:
{
size_t v_max_boxed_60_; lean_object* v_res_61_; 
v_max_boxed_60_ = lean_unbox_usize(v_max_58_);
lean_dec(v_max_58_);
v_res_61_ = lean_internal_set_max_heartbeat(v_max_boxed_60_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultVerbose___boxed(lean_object* v_x_00___x40_Lean_Shell_28281146____hygCtx___hyg_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = lean_internal_get_default_verbose(v_x_00___x40_Lean_Shell_28281146____hygCtx___hyg_63_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setExitOnPanic___boxed(lean_object* v_exit_68_, lean_object* v_a_00___x40___internal___hyg_69_){
_start:
{
uint8_t v_exit_boxed_70_; lean_object* v_res_71_; 
v_exit_boxed_70_ = lean_unbox(v_exit_68_);
v_res_71_ = lean_internal_set_exit_on_panic(v_exit_boxed_70_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setThreadStackSize___boxed(lean_object* v_sz_74_, lean_object* v_a_00___x40___internal___hyg_75_){
_start:
{
size_t v_sz_boxed_76_; lean_object* v_res_77_; 
v_sz_boxed_76_ = lean_unbox_usize(v_sz_74_);
lean_dec(v_sz_74_);
v_res_77_ = lean_internal_set_thread_stack_size(v_sz_boxed_76_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_enableDebug___boxed(lean_object* v_tag_80_, lean_object* v_a_00___x40___internal___hyg_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = lean_internal_enable_debug(v_tag_80_);
lean_dec_ref(v_tag_80_);
return v_res_82_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__1(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_84_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_85_ = l_Lean_version_specialDesc;
v___x_86_ = lean_string_dec_eq(v___x_85_, v___x_84_);
return v___x_86_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__3(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__2));
v___x_89_ = l_Lean_versionStringCore;
v___x_90_ = lean_string_append(v___x_89_, v___x_88_);
return v___x_90_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__4(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = l_Lean_version_specialDesc;
v___x_92_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shortVersionString___closed__3, &l___private_Lean_Shell_0__Lean_shortVersionString___closed__3_once, _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__3);
v___x_93_ = lean_string_append(v___x_92_, v___x_91_);
return v___x_93_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__6(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__5));
v___x_96_ = l_Lean_versionStringCore;
v___x_97_ = lean_string_append(v___x_96_, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString(void){
_start:
{
uint8_t v___x_98_; 
v___x_98_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_shortVersionString___closed__1, &l___private_Lean_Shell_0__Lean_shortVersionString___closed__1_once, _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__1);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; 
v___x_99_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shortVersionString___closed__4, &l___private_Lean_Shell_0__Lean_shortVersionString___closed__4_once, _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__4);
return v___x_99_;
}
else
{
uint8_t v___x_100_; 
v___x_100_ = l_Lean_version_isRelease;
if (v___x_100_ == 0)
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shortVersionString___closed__6, &l___private_Lean_Shell_0__Lean_shortVersionString___closed__6_once, _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__6);
return v___x_101_;
}
else
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_versionStringCore;
return v___x_102_;
}
}
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__2(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_box(0);
v___x_106_ = lean_internal_get_build_type(v___x_105_);
return v___x_106_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__4(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_108_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_109_ = l_Lean_githash;
v___x_110_ = lean_string_dec_eq(v___x_109_, v___x_108_);
return v___x_110_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__6(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_112_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_113_ = l_System_Platform_target;
v___x_114_ = lean_string_dec_eq(v___x_113_, v___x_112_);
return v___x_114_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__7(void){
_start:
{
lean_object* v___x_115_; lean_object* v_ver_116_; lean_object* v___x_117_; 
v___x_115_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__1));
v_ver_116_ = l___private_Lean_Shell_0__Lean_shortVersionString;
v___x_117_ = lean_string_append(v_ver_116_, v___x_115_);
return v___x_117_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__8(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v_ver_120_; 
v___x_118_ = l_System_Platform_target;
v___x_119_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__7, &l___private_Lean_Shell_0__Lean_versionHeader___closed__7_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__7);
v_ver_120_ = lean_string_append(v___x_119_, v___x_118_);
return v_ver_120_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader(void){
_start:
{
lean_object* v_ver_122_; lean_object* v_ver_132_; lean_object* v_ver_138_; uint8_t v___x_139_; 
v_ver_138_ = l___private_Lean_Shell_0__Lean_shortVersionString;
v___x_139_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__6, &l___private_Lean_Shell_0__Lean_versionHeader___closed__6_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__6);
if (v___x_139_ == 0)
{
lean_object* v_ver_140_; 
v_ver_140_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__8, &l___private_Lean_Shell_0__Lean_versionHeader___closed__8_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__8);
v_ver_132_ = v_ver_140_;
goto v___jp_131_;
}
else
{
v_ver_132_ = v_ver_138_;
goto v___jp_131_;
}
v___jp_121_:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_123_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__0));
v___x_124_ = lean_string_append(v___x_123_, v_ver_122_);
lean_dec_ref(v_ver_122_);
v___x_125_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__1));
v___x_126_ = lean_string_append(v___x_124_, v___x_125_);
v___x_127_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__2, &l___private_Lean_Shell_0__Lean_versionHeader___closed__2_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__2);
v___x_128_ = lean_string_append(v___x_126_, v___x_127_);
v___x_129_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__3));
v___x_130_ = lean_string_append(v___x_128_, v___x_129_);
return v___x_130_;
}
v___jp_131_:
{
lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_133_ = l_Lean_githash;
v___x_134_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__4, &l___private_Lean_Shell_0__Lean_versionHeader___closed__4_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__4);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v_ver_137_; 
v___x_135_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__5));
v___x_136_ = lean_string_append(v_ver_132_, v___x_135_);
v_ver_137_ = lean_string_append(v___x_136_, v___x_133_);
v_ver_122_ = v_ver_137_;
goto v___jp_121_;
}
else
{
v_ver_122_ = v_ver_132_;
goto v___jp_121_;
}
}
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_featuresString___closed__0(void){
_start:
{
lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_141_ = lean_box(0);
v___x_142_ = lean_internal_has_llvm_backend(v___x_141_);
return v___x_142_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_featuresString(void){
_start:
{
uint8_t v___x_145_; 
v___x_145_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_featuresString___closed__0, &l___private_Lean_Shell_0__Lean_featuresString___closed__0_once, _init_l___private_Lean_Shell_0__Lean_featuresString___closed__0);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; 
v___x_146_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_featuresString___closed__1));
return v___x_146_;
}
else
{
lean_object* v___x_147_; 
v___x_147_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_featuresString___closed__2));
return v___x_147_;
}
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__12(void){
_start:
{
lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_160_ = lean_box(0);
v___x_161_ = lean_internal_is_debug(v___x_160_);
return v___x_161_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__36(void){
_start:
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = lean_box(0);
v___x_186_ = lean_internal_is_multi_thread(v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHelp(uint8_t v_useStderr_191_){
_start:
{
lean_object* v___y_194_; lean_object* v___y_198_; lean_object* v_out_225_; 
if (v_useStderr_191_ == 0)
{
lean_object* v___x_281_; 
v___x_281_ = lean_get_stdout();
v_out_225_ = v___x_281_;
goto v___jp_224_;
}
else
{
lean_object* v___x_282_; 
v___x_282_ = lean_get_stderr();
v_out_225_ = v___x_282_;
goto v___jp_224_;
}
v___jp_193_:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__0));
v___x_196_ = l_IO_FS_Stream_putStrLn(v___y_194_, v___x_195_);
return v___x_196_;
}
v___jp_197_:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__1));
lean_inc_ref(v___y_198_);
v___x_200_ = l_IO_FS_Stream_putStrLn(v___y_198_, v___x_199_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec_ref(v___x_200_);
v___x_201_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__2));
lean_inc_ref(v___y_198_);
v___x_202_ = l_IO_FS_Stream_putStrLn(v___y_198_, v___x_201_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec_ref(v___x_202_);
v___x_203_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__3));
lean_inc_ref(v___y_198_);
v___x_204_ = l_IO_FS_Stream_putStrLn(v___y_198_, v___x_203_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v___x_205_; lean_object* v___x_206_; 
lean_dec_ref(v___x_204_);
v___x_205_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__4));
lean_inc_ref(v___y_198_);
v___x_206_ = l_IO_FS_Stream_putStrLn(v___y_198_, v___x_205_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec_ref(v___x_206_);
v___x_207_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__5));
lean_inc_ref(v___y_198_);
v___x_208_ = l_IO_FS_Stream_putStrLn(v___y_198_, v___x_207_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; 
lean_dec_ref(v___x_208_);
v___x_209_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__6));
lean_inc_ref(v___y_198_);
v___x_210_ = l_IO_FS_Stream_putStrLn(v___y_198_, v___x_209_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec_ref(v___x_210_);
v___x_211_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__7));
lean_inc_ref(v___y_198_);
v___x_212_ = l_IO_FS_Stream_putStrLn(v___y_198_, v___x_211_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v___x_213_; lean_object* v___x_214_; 
lean_dec_ref(v___x_212_);
v___x_213_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__8));
lean_inc_ref(v___y_198_);
v___x_214_ = l_IO_FS_Stream_putStrLn(v___y_198_, v___x_213_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; 
lean_dec_ref(v___x_214_);
v___x_215_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__9));
lean_inc_ref(v___y_198_);
v___x_216_ = l_IO_FS_Stream_putStrLn(v___y_198_, v___x_215_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v___x_217_; lean_object* v___x_218_; 
lean_dec_ref(v___x_216_);
v___x_217_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__10));
lean_inc_ref(v___y_198_);
v___x_218_ = l_IO_FS_Stream_putStrLn(v___y_198_, v___x_217_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec_ref(v___x_218_);
v___x_219_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__11));
lean_inc_ref(v___y_198_);
v___x_220_ = l_IO_FS_Stream_putStrLn(v___y_198_, v___x_219_);
if (lean_obj_tag(v___x_220_) == 0)
{
uint8_t v___x_221_; 
lean_dec_ref(v___x_220_);
v___x_221_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__12, &l___private_Lean_Shell_0__Lean_displayHelp___closed__12_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__12);
if (v___x_221_ == 0)
{
v___y_194_ = v___y_198_;
goto v___jp_193_;
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__13));
lean_inc_ref(v___y_198_);
v___x_223_ = l_IO_FS_Stream_putStrLn(v___y_198_, v___x_222_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_dec_ref(v___x_223_);
v___y_194_ = v___y_198_;
goto v___jp_193_;
}
else
{
lean_dec_ref(v___y_198_);
return v___x_223_;
}
}
}
else
{
lean_dec_ref(v___y_198_);
return v___x_220_;
}
}
else
{
lean_dec_ref(v___y_198_);
return v___x_218_;
}
}
else
{
lean_dec_ref(v___y_198_);
return v___x_216_;
}
}
else
{
lean_dec_ref(v___y_198_);
return v___x_214_;
}
}
else
{
lean_dec_ref(v___y_198_);
return v___x_212_;
}
}
else
{
lean_dec_ref(v___y_198_);
return v___x_210_;
}
}
else
{
lean_dec_ref(v___y_198_);
return v___x_208_;
}
}
else
{
lean_dec_ref(v___y_198_);
return v___x_206_;
}
}
else
{
lean_dec_ref(v___y_198_);
return v___x_204_;
}
}
else
{
lean_dec_ref(v___y_198_);
return v___x_202_;
}
}
else
{
lean_dec_ref(v___y_198_);
return v___x_200_;
}
}
v___jp_224_:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = l___private_Lean_Shell_0__Lean_versionHeader;
lean_inc_ref(v_out_225_);
v___x_227_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_226_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_dec_ref(v___x_227_);
v___x_228_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__14));
lean_inc_ref(v_out_225_);
v___x_229_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_228_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v___x_230_; lean_object* v___x_231_; 
lean_dec_ref(v___x_229_);
v___x_230_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__15));
lean_inc_ref(v_out_225_);
v___x_231_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_230_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec_ref(v___x_231_);
v___x_232_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__16));
lean_inc_ref(v_out_225_);
v___x_233_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_232_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v___x_234_; lean_object* v___x_235_; 
lean_dec_ref(v___x_233_);
v___x_234_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__17));
lean_inc_ref(v_out_225_);
v___x_235_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_234_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec_ref(v___x_235_);
v___x_236_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__18));
lean_inc_ref(v_out_225_);
v___x_237_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_236_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec_ref(v___x_237_);
v___x_238_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__19));
lean_inc_ref(v_out_225_);
v___x_239_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_238_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec_ref(v___x_239_);
v___x_240_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__20));
lean_inc_ref(v_out_225_);
v___x_241_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_240_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec_ref(v___x_241_);
v___x_242_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__21));
lean_inc_ref(v_out_225_);
v___x_243_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_242_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec_ref(v___x_243_);
v___x_244_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__22));
lean_inc_ref(v_out_225_);
v___x_245_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_244_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec_ref(v___x_245_);
v___x_246_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__23));
lean_inc_ref(v_out_225_);
v___x_247_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_246_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; 
lean_dec_ref(v___x_247_);
v___x_248_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__24));
lean_inc_ref(v_out_225_);
v___x_249_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_248_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v___x_250_; lean_object* v___x_251_; 
lean_dec_ref(v___x_249_);
v___x_250_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__25));
lean_inc_ref(v_out_225_);
v___x_251_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_250_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v___x_252_; lean_object* v___x_253_; 
lean_dec_ref(v___x_251_);
v___x_252_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__26));
lean_inc_ref(v_out_225_);
v___x_253_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_252_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec_ref(v___x_253_);
v___x_254_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__27));
lean_inc_ref(v_out_225_);
v___x_255_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_254_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; 
lean_dec_ref(v___x_255_);
v___x_256_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__28));
lean_inc_ref(v_out_225_);
v___x_257_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_256_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec_ref(v___x_257_);
v___x_258_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__29));
lean_inc_ref(v_out_225_);
v___x_259_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_258_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec_ref(v___x_259_);
v___x_260_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__30));
lean_inc_ref(v_out_225_);
v___x_261_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_260_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec_ref(v___x_261_);
v___x_262_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__31));
lean_inc_ref(v_out_225_);
v___x_263_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_262_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec_ref(v___x_263_);
v___x_264_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__32));
lean_inc_ref(v_out_225_);
v___x_265_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_264_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; 
lean_dec_ref(v___x_265_);
v___x_266_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__33));
lean_inc_ref(v_out_225_);
v___x_267_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_266_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec_ref(v___x_267_);
v___x_268_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__34));
lean_inc_ref(v_out_225_);
v___x_269_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_268_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; 
lean_dec_ref(v___x_269_);
v___x_270_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__35));
lean_inc_ref(v_out_225_);
v___x_271_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_270_);
if (lean_obj_tag(v___x_271_) == 0)
{
uint8_t v___x_272_; 
lean_dec_ref(v___x_271_);
v___x_272_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__36, &l___private_Lean_Shell_0__Lean_displayHelp___closed__36_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__36);
if (v___x_272_ == 0)
{
v___y_198_ = v_out_225_;
goto v___jp_197_;
}
else
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__37));
lean_inc_ref(v_out_225_);
v___x_274_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_273_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; 
lean_dec_ref(v___x_274_);
v___x_275_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__38));
lean_inc_ref(v_out_225_);
v___x_276_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_275_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; 
lean_dec_ref(v___x_276_);
v___x_277_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__39));
lean_inc_ref(v_out_225_);
v___x_278_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_277_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; 
lean_dec_ref(v___x_278_);
v___x_279_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__40));
lean_inc_ref(v_out_225_);
v___x_280_ = l_IO_FS_Stream_putStrLn(v_out_225_, v___x_279_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_dec_ref(v___x_280_);
v___y_198_ = v_out_225_;
goto v___jp_197_;
}
else
{
lean_dec_ref(v_out_225_);
return v___x_280_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_278_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_276_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_274_;
}
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_271_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_269_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_267_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_265_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_263_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_261_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_259_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_257_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_255_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_253_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_251_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_249_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_247_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_245_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_243_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_241_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_239_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_237_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_235_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_233_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_231_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_229_;
}
}
else
{
lean_dec_ref(v_out_225_);
return v___x_227_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHelp___boxed(lean_object* v_useStderr_283_, lean_object* v_a_284_){
_start:
{
uint8_t v_useStderr_boxed_285_; lean_object* v_res_286_; 
v_useStderr_boxed_285_ = lean_unbox(v_useStderr_283_);
v_res_286_ = l___private_Lean_Shell_0__Lean_displayHelp(v_useStderr_boxed_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(uint8_t v_x_287_){
_start:
{
switch(v_x_287_)
{
case 0:
{
lean_object* v___x_288_; 
v___x_288_ = lean_unsigned_to_nat(0u);
return v___x_288_;
}
case 1:
{
lean_object* v___x_289_; 
v___x_289_ = lean_unsigned_to_nat(1u);
return v___x_289_;
}
default: 
{
lean_object* v___x_290_; 
v___x_290_ = lean_unsigned_to_nat(2u);
return v___x_290_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx___boxed(lean_object* v_x_291_){
_start:
{
uint8_t v_x_boxed_292_; lean_object* v_res_293_; 
v_x_boxed_292_ = lean_unbox(v_x_291_);
v_res_293_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(v_x_boxed_292_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx(uint8_t v_x_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(v_x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx___boxed(lean_object* v_x_296_){
_start:
{
uint8_t v_x_4__boxed_297_; lean_object* v_res_298_; 
v_x_4__boxed_297_ = lean_unbox(v_x_296_);
v_res_298_ = l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx(v_x_4__boxed_297_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg(lean_object* v_k_299_){
_start:
{
lean_inc(v_k_299_);
return v_k_299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg___boxed(lean_object* v_k_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg(v_k_300_);
lean_dec(v_k_300_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim(lean_object* v_motive_302_, lean_object* v_ctorIdx_303_, uint8_t v_t_304_, lean_object* v_h_305_, lean_object* v_k_306_){
_start:
{
lean_inc(v_k_306_);
return v_k_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___boxed(lean_object* v_motive_307_, lean_object* v_ctorIdx_308_, lean_object* v_t_309_, lean_object* v_h_310_, lean_object* v_k_311_){
_start:
{
uint8_t v_t_boxed_312_; lean_object* v_res_313_; 
v_t_boxed_312_ = lean_unbox(v_t_309_);
v_res_313_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim(v_motive_307_, v_ctorIdx_308_, v_t_boxed_312_, v_h_310_, v_k_311_);
lean_dec(v_k_311_);
lean_dec(v_ctorIdx_308_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg(lean_object* v_frontend_314_){
_start:
{
lean_inc(v_frontend_314_);
return v_frontend_314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg___boxed(lean_object* v_frontend_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg(v_frontend_315_);
lean_dec(v_frontend_315_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim(lean_object* v_motive_317_, uint8_t v_t_318_, lean_object* v_h_319_, lean_object* v_frontend_320_){
_start:
{
lean_inc(v_frontend_320_);
return v_frontend_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___boxed(lean_object* v_motive_321_, lean_object* v_t_322_, lean_object* v_h_323_, lean_object* v_frontend_324_){
_start:
{
uint8_t v_t_boxed_325_; lean_object* v_res_326_; 
v_t_boxed_325_ = lean_unbox(v_t_322_);
v_res_326_ = l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim(v_motive_321_, v_t_boxed_325_, v_h_323_, v_frontend_324_);
lean_dec(v_frontend_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg(lean_object* v_watchdog_327_){
_start:
{
lean_inc(v_watchdog_327_);
return v_watchdog_327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg___boxed(lean_object* v_watchdog_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg(v_watchdog_328_);
lean_dec(v_watchdog_328_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim(lean_object* v_motive_330_, uint8_t v_t_331_, lean_object* v_h_332_, lean_object* v_watchdog_333_){
_start:
{
lean_inc(v_watchdog_333_);
return v_watchdog_333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___boxed(lean_object* v_motive_334_, lean_object* v_t_335_, lean_object* v_h_336_, lean_object* v_watchdog_337_){
_start:
{
uint8_t v_t_boxed_338_; lean_object* v_res_339_; 
v_t_boxed_338_ = lean_unbox(v_t_335_);
v_res_339_ = l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim(v_motive_334_, v_t_boxed_338_, v_h_336_, v_watchdog_337_);
lean_dec(v_watchdog_337_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg(lean_object* v_worker_340_){
_start:
{
lean_inc(v_worker_340_);
return v_worker_340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg___boxed(lean_object* v_worker_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg(v_worker_341_);
lean_dec(v_worker_341_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim(lean_object* v_motive_343_, uint8_t v_t_344_, lean_object* v_h_345_, lean_object* v_worker_346_){
_start:
{
lean_inc(v_worker_346_);
return v_worker_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___boxed(lean_object* v_motive_347_, lean_object* v_t_348_, lean_object* v_h_349_, lean_object* v_worker_350_){
_start:
{
uint8_t v_t_boxed_351_; lean_object* v_res_352_; 
v_t_boxed_351_ = lean_unbox(v_t_348_);
v_res_352_ = l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim(v_motive_347_, v_t_boxed_351_, v_h_349_, v_worker_350_);
lean_dec(v_worker_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(lean_object* v_name_353_, lean_object* v_decl_354_, lean_object* v_ref_355_){
_start:
{
lean_object* v_defValue_357_; lean_object* v_descr_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_384_; 
v_defValue_357_ = lean_ctor_get(v_decl_354_, 0);
v_descr_358_ = lean_ctor_get(v_decl_354_, 1);
v_isSharedCheck_384_ = !lean_is_exclusive(v_decl_354_);
if (v_isSharedCheck_384_ == 0)
{
v___x_360_ = v_decl_354_;
v_isShared_361_ = v_isSharedCheck_384_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_descr_358_);
lean_inc(v_defValue_357_);
lean_dec(v_decl_354_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_384_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
lean_inc(v_defValue_357_);
v___x_362_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_362_, 0, v_defValue_357_);
lean_inc(v_name_353_);
v___x_363_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_363_, 0, v_name_353_);
lean_ctor_set(v___x_363_, 1, v_ref_355_);
lean_ctor_set(v___x_363_, 2, v___x_362_);
lean_ctor_set(v___x_363_, 3, v_descr_358_);
lean_inc(v_name_353_);
v___x_364_ = lean_register_option(v_name_353_, v___x_363_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_374_; 
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_374_ == 0)
{
lean_object* v_unused_375_; 
v_unused_375_ = lean_ctor_get(v___x_364_, 0);
lean_dec(v_unused_375_);
v___x_366_ = v___x_364_;
v_isShared_367_ = v_isSharedCheck_374_;
goto v_resetjp_365_;
}
else
{
lean_dec(v___x_364_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_374_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v_defValue_357_);
lean_ctor_set(v___x_360_, 0, v_name_353_);
v___x_369_ = v___x_360_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_name_353_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_defValue_357_);
v___x_369_ = v_reuseFailAlloc_373_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_371_; 
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v___x_369_);
v___x_371_ = v___x_366_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_del_object(v___x_360_);
lean_dec(v_defValue_357_);
lean_dec(v_name_353_);
v_a_376_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_364_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_364_);
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
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0___boxed(lean_object* v_name_385_, lean_object* v_decl_386_, lean_object* v_ref_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v_name_385_, v_decl_386_, v_ref_387_);
return v_res_389_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_box(0);
v___x_394_ = lean_internal_get_default_max_memory(v___x_393_);
return v___x_394_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_395_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_396_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set(v___x_397_, 1, v___x_395_);
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
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_432_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_433_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
v___x_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
lean_ctor_set(v___x_434_, 1, v___x_432_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_439_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_));
v___x_440_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
v___x_441_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_));
v___x_442_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v___x_439_, v___x_440_, v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2____boxed(lean_object* v_a_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_();
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(lean_object* v_name_445_, lean_object* v_decl_446_, lean_object* v_ref_447_){
_start:
{
lean_object* v_defValue_449_; lean_object* v_descr_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_477_; 
v_defValue_449_ = lean_ctor_get(v_decl_446_, 0);
v_descr_450_ = lean_ctor_get(v_decl_446_, 1);
v_isSharedCheck_477_ = !lean_is_exclusive(v_decl_446_);
if (v_isSharedCheck_477_ == 0)
{
v___x_452_ = v_decl_446_;
v_isShared_453_ = v_isSharedCheck_477_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_descr_450_);
lean_inc(v_defValue_449_);
lean_dec(v_decl_446_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_477_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; uint8_t v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_454_ = lean_alloc_ctor(1, 0, 1);
v___x_455_ = lean_unbox(v_defValue_449_);
lean_ctor_set_uint8(v___x_454_, 0, v___x_455_);
lean_inc(v_name_445_);
v___x_456_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_456_, 0, v_name_445_);
lean_ctor_set(v___x_456_, 1, v_ref_447_);
lean_ctor_set(v___x_456_, 2, v___x_454_);
lean_ctor_set(v___x_456_, 3, v_descr_450_);
lean_inc(v_name_445_);
v___x_457_ = lean_register_option(v_name_445_, v___x_456_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_467_; 
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_467_ == 0)
{
lean_object* v_unused_468_; 
v_unused_468_ = lean_ctor_get(v___x_457_, 0);
lean_dec(v_unused_468_);
v___x_459_ = v___x_457_;
v_isShared_460_ = v_isSharedCheck_467_;
goto v_resetjp_458_;
}
else
{
lean_dec(v___x_457_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_467_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 1, v_defValue_449_);
lean_ctor_set(v___x_452_, 0, v_name_445_);
v___x_462_ = v___x_452_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_name_445_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_defValue_449_);
v___x_462_ = v_reuseFailAlloc_466_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_464_; 
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v___x_462_);
v___x_464_ = v___x_459_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_del_object(v___x_452_);
lean_dec(v_defValue_449_);
lean_dec(v_name_445_);
v_a_469_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_457_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_457_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0___boxed(lean_object* v_name_478_, lean_object* v_decl_479_, lean_object* v_ref_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(v_name_478_, v_decl_479_, v_ref_480_);
return v_res_482_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_486_ = lean_box(0);
v___x_487_ = lean_internal_get_default_verbose(v___x_486_);
return v___x_487_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_488_; uint8_t v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_488_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_489_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_);
v___x_490_ = lean_box(v___x_489_);
v___x_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
lean_ctor_set(v___x_491_, 1, v___x_488_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_496_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_));
v___x_497_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_);
v___x_498_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_));
v___x_499_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(v___x_496_, v___x_497_, v___x_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2____boxed(lean_object* v_a_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_();
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultOptions___boxed(lean_object* v_x_00___x40_Lean_Shell_2553953037____hygCtx___hyg_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = lean_internal_get_default_options(v_x_00___x40_Lean_Shell_2553953037____hygCtx___hyg_503_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getBelieverTrustLevel___boxed(lean_object* v_x_00___x40_Lean_Shell_1075205639____hygCtx___hyg_506_){
_start:
{
uint32_t v_res_507_; lean_object* v_r_508_; 
v_res_507_ = lean_internal_get_believer_trust_level(v_x_00___x40_Lean_Shell_1075205639____hygCtx___hyg_506_);
v_r_508_ = lean_box_uint32(v_res_507_);
return v_r_508_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0(void){
_start:
{
lean_object* v___x_509_; uint32_t v___x_510_; 
v___x_509_ = lean_box(0);
v___x_510_ = lean_internal_get_believer_trust_level(v___x_509_);
return v___x_510_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1(void){
_start:
{
uint32_t v___x_511_; uint32_t v___x_512_; uint32_t v___x_513_; 
v___x_511_ = 1;
v___x_512_ = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0, &l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0_once, _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0);
v___x_513_ = lean_uint32_add(v___x_512_, v___x_511_);
return v___x_513_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel(void){
_start:
{
uint32_t v___x_514_; 
v___x_514_ = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1, &l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1_once, _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getHardwareCurrency___boxed(lean_object* v_x_00___x40_Lean_Shell_1910423346____hygCtx___hyg_516_){
_start:
{
uint32_t v_res_517_; lean_object* v_r_518_; 
v_res_517_ = lean_internal_get_hardware_concurrency(v_x_00___x40_Lean_Shell_1910423346____hygCtx___hyg_516_);
v_r_518_ = lean_box_uint32(v_res_517_);
return v_r_518_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0(void){
_start:
{
lean_object* v___x_519_; uint32_t v___x_520_; 
v___x_519_ = lean_box(0);
v___x_520_ = lean_internal_get_hardware_concurrency(v___x_519_);
return v___x_520_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultNumThreads(void){
_start:
{
uint8_t v___x_521_; 
v___x_521_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__36, &l___private_Lean_Shell_0__Lean_displayHelp___closed__36_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__36);
if (v___x_521_ == 0)
{
uint32_t v___x_522_; 
v___x_522_ = 0;
return v___x_522_;
}
else
{
uint32_t v___x_523_; 
v___x_523_ = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0, &l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0_once, _init_l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0);
return v___x_523_;
}
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_box(0);
v___x_525_ = lean_internal_get_default_options(v___x_524_);
return v___x_525_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2(void){
_start:
{
lean_object* v___x_528_; uint32_t v___x_529_; uint32_t v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; uint8_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_528_ = lean_box(0);
v___x_529_ = l___private_Lean_Shell_0__Lean_defaultNumThreads;
v___x_530_ = l___private_Lean_Shell_0__Lean_defaultTrustLevel;
v___x_531_ = l_Lean_Options_empty;
v___x_532_ = 0;
v___x_533_ = 0;
v___x_534_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1));
v___x_535_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0, &l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0_once, _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0);
v___x_536_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v___x_536_, 0, v___x_535_);
lean_ctor_set(v___x_536_, 1, v___x_534_);
lean_ctor_set(v___x_536_, 2, v___x_531_);
lean_ctor_set(v___x_536_, 3, v___x_528_);
lean_ctor_set(v___x_536_, 4, v___x_528_);
lean_ctor_set(v___x_536_, 5, v___x_528_);
lean_ctor_set(v___x_536_, 6, v___x_528_);
lean_ctor_set(v___x_536_, 7, v___x_528_);
lean_ctor_set(v___x_536_, 8, v___x_528_);
lean_ctor_set(v___x_536_, 9, v___x_534_);
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*10 + 8, v___x_533_);
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*10 + 9, v___x_532_);
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*10 + 10, v___x_532_);
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*10 + 11, v___x_532_);
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*10 + 12, v___x_532_);
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*10 + 13, v___x_532_);
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*10 + 14, v___x_532_);
lean_ctor_set_uint32(v___x_536_, sizeof(void*)*10, v___x_530_);
lean_ctor_set_uint32(v___x_536_, sizeof(void*)*10 + 4, v___x_529_);
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*10 + 15, v___x_532_);
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*10 + 16, v___x_532_);
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*10 + 17, v___x_532_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* lean_shell_options_mk(lean_object* v_x_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2, &l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2_once, _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2);
return v___x_538_;
}
}
LEAN_EXPORT uint8_t lean_shell_options_get_run(lean_object* v_opts_539_){
_start:
{
uint8_t v_run_540_; 
v_run_540_ = lean_ctor_get_uint8(v_opts_539_, sizeof(void*)*10 + 17);
lean_dec_ref(v_opts_539_);
return v_run_540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getRun___boxed(lean_object* v_opts_541_){
_start:
{
uint8_t v_res_542_; lean_object* v_r_543_; 
v_res_542_ = lean_shell_options_get_run(v_opts_541_);
v_r_543_ = lean_box(v_res_542_);
return v_r_543_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(lean_object* v_opts_544_, lean_object* v_opt_545_){
_start:
{
lean_object* v_name_546_; lean_object* v_defValue_547_; lean_object* v_map_548_; lean_object* v___x_549_; 
v_name_546_ = lean_ctor_get(v_opt_545_, 0);
v_defValue_547_ = lean_ctor_get(v_opt_545_, 1);
v_map_548_ = lean_ctor_get(v_opts_544_, 0);
v___x_549_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_548_, v_name_546_);
if (lean_obj_tag(v___x_549_) == 0)
{
uint8_t v___x_550_; 
v___x_550_ = lean_unbox(v_defValue_547_);
return v___x_550_;
}
else
{
lean_object* v_val_551_; 
v_val_551_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_val_551_);
lean_dec_ref(v___x_549_);
if (lean_obj_tag(v_val_551_) == 1)
{
uint8_t v_v_552_; 
v_v_552_ = lean_ctor_get_uint8(v_val_551_, 0);
lean_dec_ref(v_val_551_);
return v_v_552_;
}
else
{
uint8_t v___x_553_; 
lean_dec(v_val_551_);
v___x_553_ = lean_unbox(v_defValue_547_);
return v___x_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0___boxed(lean_object* v_opts_554_, lean_object* v_opt_555_){
_start:
{
uint8_t v_res_556_; lean_object* v_r_557_; 
v_res_556_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v_opts_554_, v_opt_555_);
lean_dec_ref(v_opt_555_);
lean_dec_ref(v_opts_554_);
v_r_557_ = lean_box(v_res_556_);
return v_r_557_;
}
}
LEAN_EXPORT uint8_t lean_shell_options_get_profiler(lean_object* v_opts_558_){
_start:
{
lean_object* v_leanOpts_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v_leanOpts_559_ = lean_ctor_get(v_opts_558_, 0);
lean_inc_ref(v_leanOpts_559_);
lean_dec_ref(v_opts_558_);
v___x_560_ = l_Lean_profiler;
v___x_561_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v_leanOpts_559_, v___x_560_);
lean_dec_ref(v_leanOpts_559_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getProfiler___boxed(lean_object* v_opts_562_){
_start:
{
uint8_t v_res_563_; lean_object* v_r_564_; 
v_res_563_ = lean_shell_options_get_profiler(v_opts_562_);
v_r_564_ = lean_box(v_res_563_);
return v_r_564_;
}
}
LEAN_EXPORT uint32_t lean_shell_options_get_num_threads(lean_object* v_opts_565_){
_start:
{
uint32_t v_numThreads_566_; 
v_numThreads_566_ = lean_ctor_get_uint32(v_opts_565_, sizeof(void*)*10 + 4);
lean_dec_ref(v_opts_565_);
return v_numThreads_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getNumThreads___boxed(lean_object* v_opts_567_){
_start:
{
uint32_t v_res_568_; lean_object* v_r_569_; 
v_res_568_ = lean_shell_options_get_num_threads(v_opts_567_);
v_r_569_ = lean_box_uint32(v_res_568_);
return v_r_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_checkOptArg(lean_object* v_optName_572_, lean_object* v_optArg_x3f_573_){
_start:
{
if (lean_obj_tag(v_optArg_x3f_573_) == 1)
{
lean_object* v_val_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
v_val_575_ = lean_ctor_get(v_optArg_x3f_573_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v_optArg_x3f_573_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v_optArg_x3f_573_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_val_575_);
lean_dec(v_optArg_x3f_573_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
lean_ctor_set_tag(v___x_577_, 0);
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_val_575_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec(v_optArg_x3f_573_);
v___x_583_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__0));
v___x_584_ = lean_string_append(v___x_583_, v_optName_572_);
v___x_585_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__1));
v___x_586_ = lean_string_append(v___x_584_, v___x_585_);
v___x_587_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
v___x_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
return v___x_588_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_checkOptArg___boxed(lean_object* v_optName_589_, lean_object* v_optArg_x3f_590_, lean_object* v_a_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l___private_Lean_Shell_0__Lean_checkOptArg(v_optName_589_, v_optArg_x3f_590_);
lean_dec_ref(v_optName_589_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0(lean_object* v_o_596_, lean_object* v_k_597_, lean_object* v_v_598_){
_start:
{
lean_object* v_map_599_; uint8_t v_hasTrace_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_614_; 
v_map_599_ = lean_ctor_get(v_o_596_, 0);
v_hasTrace_600_ = lean_ctor_get_uint8(v_o_596_, sizeof(void*)*1);
v_isSharedCheck_614_ = !lean_is_exclusive(v_o_596_);
if (v_isSharedCheck_614_ == 0)
{
v___x_602_ = v_o_596_;
v_isShared_603_ = v_isSharedCheck_614_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_map_599_);
lean_dec(v_o_596_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_614_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v_v_598_);
lean_inc(v_k_597_);
v___x_605_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_597_, v___x_604_, v_map_599_);
if (v_hasTrace_600_ == 0)
{
lean_object* v___x_606_; uint8_t v___x_607_; lean_object* v___x_609_; 
v___x_606_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_607_ = l_Lean_Name_isPrefixOf(v___x_606_, v_k_597_);
lean_dec(v_k_597_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_605_);
v___x_609_ = v___x_602_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_605_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_ctor_set_uint8(v___x_609_, sizeof(void*)*1, v___x_607_);
return v___x_609_;
}
}
else
{
lean_object* v___x_612_; 
lean_dec(v_k_597_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_605_);
v___x_612_ = v___x_602_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_605_);
lean_ctor_set_uint8(v_reuseFailAlloc_613_, sizeof(void*)*1, v_hasTrace_600_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(lean_object* v___x_615_, lean_object* v_arg_616_, lean_object* v_a_617_, lean_object* v_b_618_){
_start:
{
lean_object* v_startInclusive_619_; lean_object* v_endExclusive_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v_startInclusive_619_ = lean_ctor_get(v___x_615_, 1);
v_endExclusive_620_ = lean_ctor_get(v___x_615_, 2);
v___x_621_ = lean_nat_sub(v_endExclusive_620_, v_startInclusive_619_);
v___x_622_ = lean_nat_dec_eq(v_a_617_, v___x_621_);
lean_dec(v___x_621_);
if (v___x_622_ == 0)
{
uint32_t v___x_623_; uint32_t v___x_624_; uint8_t v___x_625_; 
lean_dec(v_b_618_);
v___x_623_ = lean_string_utf8_get_fast(v_arg_616_, v_a_617_);
v___x_624_ = 61;
v___x_625_ = lean_uint32_dec_eq(v___x_623_, v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_box(0);
v___x_627_ = lean_string_utf8_next_fast(v_arg_616_, v_a_617_);
lean_dec(v_a_617_);
v_a_617_ = v___x_627_;
v_b_618_ = v___x_626_;
goto _start;
}
else
{
lean_object* v___x_629_; 
v___x_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_629_, 0, v_a_617_);
return v___x_629_;
}
}
else
{
lean_dec(v_a_617_);
return v_b_618_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg___boxed(lean_object* v___x_630_, lean_object* v_arg_631_, lean_object* v_a_632_, lean_object* v_b_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_630_, v_arg_631_, v_a_632_, v_b_633_);
lean_dec_ref(v_arg_631_);
lean_dec_ref(v___x_630_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_setConfigOption(lean_object* v_opts_638_, lean_object* v_arg_639_){
_start:
{
lean_object* v___y_642_; lean_object* v_searcher_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_searcher_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = lean_string_utf8_byte_size(v_arg_639_);
lean_inc_ref(v_arg_639_);
v___x_675_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_675_, 0, v_arg_639_);
lean_ctor_set(v___x_675_, 1, v_searcher_673_);
lean_ctor_set(v___x_675_, 2, v___x_674_);
v___x_676_ = lean_box(0);
v___x_677_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_675_, v_arg_639_, v_searcher_673_, v___x_676_);
lean_dec_ref(v___x_675_);
if (lean_obj_tag(v___x_677_) == 0)
{
v___y_642_ = v___x_674_;
goto v___jp_641_;
}
else
{
lean_object* v_val_678_; 
v_val_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_val_678_);
lean_dec_ref(v___x_677_);
v___y_642_ = v_val_678_;
goto v___jp_641_;
}
v___jp_641_:
{
lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_643_ = lean_string_utf8_byte_size(v_arg_639_);
v___x_644_ = lean_nat_dec_eq(v___y_642_, v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_662_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_662_ == 0)
{
v___x_648_ = v___x_645_;
v_isShared_649_ = v_isSharedCheck_662_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_645_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_662_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v_name_653_; lean_object* v_val_654_; lean_object* v___x_655_; 
v___x_650_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_642_);
lean_inc_ref(v_arg_639_);
v___x_651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_651_, 0, v_arg_639_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
lean_ctor_set(v___x_651_, 2, v___y_642_);
v___x_652_ = lean_string_utf8_next_fast(v_arg_639_, v___y_642_);
lean_dec(v___y_642_);
v_name_653_ = l_String_Slice_toName(v___x_651_);
lean_dec_ref(v___x_651_);
v_val_654_ = lean_string_utf8_extract(v_arg_639_, v___x_652_, v___x_643_);
lean_dec_ref(v_arg_639_);
v___x_655_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_646_, v_name_653_);
lean_dec(v_a_646_);
if (lean_obj_tag(v___x_655_) == 1)
{
lean_object* v_val_656_; lean_object* v___x_657_; 
lean_del_object(v___x_648_);
v_val_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_val_656_);
lean_dec_ref(v___x_655_);
v___x_657_ = l_Lean_Language_Lean_setOption(v_opts_638_, v_val_656_, v_name_653_, v_val_654_);
return v___x_657_;
}
else
{
lean_object* v___x_658_; lean_object* v___x_660_; 
lean_dec(v___x_655_);
v___x_658_ = l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0(v_opts_638_, v_name_653_, v_val_654_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v___x_658_);
v___x_660_ = v___x_648_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_658_);
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
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_dec(v___y_642_);
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_opts_638_);
v_a_663_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_645_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_645_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; 
lean_dec(v___y_642_);
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_opts_638_);
v___x_671_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_setConfigOption___closed__1));
v___x_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_setConfigOption___boxed(lean_object* v_opts_679_, lean_object* v_arg_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_opts_679_, v_arg_680_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(lean_object* v___x_683_, lean_object* v_arg_684_, lean_object* v_inst_685_, lean_object* v_R_686_, lean_object* v_a_687_, lean_object* v_b_688_, lean_object* v_c_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_683_, v_arg_684_, v_a_687_, v_b_688_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___boxed(lean_object* v___x_691_, lean_object* v_arg_692_, lean_object* v_inst_693_, lean_object* v_R_694_, lean_object* v_a_695_, lean_object* v_b_696_, lean_object* v_c_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(v___x_691_, v_arg_692_, v_inst_693_, v_R_694_, v_a_695_, v_b_696_, v_c_697_);
lean_dec_ref(v_arg_692_);
lean_dec_ref(v___x_691_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(lean_object* v_msg_700_){
_start:
{
lean_object* v___f_702_; lean_object* v___x_703_; 
v___f_702_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_703_ = l_IO_eprint___redArg(v___f_702_, v_msg_700_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_703_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_703_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
else
{
lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_719_; 
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_719_ == 0)
{
lean_object* v_unused_720_; 
v_unused_720_ = lean_ctor_get(v___x_703_, 0);
lean_dec(v_unused_720_);
v___x_713_ = v___x_703_;
v_isShared_714_ = v_isSharedCheck_719_;
goto v_resetjp_712_;
}
else
{
lean_dec(v___x_703_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_719_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_715_ = lean_box(0);
if (v_isShared_714_ == 0)
{
lean_ctor_set_tag(v___x_713_, 0);
lean_ctor_set(v___x_713_, 0, v___x_715_);
v___x_717_ = v___x_713_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___boxed(lean_object* v_msg_721_, lean_object* v_a_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(v_msg_721_);
return v_res_723_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_726_; lean_object* v___x_727_; 
v___x_726_ = 1;
v___x_727_ = lean_box_uint32(v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(lean_object* v_x_728_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = lean_apply_1(v_x_728_, lean_box(0));
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_751_; lean_object* v___f_752_; lean_object* v___x_753_; 
v_a_746_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_746_);
lean_dec_ref(v___x_737_);
v___x_751_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___f_752_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_753_ = l_IO_eprint___redArg(v___f_752_, v___x_751_);
lean_dec_ref(v___x_753_);
goto v___jp_747_;
v___jp_747_:
{
lean_object* v___x_748_; lean_object* v___f_749_; lean_object* v___x_750_; 
v___x_748_ = lean_io_error_to_string(v_a_746_);
v___f_749_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_750_ = l_IO_eprint___redArg(v___f_749_, v___x_748_);
lean_dec_ref(v___x_750_);
goto v___jp_733_;
}
}
v___jp_730_:
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
return v___x_732_;
}
v___jp_733_:
{
lean_object* v___x_734_; lean_object* v___f_735_; lean_object* v___x_736_; 
v___x_734_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___f_735_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_736_ = l_IO_eprint___redArg(v___f_735_, v___x_734_);
lean_dec_ref(v___x_736_);
goto v___jp_730_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed(lean_object* v_x_754_, lean_object* v_a_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(v_x_754_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(lean_object* v_00_u03b1_757_, lean_object* v_x_758_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = lean_apply_1(v_x_758_, lean_box(0));
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_767_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_767_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_781_; lean_object* v___f_782_; lean_object* v___x_783_; 
v_a_776_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_776_);
lean_dec_ref(v___x_767_);
v___x_781_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___f_782_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_783_ = l_IO_eprint___redArg(v___f_782_, v___x_781_);
lean_dec_ref(v___x_783_);
goto v___jp_777_;
v___jp_777_:
{
lean_object* v___x_778_; lean_object* v___f_779_; lean_object* v___x_780_; 
v___x_778_ = lean_io_error_to_string(v_a_776_);
v___f_779_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_780_ = l_IO_eprint___redArg(v___f_779_, v___x_778_);
lean_dec_ref(v___x_780_);
goto v___jp_763_;
}
}
v___jp_760_:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
return v___x_762_;
}
v___jp_763_:
{
lean_object* v___x_764_; lean_object* v___f_765_; lean_object* v___x_766_; 
v___x_764_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___f_765_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_766_ = l_IO_eprint___redArg(v___f_765_, v___x_764_);
lean_dec_ref(v___x_766_);
goto v___jp_760_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___boxed(lean_object* v_00_u03b1_784_, lean_object* v_x_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(v_00_u03b1_784_, v_x_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(lean_object* v_opt_790_){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___f_799_; lean_object* v___x_800_; 
v___x_795_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__0));
v___x_796_ = lean_string_append(v___x_795_, v_opt_790_);
v___x_797_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
v___x_798_ = lean_string_append(v___x_796_, v___x_797_);
v___f_799_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_800_ = l_IO_eprint___redArg(v___f_799_, v___x_798_);
lean_dec_ref(v___x_800_);
goto v___jp_792_;
v___jp_792_:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
return v___x_794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___boxed(lean_object* v_opt_801_, lean_object* v_a_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(v_opt_801_);
lean_dec_ref(v_opt_801_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(lean_object* v_opt_806_){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___f_815_; lean_object* v___x_816_; 
v___x_811_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__0));
v___x_812_ = lean_string_append(v___x_811_, v_opt_806_);
v___x_813_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__1));
v___x_814_ = lean_string_append(v___x_812_, v___x_813_);
v___f_815_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_816_ = l_IO_eprint___redArg(v___f_815_, v___x_814_);
lean_dec_ref(v___x_816_);
goto v___jp_808_;
v___jp_808_:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___boxed(lean_object* v_opt_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(v_opt_817_);
lean_dec_ref(v_opt_817_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(lean_object* v_s_820_){
_start:
{
lean_object* v___x_822_; lean_object* v_putStr_823_; lean_object* v___x_824_; 
v___x_822_ = lean_get_stderr();
v_putStr_823_ = lean_ctor_get(v___x_822_, 4);
lean_inc_ref(v_putStr_823_);
lean_dec_ref(v___x_822_);
v___x_824_ = lean_apply_2(v_putStr_823_, v_s_820_, lean_box(0));
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0___boxed(lean_object* v_s_825_, lean_object* v_a_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v_s_825_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(lean_object* v_s_828_){
_start:
{
lean_object* v___x_830_; lean_object* v_putStr_831_; lean_object* v___x_832_; 
v___x_830_ = lean_get_stdout();
v_putStr_831_ = lean_ctor_get(v___x_830_, 4);
lean_inc_ref(v_putStr_831_);
lean_dec_ref(v___x_830_);
v___x_832_ = lean_apply_2(v_putStr_831_, v_s_828_, lean_box(0));
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5___boxed(lean_object* v_s_833_, lean_object* v_a_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v_s_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(lean_object* v_s_836_){
_start:
{
uint32_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_838_ = 10;
v___x_839_ = lean_string_push(v_s_836_, v___x_838_);
v___x_840_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3___boxed(lean_object* v_s_841_, lean_object* v_a_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v_s_841_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(lean_object* v_o_844_, lean_object* v_k_845_, uint8_t v_v_846_){
_start:
{
lean_object* v_map_847_; uint8_t v_hasTrace_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_862_; 
v_map_847_ = lean_ctor_get(v_o_844_, 0);
v_hasTrace_848_ = lean_ctor_get_uint8(v_o_844_, sizeof(void*)*1);
v_isSharedCheck_862_ = !lean_is_exclusive(v_o_844_);
if (v_isSharedCheck_862_ == 0)
{
v___x_850_ = v_o_844_;
v_isShared_851_ = v_isSharedCheck_862_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_map_847_);
lean_dec(v_o_844_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_862_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_852_, 0, v_v_846_);
lean_inc(v_k_845_);
v___x_853_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_845_, v___x_852_, v_map_847_);
if (v_hasTrace_848_ == 0)
{
lean_object* v___x_854_; uint8_t v___x_855_; lean_object* v___x_857_; 
v___x_854_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_855_ = l_Lean_Name_isPrefixOf(v___x_854_, v_k_845_);
lean_dec(v_k_845_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_853_);
v___x_857_ = v___x_850_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_853_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_ctor_set_uint8(v___x_857_, sizeof(void*)*1, v___x_855_);
return v___x_857_;
}
}
else
{
lean_object* v___x_860_; 
lean_dec(v_k_845_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_853_);
v___x_860_ = v___x_850_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_853_);
lean_ctor_set_uint8(v_reuseFailAlloc_861_, sizeof(void*)*1, v_hasTrace_848_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1___boxed(lean_object* v_o_863_, lean_object* v_k_864_, lean_object* v_v_865_){
_start:
{
uint8_t v_v_boxed_866_; lean_object* v_res_867_; 
v_v_boxed_866_ = lean_unbox(v_v_865_);
v_res_867_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(v_o_863_, v_k_864_, v_v_boxed_866_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(lean_object* v_opts_868_, lean_object* v_opt_869_, uint8_t v_val_870_){
_start:
{
lean_object* v_name_871_; lean_object* v___x_872_; 
v_name_871_ = lean_ctor_get(v_opt_869_, 0);
lean_inc(v_name_871_);
lean_dec_ref(v_opt_869_);
v___x_872_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(v_opts_868_, v_name_871_, v_val_870_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1___boxed(lean_object* v_opts_873_, lean_object* v_opt_874_, lean_object* v_val_875_){
_start:
{
uint8_t v_val_boxed_876_; lean_object* v_res_877_; 
v_val_boxed_876_ = lean_unbox(v_val_875_);
v_res_877_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_opts_873_, v_opt_874_, v_val_boxed_876_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__3(lean_object* v_o_878_, lean_object* v_k_879_, lean_object* v_v_880_){
_start:
{
lean_object* v_map_881_; uint8_t v_hasTrace_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_896_; 
v_map_881_ = lean_ctor_get(v_o_878_, 0);
v_hasTrace_882_ = lean_ctor_get_uint8(v_o_878_, sizeof(void*)*1);
v_isSharedCheck_896_ = !lean_is_exclusive(v_o_878_);
if (v_isSharedCheck_896_ == 0)
{
v___x_884_ = v_o_878_;
v_isShared_885_ = v_isSharedCheck_896_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_map_881_);
lean_dec(v_o_878_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_896_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_886_, 0, v_v_880_);
lean_inc(v_k_879_);
v___x_887_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_879_, v___x_886_, v_map_881_);
if (v_hasTrace_882_ == 0)
{
lean_object* v___x_888_; uint8_t v___x_889_; lean_object* v___x_891_; 
v___x_888_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_889_ = l_Lean_Name_isPrefixOf(v___x_888_, v_k_879_);
lean_dec(v_k_879_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_887_);
v___x_891_ = v___x_884_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_887_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
lean_ctor_set_uint8(v___x_891_, sizeof(void*)*1, v___x_889_);
return v___x_891_;
}
}
else
{
lean_object* v___x_894_; 
lean_dec(v_k_879_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_887_);
v___x_894_ = v___x_884_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_887_);
lean_ctor_set_uint8(v_reuseFailAlloc_895_, sizeof(void*)*1, v_hasTrace_882_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(lean_object* v_opts_897_, lean_object* v_opt_898_, lean_object* v_val_899_){
_start:
{
lean_object* v_name_900_; lean_object* v___x_901_; 
v_name_900_ = lean_ctor_get(v_opt_898_, 0);
lean_inc(v_name_900_);
lean_dec_ref(v_opt_898_);
v___x_901_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__3(v_opts_897_, v_name_900_, v_val_899_);
return v___x_901_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25(void){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_927_ = l_System_Platform_numBits;
v___x_928_ = lean_unsigned_to_nat(2u);
v___x_929_ = lean_nat_pow(v___x_928_, v___x_927_);
return v___x_929_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1(void){
_start:
{
uint32_t v___x_939_; lean_object* v___x_940_; 
v___x_939_ = 0;
v___x_940_ = lean_box_uint32(v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* lean_shell_options_process(lean_object* v_opts_941_, uint32_t v_opt_942_, lean_object* v_optArg_x3f_943_){
_start:
{
lean_object* v___y_1045_; uint32_t v___x_1141_; uint8_t v___x_1142_; 
v___x_1141_ = 101;
v___x_1142_ = lean_uint32_dec_eq(v_opt_942_, v___x_1141_);
if (v___x_1142_ == 0)
{
uint32_t v___x_1143_; uint8_t v___x_1144_; 
v___x_1143_ = 106;
v___x_1144_ = lean_uint32_dec_eq(v_opt_942_, v___x_1143_);
if (v___x_1144_ == 0)
{
uint32_t v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = 118;
v___x_1146_ = lean_uint32_dec_eq(v_opt_942_, v___x_1145_);
if (v___x_1146_ == 0)
{
uint32_t v___x_1147_; uint8_t v___x_1148_; 
v___x_1147_ = 86;
v___x_1148_ = lean_uint32_dec_eq(v_opt_942_, v___x_1147_);
if (v___x_1148_ == 0)
{
uint32_t v___x_1149_; uint8_t v___x_1150_; 
v___x_1149_ = 103;
v___x_1150_ = lean_uint32_dec_eq(v_opt_942_, v___x_1149_);
if (v___x_1150_ == 0)
{
uint32_t v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = 104;
v___x_1152_ = lean_uint32_dec_eq(v_opt_942_, v___x_1151_);
if (v___x_1152_ == 0)
{
uint32_t v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = 102;
v___x_1154_ = lean_uint32_dec_eq(v_opt_942_, v___x_1153_);
if (v___x_1154_ == 0)
{
uint32_t v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = 99;
v___x_1156_ = lean_uint32_dec_eq(v_opt_942_, v___x_1155_);
if (v___x_1156_ == 0)
{
uint32_t v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = 98;
v___x_1158_ = lean_uint32_dec_eq(v_opt_942_, v___x_1157_);
if (v___x_1158_ == 0)
{
uint32_t v___x_1159_; uint8_t v___x_1160_; 
v___x_1159_ = 115;
v___x_1160_ = lean_uint32_dec_eq(v_opt_942_, v___x_1159_);
if (v___x_1160_ == 0)
{
uint32_t v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = 73;
v___x_1162_ = lean_uint32_dec_eq(v_opt_942_, v___x_1161_);
if (v___x_1162_ == 0)
{
uint32_t v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = 114;
v___x_1164_ = lean_uint32_dec_eq(v_opt_942_, v___x_1163_);
if (v___x_1164_ == 0)
{
uint32_t v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = 111;
v___x_1166_ = lean_uint32_dec_eq(v_opt_942_, v___x_1165_);
if (v___x_1166_ == 0)
{
uint32_t v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = 105;
v___x_1168_ = lean_uint32_dec_eq(v_opt_942_, v___x_1167_);
if (v___x_1168_ == 0)
{
uint32_t v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = 82;
v___x_1170_ = lean_uint32_dec_eq(v_opt_942_, v___x_1169_);
if (v___x_1170_ == 0)
{
uint32_t v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = 77;
v___x_1172_ = lean_uint32_dec_eq(v_opt_942_, v___x_1171_);
if (v___x_1172_ == 0)
{
uint32_t v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = 84;
v___x_1174_ = lean_uint32_dec_eq(v_opt_942_, v___x_1173_);
if (v___x_1174_ == 0)
{
uint32_t v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = 116;
v___x_1176_ = lean_uint32_dec_eq(v_opt_942_, v___x_1175_);
if (v___x_1176_ == 0)
{
uint32_t v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = 113;
v___x_1178_ = lean_uint32_dec_eq(v_opt_942_, v___x_1177_);
if (v___x_1178_ == 0)
{
uint32_t v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = 100;
v___x_1180_ = lean_uint32_dec_eq(v_opt_942_, v___x_1179_);
if (v___x_1180_ == 0)
{
uint32_t v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = 79;
v___x_1182_ = lean_uint32_dec_eq(v_opt_942_, v___x_1181_);
if (v___x_1182_ == 0)
{
uint32_t v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = 78;
v___x_1184_ = lean_uint32_dec_eq(v_opt_942_, v___x_1183_);
if (v___x_1184_ == 0)
{
uint32_t v___x_1185_; uint8_t v___x_1186_; 
v___x_1185_ = 74;
v___x_1186_ = lean_uint32_dec_eq(v_opt_942_, v___x_1185_);
if (v___x_1186_ == 0)
{
uint32_t v___x_1187_; uint8_t v___x_1188_; 
v___x_1187_ = 97;
v___x_1188_ = lean_uint32_dec_eq(v_opt_942_, v___x_1187_);
if (v___x_1188_ == 0)
{
uint32_t v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = 120;
v___x_1190_ = lean_uint32_dec_eq(v_opt_942_, v___x_1189_);
if (v___x_1190_ == 0)
{
uint32_t v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = 76;
v___x_1192_ = lean_uint32_dec_eq(v_opt_942_, v___x_1191_);
if (v___x_1192_ == 0)
{
uint32_t v___x_1193_; uint8_t v___x_1194_; 
v___x_1193_ = 68;
v___x_1194_ = lean_uint32_dec_eq(v_opt_942_, v___x_1193_);
if (v___x_1194_ == 0)
{
uint32_t v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = 83;
v___x_1196_ = lean_uint32_dec_eq(v_opt_942_, v___x_1195_);
if (v___x_1196_ == 0)
{
uint32_t v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = 87;
v___x_1198_ = lean_uint32_dec_eq(v_opt_942_, v___x_1197_);
if (v___x_1198_ == 0)
{
uint32_t v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = 80;
v___x_1200_ = lean_uint32_dec_eq(v_opt_942_, v___x_1199_);
if (v___x_1200_ == 0)
{
uint32_t v___x_1201_; uint8_t v___x_1202_; 
v___x_1201_ = 66;
v___x_1202_ = lean_uint32_dec_eq(v_opt_942_, v___x_1201_);
if (v___x_1202_ == 0)
{
uint32_t v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = 112;
v___x_1204_ = lean_uint32_dec_eq(v_opt_942_, v___x_1203_);
if (v___x_1204_ == 0)
{
uint32_t v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = 108;
v___x_1206_ = lean_uint32_dec_eq(v_opt_942_, v___x_1205_);
if (v___x_1206_ == 0)
{
uint32_t v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = 117;
v___x_1208_ = lean_uint32_dec_eq(v_opt_942_, v___x_1207_);
if (v___x_1208_ == 0)
{
uint32_t v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = 69;
v___x_1210_ = lean_uint32_dec_eq(v_opt_942_, v___x_1209_);
if (v___x_1210_ == 0)
{
lean_dec(v_optArg_x3f_943_);
lean_dec_ref(v_opts_941_);
goto v___jp_1063_;
}
else
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1));
v___x_1212_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1211_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1251_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1215_ = v___x_1212_;
v_isShared_1216_ = v_isSharedCheck_1251_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1212_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1251_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v_leanOpts_1217_; lean_object* v_forwardedArgs_1218_; uint8_t v_component_1219_; uint8_t v_printPrefix_1220_; uint8_t v_printLibDir_1221_; uint8_t v_useStdin_1222_; uint8_t v_onlyDeps_1223_; uint8_t v_onlySrcDeps_1224_; uint8_t v_depsJson_1225_; lean_object* v_opts_1226_; uint32_t v_trustLevel_1227_; uint32_t v_numThreads_1228_; lean_object* v_rootDir_x3f_1229_; lean_object* v_setupFileName_x3f_1230_; lean_object* v_oleanFileName_x3f_1231_; lean_object* v_ileanFileName_x3f_1232_; lean_object* v_cFileName_x3f_1233_; lean_object* v_bcFileName_x3f_1234_; uint8_t v_jsonOutput_1235_; lean_object* v_errorOnKinds_1236_; uint8_t v_printStats_1237_; uint8_t v_run_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1250_; 
v_leanOpts_1217_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1218_ = lean_ctor_get(v_opts_941_, 1);
v_component_1219_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_1220_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_1221_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_1222_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_1223_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1224_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_1225_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_1226_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1227_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_1228_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1229_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1230_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1231_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1232_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1233_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1234_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1235_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_1236_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1237_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_1238_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_1250_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1240_ = v_opts_941_;
v_isShared_1241_ = v_isSharedCheck_1250_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_errorOnKinds_1236_);
lean_inc(v_bcFileName_x3f_1234_);
lean_inc(v_cFileName_x3f_1233_);
lean_inc(v_ileanFileName_x3f_1232_);
lean_inc(v_oleanFileName_x3f_1231_);
lean_inc(v_setupFileName_x3f_1230_);
lean_inc(v_rootDir_x3f_1229_);
lean_inc(v_opts_1226_);
lean_inc(v_forwardedArgs_1218_);
lean_inc(v_leanOpts_1217_);
lean_dec(v_opts_941_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1250_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1245_; 
v___x_1242_ = l_String_toName(v_a_1213_);
v___x_1243_ = lean_array_push(v_errorOnKinds_1236_, v___x_1242_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 9, v___x_1243_);
v___x_1245_ = v___x_1240_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_leanOpts_1217_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_forwardedArgs_1218_);
lean_ctor_set(v_reuseFailAlloc_1249_, 2, v_opts_1226_);
lean_ctor_set(v_reuseFailAlloc_1249_, 3, v_rootDir_x3f_1229_);
lean_ctor_set(v_reuseFailAlloc_1249_, 4, v_setupFileName_x3f_1230_);
lean_ctor_set(v_reuseFailAlloc_1249_, 5, v_oleanFileName_x3f_1231_);
lean_ctor_set(v_reuseFailAlloc_1249_, 6, v_ileanFileName_x3f_1232_);
lean_ctor_set(v_reuseFailAlloc_1249_, 7, v_cFileName_x3f_1233_);
lean_ctor_set(v_reuseFailAlloc_1249_, 8, v_bcFileName_x3f_1234_);
lean_ctor_set(v_reuseFailAlloc_1249_, 9, v___x_1243_);
lean_ctor_set_uint8(v_reuseFailAlloc_1249_, sizeof(void*)*10 + 8, v_component_1219_);
lean_ctor_set_uint8(v_reuseFailAlloc_1249_, sizeof(void*)*10 + 9, v_printPrefix_1220_);
lean_ctor_set_uint8(v_reuseFailAlloc_1249_, sizeof(void*)*10 + 10, v_printLibDir_1221_);
lean_ctor_set_uint8(v_reuseFailAlloc_1249_, sizeof(void*)*10 + 11, v_useStdin_1222_);
lean_ctor_set_uint8(v_reuseFailAlloc_1249_, sizeof(void*)*10 + 12, v_onlyDeps_1223_);
lean_ctor_set_uint8(v_reuseFailAlloc_1249_, sizeof(void*)*10 + 13, v_onlySrcDeps_1224_);
lean_ctor_set_uint8(v_reuseFailAlloc_1249_, sizeof(void*)*10 + 14, v_depsJson_1225_);
lean_ctor_set_uint32(v_reuseFailAlloc_1249_, sizeof(void*)*10, v_trustLevel_1227_);
lean_ctor_set_uint32(v_reuseFailAlloc_1249_, sizeof(void*)*10 + 4, v_numThreads_1228_);
lean_ctor_set_uint8(v_reuseFailAlloc_1249_, sizeof(void*)*10 + 15, v_jsonOutput_1235_);
lean_ctor_set_uint8(v_reuseFailAlloc_1249_, sizeof(void*)*10 + 16, v_printStats_1237_);
lean_ctor_set_uint8(v_reuseFailAlloc_1249_, sizeof(void*)*10 + 17, v_run_1238_);
v___x_1245_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
lean_object* v___x_1247_; 
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1245_);
v___x_1247_ = v___x_1215_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_dec_ref(v_opts_941_);
v_a_1252_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1252_);
lean_dec_ref(v___x_1212_);
v___x_1256_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1257_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1256_);
lean_dec_ref(v___x_1257_);
goto v___jp_1253_;
v___jp_1253_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = lean_io_error_to_string(v_a_1252_);
v___x_1255_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1254_);
lean_dec_ref(v___x_1255_);
goto v___jp_1069_;
}
}
}
}
else
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2));
v___x_1259_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1258_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1297_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1262_ = v___x_1259_;
v_isShared_1263_ = v_isSharedCheck_1297_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1259_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1297_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v_leanOpts_1264_; lean_object* v_forwardedArgs_1265_; uint8_t v_component_1266_; uint8_t v_printPrefix_1267_; uint8_t v_printLibDir_1268_; uint8_t v_useStdin_1269_; uint8_t v_onlyDeps_1270_; uint8_t v_onlySrcDeps_1271_; uint8_t v_depsJson_1272_; lean_object* v_opts_1273_; uint32_t v_trustLevel_1274_; uint32_t v_numThreads_1275_; lean_object* v_rootDir_x3f_1276_; lean_object* v_oleanFileName_x3f_1277_; lean_object* v_ileanFileName_x3f_1278_; lean_object* v_cFileName_x3f_1279_; lean_object* v_bcFileName_x3f_1280_; uint8_t v_jsonOutput_1281_; lean_object* v_errorOnKinds_1282_; uint8_t v_printStats_1283_; uint8_t v_run_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1295_; 
v_leanOpts_1264_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1265_ = lean_ctor_get(v_opts_941_, 1);
v_component_1266_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_1267_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_1268_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_1269_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_1270_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1271_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_1272_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_1273_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1274_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_1275_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1276_ = lean_ctor_get(v_opts_941_, 3);
v_oleanFileName_x3f_1277_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1278_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1279_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1280_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1281_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_1282_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1283_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_1284_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1295_ == 0)
{
lean_object* v_unused_1296_; 
v_unused_1296_ = lean_ctor_get(v_opts_941_, 4);
lean_dec(v_unused_1296_);
v___x_1286_ = v_opts_941_;
v_isShared_1287_ = v_isSharedCheck_1295_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_errorOnKinds_1282_);
lean_inc(v_bcFileName_x3f_1280_);
lean_inc(v_cFileName_x3f_1279_);
lean_inc(v_ileanFileName_x3f_1278_);
lean_inc(v_oleanFileName_x3f_1277_);
lean_inc(v_rootDir_x3f_1276_);
lean_inc(v_opts_1273_);
lean_inc(v_forwardedArgs_1265_);
lean_inc(v_leanOpts_1264_);
lean_dec(v_opts_941_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1295_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1288_, 0, v_a_1260_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 4, v___x_1288_);
v___x_1290_ = v___x_1286_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_leanOpts_1264_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_forwardedArgs_1265_);
lean_ctor_set(v_reuseFailAlloc_1294_, 2, v_opts_1273_);
lean_ctor_set(v_reuseFailAlloc_1294_, 3, v_rootDir_x3f_1276_);
lean_ctor_set(v_reuseFailAlloc_1294_, 4, v___x_1288_);
lean_ctor_set(v_reuseFailAlloc_1294_, 5, v_oleanFileName_x3f_1277_);
lean_ctor_set(v_reuseFailAlloc_1294_, 6, v_ileanFileName_x3f_1278_);
lean_ctor_set(v_reuseFailAlloc_1294_, 7, v_cFileName_x3f_1279_);
lean_ctor_set(v_reuseFailAlloc_1294_, 8, v_bcFileName_x3f_1280_);
lean_ctor_set(v_reuseFailAlloc_1294_, 9, v_errorOnKinds_1282_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, sizeof(void*)*10 + 8, v_component_1266_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, sizeof(void*)*10 + 9, v_printPrefix_1267_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, sizeof(void*)*10 + 10, v_printLibDir_1268_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, sizeof(void*)*10 + 11, v_useStdin_1269_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, sizeof(void*)*10 + 12, v_onlyDeps_1270_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, sizeof(void*)*10 + 13, v_onlySrcDeps_1271_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, sizeof(void*)*10 + 14, v_depsJson_1272_);
lean_ctor_set_uint32(v_reuseFailAlloc_1294_, sizeof(void*)*10, v_trustLevel_1274_);
lean_ctor_set_uint32(v_reuseFailAlloc_1294_, sizeof(void*)*10 + 4, v_numThreads_1275_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, sizeof(void*)*10 + 15, v_jsonOutput_1281_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, sizeof(void*)*10 + 16, v_printStats_1283_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, sizeof(void*)*10 + 17, v_run_1284_);
v___x_1290_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
lean_object* v___x_1292_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___x_1290_);
v___x_1292_ = v___x_1262_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1290_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
lean_dec_ref(v_opts_941_);
v_a_1298_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_a_1298_);
lean_dec_ref(v___x_1259_);
v___x_1302_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1303_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1302_);
lean_dec_ref(v___x_1303_);
goto v___jp_1299_;
v___jp_1299_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = lean_io_error_to_string(v_a_1298_);
v___x_1301_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1300_);
lean_dec_ref(v___x_1301_);
goto v___jp_1035_;
}
}
}
}
else
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3));
v___x_1305_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1304_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1307_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1306_);
lean_dec_ref(v___x_1305_);
lean_inc(v_a_1306_);
v___x_1307_ = lean_load_dynlib(v_a_1306_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1346_; 
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; 
v_unused_1347_ = lean_ctor_get(v___x_1307_, 0);
lean_dec(v_unused_1347_);
v___x_1309_ = v___x_1307_;
v_isShared_1310_ = v_isSharedCheck_1346_;
goto v_resetjp_1308_;
}
else
{
lean_dec(v___x_1307_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1346_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v_leanOpts_1311_; lean_object* v_forwardedArgs_1312_; uint8_t v_component_1313_; uint8_t v_printPrefix_1314_; uint8_t v_printLibDir_1315_; uint8_t v_useStdin_1316_; uint8_t v_onlyDeps_1317_; uint8_t v_onlySrcDeps_1318_; uint8_t v_depsJson_1319_; lean_object* v_opts_1320_; uint32_t v_trustLevel_1321_; uint32_t v_numThreads_1322_; lean_object* v_rootDir_x3f_1323_; lean_object* v_setupFileName_x3f_1324_; lean_object* v_oleanFileName_x3f_1325_; lean_object* v_ileanFileName_x3f_1326_; lean_object* v_cFileName_x3f_1327_; lean_object* v_bcFileName_x3f_1328_; uint8_t v_jsonOutput_1329_; lean_object* v_errorOnKinds_1330_; uint8_t v_printStats_1331_; uint8_t v_run_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1345_; 
v_leanOpts_1311_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1312_ = lean_ctor_get(v_opts_941_, 1);
v_component_1313_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_1314_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_1315_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_1316_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_1317_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1318_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_1319_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_1320_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1321_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_1322_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1323_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1324_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1325_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1326_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1327_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1328_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1329_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_1330_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1331_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_1332_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1334_ = v_opts_941_;
v_isShared_1335_ = v_isSharedCheck_1345_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_errorOnKinds_1330_);
lean_inc(v_bcFileName_x3f_1328_);
lean_inc(v_cFileName_x3f_1327_);
lean_inc(v_ileanFileName_x3f_1326_);
lean_inc(v_oleanFileName_x3f_1325_);
lean_inc(v_setupFileName_x3f_1324_);
lean_inc(v_rootDir_x3f_1323_);
lean_inc(v_opts_1320_);
lean_inc(v_forwardedArgs_1312_);
lean_inc(v_leanOpts_1311_);
lean_dec(v_opts_941_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1345_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1336_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4));
v___x_1337_ = lean_string_append(v___x_1336_, v_a_1306_);
lean_dec(v_a_1306_);
v___x_1338_ = lean_array_push(v_forwardedArgs_1312_, v___x_1337_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 1, v___x_1338_);
v___x_1340_ = v___x_1334_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_leanOpts_1311_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v___x_1338_);
lean_ctor_set(v_reuseFailAlloc_1344_, 2, v_opts_1320_);
lean_ctor_set(v_reuseFailAlloc_1344_, 3, v_rootDir_x3f_1323_);
lean_ctor_set(v_reuseFailAlloc_1344_, 4, v_setupFileName_x3f_1324_);
lean_ctor_set(v_reuseFailAlloc_1344_, 5, v_oleanFileName_x3f_1325_);
lean_ctor_set(v_reuseFailAlloc_1344_, 6, v_ileanFileName_x3f_1326_);
lean_ctor_set(v_reuseFailAlloc_1344_, 7, v_cFileName_x3f_1327_);
lean_ctor_set(v_reuseFailAlloc_1344_, 8, v_bcFileName_x3f_1328_);
lean_ctor_set(v_reuseFailAlloc_1344_, 9, v_errorOnKinds_1330_);
lean_ctor_set_uint8(v_reuseFailAlloc_1344_, sizeof(void*)*10 + 8, v_component_1313_);
lean_ctor_set_uint8(v_reuseFailAlloc_1344_, sizeof(void*)*10 + 9, v_printPrefix_1314_);
lean_ctor_set_uint8(v_reuseFailAlloc_1344_, sizeof(void*)*10 + 10, v_printLibDir_1315_);
lean_ctor_set_uint8(v_reuseFailAlloc_1344_, sizeof(void*)*10 + 11, v_useStdin_1316_);
lean_ctor_set_uint8(v_reuseFailAlloc_1344_, sizeof(void*)*10 + 12, v_onlyDeps_1317_);
lean_ctor_set_uint8(v_reuseFailAlloc_1344_, sizeof(void*)*10 + 13, v_onlySrcDeps_1318_);
lean_ctor_set_uint8(v_reuseFailAlloc_1344_, sizeof(void*)*10 + 14, v_depsJson_1319_);
lean_ctor_set_uint32(v_reuseFailAlloc_1344_, sizeof(void*)*10, v_trustLevel_1321_);
lean_ctor_set_uint32(v_reuseFailAlloc_1344_, sizeof(void*)*10 + 4, v_numThreads_1322_);
lean_ctor_set_uint8(v_reuseFailAlloc_1344_, sizeof(void*)*10 + 15, v_jsonOutput_1329_);
lean_ctor_set_uint8(v_reuseFailAlloc_1344_, sizeof(void*)*10 + 16, v_printStats_1331_);
lean_ctor_set_uint8(v_reuseFailAlloc_1344_, sizeof(void*)*10 + 17, v_run_1332_);
v___x_1340_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1342_; 
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v___x_1340_);
v___x_1342_ = v___x_1309_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
lean_dec(v_a_1306_);
lean_dec_ref(v_opts_941_);
v_a_1348_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1348_);
lean_dec_ref(v___x_1307_);
v___x_1352_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1353_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1352_);
lean_dec_ref(v___x_1353_);
goto v___jp_1349_;
v___jp_1349_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1350_ = lean_io_error_to_string(v_a_1348_);
v___x_1351_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1350_);
lean_dec_ref(v___x_1351_);
goto v___jp_1075_;
}
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
lean_dec_ref(v_opts_941_);
v_a_1354_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1354_);
lean_dec_ref(v___x_1305_);
v___x_1358_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1359_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1358_);
lean_dec_ref(v___x_1359_);
goto v___jp_1355_;
v___jp_1355_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_io_error_to_string(v_a_1354_);
v___x_1357_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1356_);
lean_dec_ref(v___x_1357_);
goto v___jp_1029_;
}
}
}
}
else
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5));
v___x_1361_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1360_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1363_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1362_);
lean_dec_ref(v___x_1361_);
lean_inc(v_a_1362_);
v___x_1363_ = lean_load_plugin(v_a_1362_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1402_; 
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1402_ == 0)
{
lean_object* v_unused_1403_; 
v_unused_1403_ = lean_ctor_get(v___x_1363_, 0);
lean_dec(v_unused_1403_);
v___x_1365_ = v___x_1363_;
v_isShared_1366_ = v_isSharedCheck_1402_;
goto v_resetjp_1364_;
}
else
{
lean_dec(v___x_1363_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1402_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v_leanOpts_1367_; lean_object* v_forwardedArgs_1368_; uint8_t v_component_1369_; uint8_t v_printPrefix_1370_; uint8_t v_printLibDir_1371_; uint8_t v_useStdin_1372_; uint8_t v_onlyDeps_1373_; uint8_t v_onlySrcDeps_1374_; uint8_t v_depsJson_1375_; lean_object* v_opts_1376_; uint32_t v_trustLevel_1377_; uint32_t v_numThreads_1378_; lean_object* v_rootDir_x3f_1379_; lean_object* v_setupFileName_x3f_1380_; lean_object* v_oleanFileName_x3f_1381_; lean_object* v_ileanFileName_x3f_1382_; lean_object* v_cFileName_x3f_1383_; lean_object* v_bcFileName_x3f_1384_; uint8_t v_jsonOutput_1385_; lean_object* v_errorOnKinds_1386_; uint8_t v_printStats_1387_; uint8_t v_run_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1401_; 
v_leanOpts_1367_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1368_ = lean_ctor_get(v_opts_941_, 1);
v_component_1369_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_1370_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_1371_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_1372_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_1373_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1374_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_1375_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_1376_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1377_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_1378_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1379_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1380_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1381_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1382_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1383_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1384_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1385_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_1386_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1387_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_1388_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1390_ = v_opts_941_;
v_isShared_1391_ = v_isSharedCheck_1401_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_errorOnKinds_1386_);
lean_inc(v_bcFileName_x3f_1384_);
lean_inc(v_cFileName_x3f_1383_);
lean_inc(v_ileanFileName_x3f_1382_);
lean_inc(v_oleanFileName_x3f_1381_);
lean_inc(v_setupFileName_x3f_1380_);
lean_inc(v_rootDir_x3f_1379_);
lean_inc(v_opts_1376_);
lean_inc(v_forwardedArgs_1368_);
lean_inc(v_leanOpts_1367_);
lean_dec(v_opts_941_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1401_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1396_; 
v___x_1392_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6));
v___x_1393_ = lean_string_append(v___x_1392_, v_a_1362_);
lean_dec(v_a_1362_);
v___x_1394_ = lean_array_push(v_forwardedArgs_1368_, v___x_1393_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 1, v___x_1394_);
v___x_1396_ = v___x_1390_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_leanOpts_1367_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1400_, 2, v_opts_1376_);
lean_ctor_set(v_reuseFailAlloc_1400_, 3, v_rootDir_x3f_1379_);
lean_ctor_set(v_reuseFailAlloc_1400_, 4, v_setupFileName_x3f_1380_);
lean_ctor_set(v_reuseFailAlloc_1400_, 5, v_oleanFileName_x3f_1381_);
lean_ctor_set(v_reuseFailAlloc_1400_, 6, v_ileanFileName_x3f_1382_);
lean_ctor_set(v_reuseFailAlloc_1400_, 7, v_cFileName_x3f_1383_);
lean_ctor_set(v_reuseFailAlloc_1400_, 8, v_bcFileName_x3f_1384_);
lean_ctor_set(v_reuseFailAlloc_1400_, 9, v_errorOnKinds_1386_);
lean_ctor_set_uint8(v_reuseFailAlloc_1400_, sizeof(void*)*10 + 8, v_component_1369_);
lean_ctor_set_uint8(v_reuseFailAlloc_1400_, sizeof(void*)*10 + 9, v_printPrefix_1370_);
lean_ctor_set_uint8(v_reuseFailAlloc_1400_, sizeof(void*)*10 + 10, v_printLibDir_1371_);
lean_ctor_set_uint8(v_reuseFailAlloc_1400_, sizeof(void*)*10 + 11, v_useStdin_1372_);
lean_ctor_set_uint8(v_reuseFailAlloc_1400_, sizeof(void*)*10 + 12, v_onlyDeps_1373_);
lean_ctor_set_uint8(v_reuseFailAlloc_1400_, sizeof(void*)*10 + 13, v_onlySrcDeps_1374_);
lean_ctor_set_uint8(v_reuseFailAlloc_1400_, sizeof(void*)*10 + 14, v_depsJson_1375_);
lean_ctor_set_uint32(v_reuseFailAlloc_1400_, sizeof(void*)*10, v_trustLevel_1377_);
lean_ctor_set_uint32(v_reuseFailAlloc_1400_, sizeof(void*)*10 + 4, v_numThreads_1378_);
lean_ctor_set_uint8(v_reuseFailAlloc_1400_, sizeof(void*)*10 + 15, v_jsonOutput_1385_);
lean_ctor_set_uint8(v_reuseFailAlloc_1400_, sizeof(void*)*10 + 16, v_printStats_1387_);
lean_ctor_set_uint8(v_reuseFailAlloc_1400_, sizeof(void*)*10 + 17, v_run_1388_);
v___x_1396_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1398_; 
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v___x_1396_);
v___x_1398_ = v___x_1365_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
lean_dec(v_a_1362_);
lean_dec_ref(v_opts_941_);
v_a_1404_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1404_);
lean_dec_ref(v___x_1363_);
v___x_1408_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1409_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1408_);
lean_dec_ref(v___x_1409_);
goto v___jp_1405_;
v___jp_1405_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = lean_io_error_to_string(v_a_1404_);
v___x_1407_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1406_);
lean_dec_ref(v___x_1407_);
goto v___jp_1081_;
}
}
}
else
{
lean_object* v_a_1410_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
lean_dec_ref(v_opts_941_);
v_a_1410_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1410_);
lean_dec_ref(v___x_1361_);
v___x_1414_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1415_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1414_);
lean_dec_ref(v___x_1415_);
goto v___jp_1411_;
v___jp_1411_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = lean_io_error_to_string(v_a_1410_);
v___x_1413_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1412_);
lean_dec_ref(v___x_1413_);
goto v___jp_1023_;
}
}
}
}
else
{
uint8_t v___x_1416_; 
v___x_1416_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__12, &l___private_Lean_Shell_0__Lean_displayHelp___closed__12_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__12);
if (v___x_1416_ == 0)
{
lean_dec(v_optArg_x3f_943_);
lean_dec_ref(v_opts_941_);
goto v___jp_1063_;
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7));
v___x_1418_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1417_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1427_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1421_ = v___x_1418_;
v_isShared_1422_ = v_isSharedCheck_1427_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1418_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1427_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1423_ = lean_internal_enable_debug(v_a_1419_);
lean_dec(v_a_1419_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v_opts_941_);
v___x_1425_ = v___x_1421_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_opts_941_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_dec_ref(v_opts_941_);
v_a_1428_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1428_);
lean_dec_ref(v___x_1418_);
v___x_1432_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1433_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1432_);
lean_dec_ref(v___x_1433_);
goto v___jp_1429_;
v___jp_1429_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = lean_io_error_to_string(v_a_1428_);
v___x_1431_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1430_);
lean_dec_ref(v___x_1431_);
goto v___jp_1087_;
}
}
}
}
}
else
{
lean_object* v_leanOpts_1434_; lean_object* v_forwardedArgs_1435_; uint8_t v_component_1436_; uint8_t v_printPrefix_1437_; uint8_t v_printLibDir_1438_; uint8_t v_useStdin_1439_; uint8_t v_onlyDeps_1440_; uint8_t v_onlySrcDeps_1441_; uint8_t v_depsJson_1442_; lean_object* v_opts_1443_; uint32_t v_trustLevel_1444_; uint32_t v_numThreads_1445_; lean_object* v_rootDir_x3f_1446_; lean_object* v_setupFileName_x3f_1447_; lean_object* v_oleanFileName_x3f_1448_; lean_object* v_ileanFileName_x3f_1449_; lean_object* v_cFileName_x3f_1450_; lean_object* v_bcFileName_x3f_1451_; uint8_t v_jsonOutput_1452_; lean_object* v_errorOnKinds_1453_; uint8_t v_printStats_1454_; uint8_t v_run_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1465_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_1434_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1435_ = lean_ctor_get(v_opts_941_, 1);
v_component_1436_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_1437_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_1438_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_1439_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_1440_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1441_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_1442_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_1443_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1444_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_1445_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1446_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1447_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1448_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1449_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1450_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1451_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1452_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_1453_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1454_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_1455_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1457_ = v_opts_941_;
v_isShared_1458_ = v_isSharedCheck_1465_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_errorOnKinds_1453_);
lean_inc(v_bcFileName_x3f_1451_);
lean_inc(v_cFileName_x3f_1450_);
lean_inc(v_ileanFileName_x3f_1449_);
lean_inc(v_oleanFileName_x3f_1448_);
lean_inc(v_setupFileName_x3f_1447_);
lean_inc(v_rootDir_x3f_1446_);
lean_inc(v_opts_1443_);
lean_inc(v_forwardedArgs_1435_);
lean_inc(v_leanOpts_1434_);
lean_dec(v_opts_941_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1465_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1459_ = l_Lean_profiler;
v___x_1460_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_1434_, v___x_1459_, v___x_1200_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v___x_1460_);
v___x_1462_ = v___x_1457_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_forwardedArgs_1435_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_opts_1443_);
lean_ctor_set(v_reuseFailAlloc_1464_, 3, v_rootDir_x3f_1446_);
lean_ctor_set(v_reuseFailAlloc_1464_, 4, v_setupFileName_x3f_1447_);
lean_ctor_set(v_reuseFailAlloc_1464_, 5, v_oleanFileName_x3f_1448_);
lean_ctor_set(v_reuseFailAlloc_1464_, 6, v_ileanFileName_x3f_1449_);
lean_ctor_set(v_reuseFailAlloc_1464_, 7, v_cFileName_x3f_1450_);
lean_ctor_set(v_reuseFailAlloc_1464_, 8, v_bcFileName_x3f_1451_);
lean_ctor_set(v_reuseFailAlloc_1464_, 9, v_errorOnKinds_1453_);
lean_ctor_set_uint8(v_reuseFailAlloc_1464_, sizeof(void*)*10 + 8, v_component_1436_);
lean_ctor_set_uint8(v_reuseFailAlloc_1464_, sizeof(void*)*10 + 9, v_printPrefix_1437_);
lean_ctor_set_uint8(v_reuseFailAlloc_1464_, sizeof(void*)*10 + 10, v_printLibDir_1438_);
lean_ctor_set_uint8(v_reuseFailAlloc_1464_, sizeof(void*)*10 + 11, v_useStdin_1439_);
lean_ctor_set_uint8(v_reuseFailAlloc_1464_, sizeof(void*)*10 + 12, v_onlyDeps_1440_);
lean_ctor_set_uint8(v_reuseFailAlloc_1464_, sizeof(void*)*10 + 13, v_onlySrcDeps_1441_);
lean_ctor_set_uint8(v_reuseFailAlloc_1464_, sizeof(void*)*10 + 14, v_depsJson_1442_);
lean_ctor_set_uint32(v_reuseFailAlloc_1464_, sizeof(void*)*10, v_trustLevel_1444_);
lean_ctor_set_uint32(v_reuseFailAlloc_1464_, sizeof(void*)*10 + 4, v_numThreads_1445_);
lean_ctor_set_uint8(v_reuseFailAlloc_1464_, sizeof(void*)*10 + 15, v_jsonOutput_1452_);
lean_ctor_set_uint8(v_reuseFailAlloc_1464_, sizeof(void*)*10 + 16, v_printStats_1454_);
lean_ctor_set_uint8(v_reuseFailAlloc_1464_, sizeof(void*)*10 + 17, v_run_1455_);
v___x_1462_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1463_; 
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
return v___x_1463_;
}
}
}
}
else
{
lean_object* v_leanOpts_1466_; lean_object* v_forwardedArgs_1467_; uint8_t v_printPrefix_1468_; uint8_t v_printLibDir_1469_; uint8_t v_useStdin_1470_; uint8_t v_onlyDeps_1471_; uint8_t v_onlySrcDeps_1472_; uint8_t v_depsJson_1473_; lean_object* v_opts_1474_; uint32_t v_trustLevel_1475_; uint32_t v_numThreads_1476_; lean_object* v_rootDir_x3f_1477_; lean_object* v_setupFileName_x3f_1478_; lean_object* v_oleanFileName_x3f_1479_; lean_object* v_ileanFileName_x3f_1480_; lean_object* v_cFileName_x3f_1481_; lean_object* v_bcFileName_x3f_1482_; uint8_t v_jsonOutput_1483_; lean_object* v_errorOnKinds_1484_; uint8_t v_printStats_1485_; uint8_t v_run_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1495_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_1466_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1467_ = lean_ctor_get(v_opts_941_, 1);
v_printPrefix_1468_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_1469_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_1470_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_1471_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1472_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_1473_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_1474_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1475_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_1476_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1477_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1478_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1479_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1480_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1481_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1482_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1483_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_1484_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1485_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_1486_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_1495_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1488_ = v_opts_941_;
v_isShared_1489_ = v_isSharedCheck_1495_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_errorOnKinds_1484_);
lean_inc(v_bcFileName_x3f_1482_);
lean_inc(v_cFileName_x3f_1481_);
lean_inc(v_ileanFileName_x3f_1480_);
lean_inc(v_oleanFileName_x3f_1479_);
lean_inc(v_setupFileName_x3f_1478_);
lean_inc(v_rootDir_x3f_1477_);
lean_inc(v_opts_1474_);
lean_inc(v_forwardedArgs_1467_);
lean_inc(v_leanOpts_1466_);
lean_dec(v_opts_941_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1495_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
uint8_t v___x_1490_; lean_object* v___x_1492_; 
v___x_1490_ = 2;
if (v_isShared_1489_ == 0)
{
v___x_1492_ = v___x_1488_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_leanOpts_1466_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v_forwardedArgs_1467_);
lean_ctor_set(v_reuseFailAlloc_1494_, 2, v_opts_1474_);
lean_ctor_set(v_reuseFailAlloc_1494_, 3, v_rootDir_x3f_1477_);
lean_ctor_set(v_reuseFailAlloc_1494_, 4, v_setupFileName_x3f_1478_);
lean_ctor_set(v_reuseFailAlloc_1494_, 5, v_oleanFileName_x3f_1479_);
lean_ctor_set(v_reuseFailAlloc_1494_, 6, v_ileanFileName_x3f_1480_);
lean_ctor_set(v_reuseFailAlloc_1494_, 7, v_cFileName_x3f_1481_);
lean_ctor_set(v_reuseFailAlloc_1494_, 8, v_bcFileName_x3f_1482_);
lean_ctor_set(v_reuseFailAlloc_1494_, 9, v_errorOnKinds_1484_);
lean_ctor_set_uint8(v_reuseFailAlloc_1494_, sizeof(void*)*10 + 9, v_printPrefix_1468_);
lean_ctor_set_uint8(v_reuseFailAlloc_1494_, sizeof(void*)*10 + 10, v_printLibDir_1469_);
lean_ctor_set_uint8(v_reuseFailAlloc_1494_, sizeof(void*)*10 + 11, v_useStdin_1470_);
lean_ctor_set_uint8(v_reuseFailAlloc_1494_, sizeof(void*)*10 + 12, v_onlyDeps_1471_);
lean_ctor_set_uint8(v_reuseFailAlloc_1494_, sizeof(void*)*10 + 13, v_onlySrcDeps_1472_);
lean_ctor_set_uint8(v_reuseFailAlloc_1494_, sizeof(void*)*10 + 14, v_depsJson_1473_);
lean_ctor_set_uint32(v_reuseFailAlloc_1494_, sizeof(void*)*10, v_trustLevel_1475_);
lean_ctor_set_uint32(v_reuseFailAlloc_1494_, sizeof(void*)*10 + 4, v_numThreads_1476_);
lean_ctor_set_uint8(v_reuseFailAlloc_1494_, sizeof(void*)*10 + 15, v_jsonOutput_1483_);
lean_ctor_set_uint8(v_reuseFailAlloc_1494_, sizeof(void*)*10 + 16, v_printStats_1485_);
lean_ctor_set_uint8(v_reuseFailAlloc_1494_, sizeof(void*)*10 + 17, v_run_1486_);
v___x_1492_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
lean_object* v___x_1493_; 
lean_ctor_set_uint8(v___x_1492_, sizeof(void*)*10 + 8, v___x_1490_);
v___x_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1492_);
return v___x_1493_;
}
}
}
}
else
{
lean_object* v_leanOpts_1496_; lean_object* v_forwardedArgs_1497_; uint8_t v_printPrefix_1498_; uint8_t v_printLibDir_1499_; uint8_t v_useStdin_1500_; uint8_t v_onlyDeps_1501_; uint8_t v_onlySrcDeps_1502_; uint8_t v_depsJson_1503_; lean_object* v_opts_1504_; uint32_t v_trustLevel_1505_; uint32_t v_numThreads_1506_; lean_object* v_rootDir_x3f_1507_; lean_object* v_setupFileName_x3f_1508_; lean_object* v_oleanFileName_x3f_1509_; lean_object* v_ileanFileName_x3f_1510_; lean_object* v_cFileName_x3f_1511_; lean_object* v_bcFileName_x3f_1512_; uint8_t v_jsonOutput_1513_; lean_object* v_errorOnKinds_1514_; uint8_t v_printStats_1515_; uint8_t v_run_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1525_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_1496_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1497_ = lean_ctor_get(v_opts_941_, 1);
v_printPrefix_1498_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_1499_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_1500_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_1501_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1502_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_1503_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_1504_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1505_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_1506_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1507_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1508_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1509_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1510_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1511_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1512_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1513_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_1514_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1515_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_1516_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_1525_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1518_ = v_opts_941_;
v_isShared_1519_ = v_isSharedCheck_1525_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_errorOnKinds_1514_);
lean_inc(v_bcFileName_x3f_1512_);
lean_inc(v_cFileName_x3f_1511_);
lean_inc(v_ileanFileName_x3f_1510_);
lean_inc(v_oleanFileName_x3f_1509_);
lean_inc(v_setupFileName_x3f_1508_);
lean_inc(v_rootDir_x3f_1507_);
lean_inc(v_opts_1504_);
lean_inc(v_forwardedArgs_1497_);
lean_inc(v_leanOpts_1496_);
lean_dec(v_opts_941_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1525_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
uint8_t v___x_1520_; lean_object* v___x_1522_; 
v___x_1520_ = 1;
if (v_isShared_1519_ == 0)
{
v___x_1522_ = v___x_1518_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_leanOpts_1496_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_forwardedArgs_1497_);
lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_opts_1504_);
lean_ctor_set(v_reuseFailAlloc_1524_, 3, v_rootDir_x3f_1507_);
lean_ctor_set(v_reuseFailAlloc_1524_, 4, v_setupFileName_x3f_1508_);
lean_ctor_set(v_reuseFailAlloc_1524_, 5, v_oleanFileName_x3f_1509_);
lean_ctor_set(v_reuseFailAlloc_1524_, 6, v_ileanFileName_x3f_1510_);
lean_ctor_set(v_reuseFailAlloc_1524_, 7, v_cFileName_x3f_1511_);
lean_ctor_set(v_reuseFailAlloc_1524_, 8, v_bcFileName_x3f_1512_);
lean_ctor_set(v_reuseFailAlloc_1524_, 9, v_errorOnKinds_1514_);
lean_ctor_set_uint8(v_reuseFailAlloc_1524_, sizeof(void*)*10 + 9, v_printPrefix_1498_);
lean_ctor_set_uint8(v_reuseFailAlloc_1524_, sizeof(void*)*10 + 10, v_printLibDir_1499_);
lean_ctor_set_uint8(v_reuseFailAlloc_1524_, sizeof(void*)*10 + 11, v_useStdin_1500_);
lean_ctor_set_uint8(v_reuseFailAlloc_1524_, sizeof(void*)*10 + 12, v_onlyDeps_1501_);
lean_ctor_set_uint8(v_reuseFailAlloc_1524_, sizeof(void*)*10 + 13, v_onlySrcDeps_1502_);
lean_ctor_set_uint8(v_reuseFailAlloc_1524_, sizeof(void*)*10 + 14, v_depsJson_1503_);
lean_ctor_set_uint32(v_reuseFailAlloc_1524_, sizeof(void*)*10, v_trustLevel_1505_);
lean_ctor_set_uint32(v_reuseFailAlloc_1524_, sizeof(void*)*10 + 4, v_numThreads_1506_);
lean_ctor_set_uint8(v_reuseFailAlloc_1524_, sizeof(void*)*10 + 15, v_jsonOutput_1513_);
lean_ctor_set_uint8(v_reuseFailAlloc_1524_, sizeof(void*)*10 + 16, v_printStats_1515_);
lean_ctor_set_uint8(v_reuseFailAlloc_1524_, sizeof(void*)*10 + 17, v_run_1516_);
v___x_1522_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
lean_object* v___x_1523_; 
lean_ctor_set_uint8(v___x_1522_, sizeof(void*)*10 + 8, v___x_1520_);
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
return v___x_1523_;
}
}
}
}
else
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8));
v___x_1527_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1526_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; lean_object* v_leanOpts_1529_; lean_object* v_forwardedArgs_1530_; uint8_t v_component_1531_; uint8_t v_printPrefix_1532_; uint8_t v_printLibDir_1533_; uint8_t v_useStdin_1534_; uint8_t v_onlyDeps_1535_; uint8_t v_onlySrcDeps_1536_; uint8_t v_depsJson_1537_; lean_object* v_opts_1538_; uint32_t v_trustLevel_1539_; uint32_t v_numThreads_1540_; lean_object* v_rootDir_x3f_1541_; lean_object* v_setupFileName_x3f_1542_; lean_object* v_oleanFileName_x3f_1543_; lean_object* v_ileanFileName_x3f_1544_; lean_object* v_cFileName_x3f_1545_; lean_object* v_bcFileName_x3f_1546_; uint8_t v_jsonOutput_1547_; lean_object* v_errorOnKinds_1548_; uint8_t v_printStats_1549_; uint8_t v_run_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1575_; 
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1528_);
lean_dec_ref(v___x_1527_);
v_leanOpts_1529_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1530_ = lean_ctor_get(v_opts_941_, 1);
v_component_1531_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_1532_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_1533_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_1534_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_1535_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1536_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_1537_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_1538_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1539_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_1540_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1541_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1542_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1543_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1544_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1545_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1546_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1547_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_1548_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1549_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_1550_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1552_ = v_opts_941_;
v_isShared_1553_ = v_isSharedCheck_1575_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_errorOnKinds_1548_);
lean_inc(v_bcFileName_x3f_1546_);
lean_inc(v_cFileName_x3f_1545_);
lean_inc(v_ileanFileName_x3f_1544_);
lean_inc(v_oleanFileName_x3f_1543_);
lean_inc(v_setupFileName_x3f_1542_);
lean_inc(v_rootDir_x3f_1541_);
lean_inc(v_opts_1538_);
lean_inc(v_forwardedArgs_1530_);
lean_inc(v_leanOpts_1529_);
lean_dec(v_opts_941_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1575_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1554_; 
lean_inc(v_a_1528_);
v___x_1554_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_leanOpts_1529_, v_a_1528_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1568_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1557_ = v___x_1554_;
v_isShared_1558_ = v_isSharedCheck_1568_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1554_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1568_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1559_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9));
v___x_1560_ = lean_string_append(v___x_1559_, v_a_1528_);
lean_dec(v_a_1528_);
v___x_1561_ = lean_array_push(v_forwardedArgs_1530_, v___x_1560_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 1, v___x_1561_);
lean_ctor_set(v___x_1552_, 0, v_a_1555_);
v___x_1563_ = v___x_1552_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1555_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v___x_1561_);
lean_ctor_set(v_reuseFailAlloc_1567_, 2, v_opts_1538_);
lean_ctor_set(v_reuseFailAlloc_1567_, 3, v_rootDir_x3f_1541_);
lean_ctor_set(v_reuseFailAlloc_1567_, 4, v_setupFileName_x3f_1542_);
lean_ctor_set(v_reuseFailAlloc_1567_, 5, v_oleanFileName_x3f_1543_);
lean_ctor_set(v_reuseFailAlloc_1567_, 6, v_ileanFileName_x3f_1544_);
lean_ctor_set(v_reuseFailAlloc_1567_, 7, v_cFileName_x3f_1545_);
lean_ctor_set(v_reuseFailAlloc_1567_, 8, v_bcFileName_x3f_1546_);
lean_ctor_set(v_reuseFailAlloc_1567_, 9, v_errorOnKinds_1548_);
lean_ctor_set_uint8(v_reuseFailAlloc_1567_, sizeof(void*)*10 + 8, v_component_1531_);
lean_ctor_set_uint8(v_reuseFailAlloc_1567_, sizeof(void*)*10 + 9, v_printPrefix_1532_);
lean_ctor_set_uint8(v_reuseFailAlloc_1567_, sizeof(void*)*10 + 10, v_printLibDir_1533_);
lean_ctor_set_uint8(v_reuseFailAlloc_1567_, sizeof(void*)*10 + 11, v_useStdin_1534_);
lean_ctor_set_uint8(v_reuseFailAlloc_1567_, sizeof(void*)*10 + 12, v_onlyDeps_1535_);
lean_ctor_set_uint8(v_reuseFailAlloc_1567_, sizeof(void*)*10 + 13, v_onlySrcDeps_1536_);
lean_ctor_set_uint8(v_reuseFailAlloc_1567_, sizeof(void*)*10 + 14, v_depsJson_1537_);
lean_ctor_set_uint32(v_reuseFailAlloc_1567_, sizeof(void*)*10, v_trustLevel_1539_);
lean_ctor_set_uint32(v_reuseFailAlloc_1567_, sizeof(void*)*10 + 4, v_numThreads_1540_);
lean_ctor_set_uint8(v_reuseFailAlloc_1567_, sizeof(void*)*10 + 15, v_jsonOutput_1547_);
lean_ctor_set_uint8(v_reuseFailAlloc_1567_, sizeof(void*)*10 + 16, v_printStats_1549_);
lean_ctor_set_uint8(v_reuseFailAlloc_1567_, sizeof(void*)*10 + 17, v_run_1550_);
v___x_1563_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
lean_object* v___x_1565_; 
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 0, v___x_1563_);
v___x_1565_ = v___x_1557_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
lean_del_object(v___x_1552_);
lean_dec_ref(v_errorOnKinds_1548_);
lean_dec(v_bcFileName_x3f_1546_);
lean_dec(v_cFileName_x3f_1545_);
lean_dec(v_ileanFileName_x3f_1544_);
lean_dec(v_oleanFileName_x3f_1543_);
lean_dec(v_setupFileName_x3f_1542_);
lean_dec(v_rootDir_x3f_1541_);
lean_dec_ref(v_opts_1538_);
lean_dec_ref(v_forwardedArgs_1530_);
lean_dec(v_a_1528_);
v_a_1569_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1569_);
lean_dec_ref(v___x_1554_);
v___x_1573_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1574_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1573_);
lean_dec_ref(v___x_1574_);
goto v___jp_1570_;
v___jp_1570_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = lean_io_error_to_string(v_a_1569_);
v___x_1572_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1571_);
lean_dec_ref(v___x_1572_);
goto v___jp_1017_;
}
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
lean_dec_ref(v_opts_941_);
v_a_1576_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1576_);
lean_dec_ref(v___x_1527_);
v___x_1580_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1581_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1580_);
lean_dec_ref(v___x_1581_);
goto v___jp_1577_;
v___jp_1577_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = lean_io_error_to_string(v_a_1576_);
v___x_1579_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1578_);
lean_dec_ref(v___x_1579_);
goto v___jp_1093_;
}
}
}
}
else
{
lean_object* v_leanOpts_1582_; lean_object* v_forwardedArgs_1583_; uint8_t v_component_1584_; uint8_t v_printPrefix_1585_; uint8_t v_useStdin_1586_; uint8_t v_onlyDeps_1587_; uint8_t v_onlySrcDeps_1588_; uint8_t v_depsJson_1589_; lean_object* v_opts_1590_; uint32_t v_trustLevel_1591_; uint32_t v_numThreads_1592_; lean_object* v_rootDir_x3f_1593_; lean_object* v_setupFileName_x3f_1594_; lean_object* v_oleanFileName_x3f_1595_; lean_object* v_ileanFileName_x3f_1596_; lean_object* v_cFileName_x3f_1597_; lean_object* v_bcFileName_x3f_1598_; uint8_t v_jsonOutput_1599_; lean_object* v_errorOnKinds_1600_; uint8_t v_printStats_1601_; uint8_t v_run_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1610_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_1582_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1583_ = lean_ctor_get(v_opts_941_, 1);
v_component_1584_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_1585_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_useStdin_1586_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_1587_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1588_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_1589_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_1590_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1591_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_1592_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1593_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1594_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1595_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1596_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1597_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1598_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1599_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_1600_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1601_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_1602_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1604_ = v_opts_941_;
v_isShared_1605_ = v_isSharedCheck_1610_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_errorOnKinds_1600_);
lean_inc(v_bcFileName_x3f_1598_);
lean_inc(v_cFileName_x3f_1597_);
lean_inc(v_ileanFileName_x3f_1596_);
lean_inc(v_oleanFileName_x3f_1595_);
lean_inc(v_setupFileName_x3f_1594_);
lean_inc(v_rootDir_x3f_1593_);
lean_inc(v_opts_1590_);
lean_inc(v_forwardedArgs_1583_);
lean_inc(v_leanOpts_1582_);
lean_dec(v_opts_941_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1610_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_leanOpts_1582_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_forwardedArgs_1583_);
lean_ctor_set(v_reuseFailAlloc_1609_, 2, v_opts_1590_);
lean_ctor_set(v_reuseFailAlloc_1609_, 3, v_rootDir_x3f_1593_);
lean_ctor_set(v_reuseFailAlloc_1609_, 4, v_setupFileName_x3f_1594_);
lean_ctor_set(v_reuseFailAlloc_1609_, 5, v_oleanFileName_x3f_1595_);
lean_ctor_set(v_reuseFailAlloc_1609_, 6, v_ileanFileName_x3f_1596_);
lean_ctor_set(v_reuseFailAlloc_1609_, 7, v_cFileName_x3f_1597_);
lean_ctor_set(v_reuseFailAlloc_1609_, 8, v_bcFileName_x3f_1598_);
lean_ctor_set(v_reuseFailAlloc_1609_, 9, v_errorOnKinds_1600_);
lean_ctor_set_uint8(v_reuseFailAlloc_1609_, sizeof(void*)*10 + 8, v_component_1584_);
lean_ctor_set_uint8(v_reuseFailAlloc_1609_, sizeof(void*)*10 + 9, v_printPrefix_1585_);
lean_ctor_set_uint8(v_reuseFailAlloc_1609_, sizeof(void*)*10 + 11, v_useStdin_1586_);
lean_ctor_set_uint8(v_reuseFailAlloc_1609_, sizeof(void*)*10 + 12, v_onlyDeps_1587_);
lean_ctor_set_uint8(v_reuseFailAlloc_1609_, sizeof(void*)*10 + 13, v_onlySrcDeps_1588_);
lean_ctor_set_uint8(v_reuseFailAlloc_1609_, sizeof(void*)*10 + 14, v_depsJson_1589_);
lean_ctor_set_uint32(v_reuseFailAlloc_1609_, sizeof(void*)*10, v_trustLevel_1591_);
lean_ctor_set_uint32(v_reuseFailAlloc_1609_, sizeof(void*)*10 + 4, v_numThreads_1592_);
lean_ctor_set_uint8(v_reuseFailAlloc_1609_, sizeof(void*)*10 + 15, v_jsonOutput_1599_);
lean_ctor_set_uint8(v_reuseFailAlloc_1609_, sizeof(void*)*10 + 16, v_printStats_1601_);
lean_ctor_set_uint8(v_reuseFailAlloc_1609_, sizeof(void*)*10 + 17, v_run_1602_);
v___x_1607_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
lean_object* v___x_1608_; 
lean_ctor_set_uint8(v___x_1607_, sizeof(void*)*10 + 10, v___x_1192_);
v___x_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
return v___x_1608_;
}
}
}
}
else
{
lean_object* v_leanOpts_1611_; lean_object* v_forwardedArgs_1612_; uint8_t v_component_1613_; uint8_t v_printLibDir_1614_; uint8_t v_useStdin_1615_; uint8_t v_onlyDeps_1616_; uint8_t v_onlySrcDeps_1617_; uint8_t v_depsJson_1618_; lean_object* v_opts_1619_; uint32_t v_trustLevel_1620_; uint32_t v_numThreads_1621_; lean_object* v_rootDir_x3f_1622_; lean_object* v_setupFileName_x3f_1623_; lean_object* v_oleanFileName_x3f_1624_; lean_object* v_ileanFileName_x3f_1625_; lean_object* v_cFileName_x3f_1626_; lean_object* v_bcFileName_x3f_1627_; uint8_t v_jsonOutput_1628_; lean_object* v_errorOnKinds_1629_; uint8_t v_printStats_1630_; uint8_t v_run_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1639_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_1611_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1612_ = lean_ctor_get(v_opts_941_, 1);
v_component_1613_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printLibDir_1614_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_1615_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_1616_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1617_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_1618_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_1619_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1620_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_1621_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1622_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1623_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1624_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1625_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1626_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1627_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1628_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_1629_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1630_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_1631_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_1639_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1633_ = v_opts_941_;
v_isShared_1634_ = v_isSharedCheck_1639_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_errorOnKinds_1629_);
lean_inc(v_bcFileName_x3f_1627_);
lean_inc(v_cFileName_x3f_1626_);
lean_inc(v_ileanFileName_x3f_1625_);
lean_inc(v_oleanFileName_x3f_1624_);
lean_inc(v_setupFileName_x3f_1623_);
lean_inc(v_rootDir_x3f_1622_);
lean_inc(v_opts_1619_);
lean_inc(v_forwardedArgs_1612_);
lean_inc(v_leanOpts_1611_);
lean_dec(v_opts_941_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1639_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_leanOpts_1611_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_forwardedArgs_1612_);
lean_ctor_set(v_reuseFailAlloc_1638_, 2, v_opts_1619_);
lean_ctor_set(v_reuseFailAlloc_1638_, 3, v_rootDir_x3f_1622_);
lean_ctor_set(v_reuseFailAlloc_1638_, 4, v_setupFileName_x3f_1623_);
lean_ctor_set(v_reuseFailAlloc_1638_, 5, v_oleanFileName_x3f_1624_);
lean_ctor_set(v_reuseFailAlloc_1638_, 6, v_ileanFileName_x3f_1625_);
lean_ctor_set(v_reuseFailAlloc_1638_, 7, v_cFileName_x3f_1626_);
lean_ctor_set(v_reuseFailAlloc_1638_, 8, v_bcFileName_x3f_1627_);
lean_ctor_set(v_reuseFailAlloc_1638_, 9, v_errorOnKinds_1629_);
lean_ctor_set_uint8(v_reuseFailAlloc_1638_, sizeof(void*)*10 + 8, v_component_1613_);
lean_ctor_set_uint8(v_reuseFailAlloc_1638_, sizeof(void*)*10 + 10, v_printLibDir_1614_);
lean_ctor_set_uint8(v_reuseFailAlloc_1638_, sizeof(void*)*10 + 11, v_useStdin_1615_);
lean_ctor_set_uint8(v_reuseFailAlloc_1638_, sizeof(void*)*10 + 12, v_onlyDeps_1616_);
lean_ctor_set_uint8(v_reuseFailAlloc_1638_, sizeof(void*)*10 + 13, v_onlySrcDeps_1617_);
lean_ctor_set_uint8(v_reuseFailAlloc_1638_, sizeof(void*)*10 + 14, v_depsJson_1618_);
lean_ctor_set_uint32(v_reuseFailAlloc_1638_, sizeof(void*)*10, v_trustLevel_1620_);
lean_ctor_set_uint32(v_reuseFailAlloc_1638_, sizeof(void*)*10 + 4, v_numThreads_1621_);
lean_ctor_set_uint8(v_reuseFailAlloc_1638_, sizeof(void*)*10 + 15, v_jsonOutput_1628_);
lean_ctor_set_uint8(v_reuseFailAlloc_1638_, sizeof(void*)*10 + 16, v_printStats_1630_);
lean_ctor_set_uint8(v_reuseFailAlloc_1638_, sizeof(void*)*10 + 17, v_run_1631_);
v___x_1636_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1637_; 
lean_ctor_set_uint8(v___x_1636_, sizeof(void*)*10 + 9, v___x_1190_);
v___x_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
return v___x_1637_;
}
}
}
}
else
{
lean_object* v_leanOpts_1640_; lean_object* v_forwardedArgs_1641_; uint8_t v_component_1642_; uint8_t v_printPrefix_1643_; uint8_t v_printLibDir_1644_; uint8_t v_useStdin_1645_; uint8_t v_onlyDeps_1646_; uint8_t v_onlySrcDeps_1647_; uint8_t v_depsJson_1648_; lean_object* v_opts_1649_; uint32_t v_trustLevel_1650_; uint32_t v_numThreads_1651_; lean_object* v_rootDir_x3f_1652_; lean_object* v_setupFileName_x3f_1653_; lean_object* v_oleanFileName_x3f_1654_; lean_object* v_ileanFileName_x3f_1655_; lean_object* v_cFileName_x3f_1656_; lean_object* v_bcFileName_x3f_1657_; uint8_t v_jsonOutput_1658_; lean_object* v_errorOnKinds_1659_; uint8_t v_run_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1668_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_1640_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1641_ = lean_ctor_get(v_opts_941_, 1);
v_component_1642_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_1643_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_1644_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_1645_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_1646_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1647_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_1648_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_1649_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1650_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_1651_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1652_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1653_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1654_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1655_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1656_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1657_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1658_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_1659_ = lean_ctor_get(v_opts_941_, 9);
v_run_1660_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_1668_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1662_ = v_opts_941_;
v_isShared_1663_ = v_isSharedCheck_1668_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_errorOnKinds_1659_);
lean_inc(v_bcFileName_x3f_1657_);
lean_inc(v_cFileName_x3f_1656_);
lean_inc(v_ileanFileName_x3f_1655_);
lean_inc(v_oleanFileName_x3f_1654_);
lean_inc(v_setupFileName_x3f_1653_);
lean_inc(v_rootDir_x3f_1652_);
lean_inc(v_opts_1649_);
lean_inc(v_forwardedArgs_1641_);
lean_inc(v_leanOpts_1640_);
lean_dec(v_opts_941_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1668_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_leanOpts_1640_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_forwardedArgs_1641_);
lean_ctor_set(v_reuseFailAlloc_1667_, 2, v_opts_1649_);
lean_ctor_set(v_reuseFailAlloc_1667_, 3, v_rootDir_x3f_1652_);
lean_ctor_set(v_reuseFailAlloc_1667_, 4, v_setupFileName_x3f_1653_);
lean_ctor_set(v_reuseFailAlloc_1667_, 5, v_oleanFileName_x3f_1654_);
lean_ctor_set(v_reuseFailAlloc_1667_, 6, v_ileanFileName_x3f_1655_);
lean_ctor_set(v_reuseFailAlloc_1667_, 7, v_cFileName_x3f_1656_);
lean_ctor_set(v_reuseFailAlloc_1667_, 8, v_bcFileName_x3f_1657_);
lean_ctor_set(v_reuseFailAlloc_1667_, 9, v_errorOnKinds_1659_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, sizeof(void*)*10 + 8, v_component_1642_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, sizeof(void*)*10 + 9, v_printPrefix_1643_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, sizeof(void*)*10 + 10, v_printLibDir_1644_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, sizeof(void*)*10 + 11, v_useStdin_1645_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, sizeof(void*)*10 + 12, v_onlyDeps_1646_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, sizeof(void*)*10 + 13, v_onlySrcDeps_1647_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, sizeof(void*)*10 + 14, v_depsJson_1648_);
lean_ctor_set_uint32(v_reuseFailAlloc_1667_, sizeof(void*)*10, v_trustLevel_1650_);
lean_ctor_set_uint32(v_reuseFailAlloc_1667_, sizeof(void*)*10 + 4, v_numThreads_1651_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, sizeof(void*)*10 + 15, v_jsonOutput_1658_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, sizeof(void*)*10 + 17, v_run_1660_);
v___x_1665_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v___x_1666_; 
lean_ctor_set_uint8(v___x_1665_, sizeof(void*)*10 + 16, v___x_1188_);
v___x_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
return v___x_1666_;
}
}
}
}
else
{
lean_object* v_leanOpts_1669_; lean_object* v_forwardedArgs_1670_; uint8_t v_component_1671_; uint8_t v_printPrefix_1672_; uint8_t v_printLibDir_1673_; uint8_t v_useStdin_1674_; uint8_t v_onlyDeps_1675_; uint8_t v_onlySrcDeps_1676_; uint8_t v_depsJson_1677_; lean_object* v_opts_1678_; uint32_t v_trustLevel_1679_; uint32_t v_numThreads_1680_; lean_object* v_rootDir_x3f_1681_; lean_object* v_setupFileName_x3f_1682_; lean_object* v_oleanFileName_x3f_1683_; lean_object* v_ileanFileName_x3f_1684_; lean_object* v_cFileName_x3f_1685_; lean_object* v_bcFileName_x3f_1686_; lean_object* v_errorOnKinds_1687_; uint8_t v_printStats_1688_; uint8_t v_run_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1697_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_1669_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1670_ = lean_ctor_get(v_opts_941_, 1);
v_component_1671_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_1672_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_1673_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_1674_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_1675_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1676_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_1677_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_1678_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1679_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_1680_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1681_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1682_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1683_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1684_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1685_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1686_ = lean_ctor_get(v_opts_941_, 8);
v_errorOnKinds_1687_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1688_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_1689_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1691_ = v_opts_941_;
v_isShared_1692_ = v_isSharedCheck_1697_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_errorOnKinds_1687_);
lean_inc(v_bcFileName_x3f_1686_);
lean_inc(v_cFileName_x3f_1685_);
lean_inc(v_ileanFileName_x3f_1684_);
lean_inc(v_oleanFileName_x3f_1683_);
lean_inc(v_setupFileName_x3f_1682_);
lean_inc(v_rootDir_x3f_1681_);
lean_inc(v_opts_1678_);
lean_inc(v_forwardedArgs_1670_);
lean_inc(v_leanOpts_1669_);
lean_dec(v_opts_941_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1697_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_leanOpts_1669_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_forwardedArgs_1670_);
lean_ctor_set(v_reuseFailAlloc_1696_, 2, v_opts_1678_);
lean_ctor_set(v_reuseFailAlloc_1696_, 3, v_rootDir_x3f_1681_);
lean_ctor_set(v_reuseFailAlloc_1696_, 4, v_setupFileName_x3f_1682_);
lean_ctor_set(v_reuseFailAlloc_1696_, 5, v_oleanFileName_x3f_1683_);
lean_ctor_set(v_reuseFailAlloc_1696_, 6, v_ileanFileName_x3f_1684_);
lean_ctor_set(v_reuseFailAlloc_1696_, 7, v_cFileName_x3f_1685_);
lean_ctor_set(v_reuseFailAlloc_1696_, 8, v_bcFileName_x3f_1686_);
lean_ctor_set(v_reuseFailAlloc_1696_, 9, v_errorOnKinds_1687_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, sizeof(void*)*10 + 8, v_component_1671_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, sizeof(void*)*10 + 9, v_printPrefix_1672_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, sizeof(void*)*10 + 10, v_printLibDir_1673_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, sizeof(void*)*10 + 11, v_useStdin_1674_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, sizeof(void*)*10 + 12, v_onlyDeps_1675_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, sizeof(void*)*10 + 13, v_onlySrcDeps_1676_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, sizeof(void*)*10 + 14, v_depsJson_1677_);
lean_ctor_set_uint32(v_reuseFailAlloc_1696_, sizeof(void*)*10, v_trustLevel_1679_);
lean_ctor_set_uint32(v_reuseFailAlloc_1696_, sizeof(void*)*10 + 4, v_numThreads_1680_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, sizeof(void*)*10 + 16, v_printStats_1688_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, sizeof(void*)*10 + 17, v_run_1689_);
v___x_1694_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
lean_object* v___x_1695_; 
lean_ctor_set_uint8(v___x_1694_, sizeof(void*)*10 + 15, v___x_1186_);
v___x_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
return v___x_1695_;
}
}
}
}
else
{
lean_object* v_leanOpts_1698_; lean_object* v_forwardedArgs_1699_; uint8_t v_component_1700_; uint8_t v_printPrefix_1701_; uint8_t v_printLibDir_1702_; uint8_t v_useStdin_1703_; uint8_t v_onlySrcDeps_1704_; lean_object* v_opts_1705_; uint32_t v_trustLevel_1706_; uint32_t v_numThreads_1707_; lean_object* v_rootDir_x3f_1708_; lean_object* v_setupFileName_x3f_1709_; lean_object* v_oleanFileName_x3f_1710_; lean_object* v_ileanFileName_x3f_1711_; lean_object* v_cFileName_x3f_1712_; lean_object* v_bcFileName_x3f_1713_; uint8_t v_jsonOutput_1714_; lean_object* v_errorOnKinds_1715_; uint8_t v_printStats_1716_; uint8_t v_run_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1725_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_1698_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1699_ = lean_ctor_get(v_opts_941_, 1);
v_component_1700_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_1701_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_1702_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_1703_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlySrcDeps_1704_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_opts_1705_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1706_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_1707_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1708_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1709_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1710_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1711_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1712_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1713_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1714_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_1715_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1716_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_1717_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1719_ = v_opts_941_;
v_isShared_1720_ = v_isSharedCheck_1725_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_errorOnKinds_1715_);
lean_inc(v_bcFileName_x3f_1713_);
lean_inc(v_cFileName_x3f_1712_);
lean_inc(v_ileanFileName_x3f_1711_);
lean_inc(v_oleanFileName_x3f_1710_);
lean_inc(v_setupFileName_x3f_1709_);
lean_inc(v_rootDir_x3f_1708_);
lean_inc(v_opts_1705_);
lean_inc(v_forwardedArgs_1699_);
lean_inc(v_leanOpts_1698_);
lean_dec(v_opts_941_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1725_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_leanOpts_1698_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_forwardedArgs_1699_);
lean_ctor_set(v_reuseFailAlloc_1724_, 2, v_opts_1705_);
lean_ctor_set(v_reuseFailAlloc_1724_, 3, v_rootDir_x3f_1708_);
lean_ctor_set(v_reuseFailAlloc_1724_, 4, v_setupFileName_x3f_1709_);
lean_ctor_set(v_reuseFailAlloc_1724_, 5, v_oleanFileName_x3f_1710_);
lean_ctor_set(v_reuseFailAlloc_1724_, 6, v_ileanFileName_x3f_1711_);
lean_ctor_set(v_reuseFailAlloc_1724_, 7, v_cFileName_x3f_1712_);
lean_ctor_set(v_reuseFailAlloc_1724_, 8, v_bcFileName_x3f_1713_);
lean_ctor_set(v_reuseFailAlloc_1724_, 9, v_errorOnKinds_1715_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, sizeof(void*)*10 + 8, v_component_1700_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, sizeof(void*)*10 + 9, v_printPrefix_1701_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, sizeof(void*)*10 + 10, v_printLibDir_1702_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, sizeof(void*)*10 + 11, v_useStdin_1703_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, sizeof(void*)*10 + 13, v_onlySrcDeps_1704_);
lean_ctor_set_uint32(v_reuseFailAlloc_1724_, sizeof(void*)*10, v_trustLevel_1706_);
lean_ctor_set_uint32(v_reuseFailAlloc_1724_, sizeof(void*)*10 + 4, v_numThreads_1707_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, sizeof(void*)*10 + 15, v_jsonOutput_1714_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, sizeof(void*)*10 + 16, v_printStats_1716_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, sizeof(void*)*10 + 17, v_run_1717_);
v___x_1722_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
lean_object* v___x_1723_; 
lean_ctor_set_uint8(v___x_1722_, sizeof(void*)*10 + 12, v___x_1184_);
lean_ctor_set_uint8(v___x_1722_, sizeof(void*)*10 + 14, v___x_1184_);
v___x_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
return v___x_1723_;
}
}
}
}
else
{
lean_object* v_leanOpts_1726_; lean_object* v_forwardedArgs_1727_; uint8_t v_component_1728_; uint8_t v_printPrefix_1729_; uint8_t v_printLibDir_1730_; uint8_t v_useStdin_1731_; uint8_t v_onlyDeps_1732_; uint8_t v_depsJson_1733_; lean_object* v_opts_1734_; uint32_t v_trustLevel_1735_; uint32_t v_numThreads_1736_; lean_object* v_rootDir_x3f_1737_; lean_object* v_setupFileName_x3f_1738_; lean_object* v_oleanFileName_x3f_1739_; lean_object* v_ileanFileName_x3f_1740_; lean_object* v_cFileName_x3f_1741_; lean_object* v_bcFileName_x3f_1742_; uint8_t v_jsonOutput_1743_; lean_object* v_errorOnKinds_1744_; uint8_t v_printStats_1745_; uint8_t v_run_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1754_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_1726_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1727_ = lean_ctor_get(v_opts_941_, 1);
v_component_1728_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_1729_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_1730_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_1731_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_1732_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_depsJson_1733_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_1734_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1735_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_1736_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1737_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1738_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1739_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1740_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1741_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1742_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1743_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_1744_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1745_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_1746_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_1754_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1748_ = v_opts_941_;
v_isShared_1749_ = v_isSharedCheck_1754_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_errorOnKinds_1744_);
lean_inc(v_bcFileName_x3f_1742_);
lean_inc(v_cFileName_x3f_1741_);
lean_inc(v_ileanFileName_x3f_1740_);
lean_inc(v_oleanFileName_x3f_1739_);
lean_inc(v_setupFileName_x3f_1738_);
lean_inc(v_rootDir_x3f_1737_);
lean_inc(v_opts_1734_);
lean_inc(v_forwardedArgs_1727_);
lean_inc(v_leanOpts_1726_);
lean_dec(v_opts_941_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1754_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_leanOpts_1726_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v_forwardedArgs_1727_);
lean_ctor_set(v_reuseFailAlloc_1753_, 2, v_opts_1734_);
lean_ctor_set(v_reuseFailAlloc_1753_, 3, v_rootDir_x3f_1737_);
lean_ctor_set(v_reuseFailAlloc_1753_, 4, v_setupFileName_x3f_1738_);
lean_ctor_set(v_reuseFailAlloc_1753_, 5, v_oleanFileName_x3f_1739_);
lean_ctor_set(v_reuseFailAlloc_1753_, 6, v_ileanFileName_x3f_1740_);
lean_ctor_set(v_reuseFailAlloc_1753_, 7, v_cFileName_x3f_1741_);
lean_ctor_set(v_reuseFailAlloc_1753_, 8, v_bcFileName_x3f_1742_);
lean_ctor_set(v_reuseFailAlloc_1753_, 9, v_errorOnKinds_1744_);
lean_ctor_set_uint8(v_reuseFailAlloc_1753_, sizeof(void*)*10 + 8, v_component_1728_);
lean_ctor_set_uint8(v_reuseFailAlloc_1753_, sizeof(void*)*10 + 9, v_printPrefix_1729_);
lean_ctor_set_uint8(v_reuseFailAlloc_1753_, sizeof(void*)*10 + 10, v_printLibDir_1730_);
lean_ctor_set_uint8(v_reuseFailAlloc_1753_, sizeof(void*)*10 + 11, v_useStdin_1731_);
lean_ctor_set_uint8(v_reuseFailAlloc_1753_, sizeof(void*)*10 + 12, v_onlyDeps_1732_);
lean_ctor_set_uint8(v_reuseFailAlloc_1753_, sizeof(void*)*10 + 14, v_depsJson_1733_);
lean_ctor_set_uint32(v_reuseFailAlloc_1753_, sizeof(void*)*10, v_trustLevel_1735_);
lean_ctor_set_uint32(v_reuseFailAlloc_1753_, sizeof(void*)*10 + 4, v_numThreads_1736_);
lean_ctor_set_uint8(v_reuseFailAlloc_1753_, sizeof(void*)*10 + 15, v_jsonOutput_1743_);
lean_ctor_set_uint8(v_reuseFailAlloc_1753_, sizeof(void*)*10 + 16, v_printStats_1745_);
lean_ctor_set_uint8(v_reuseFailAlloc_1753_, sizeof(void*)*10 + 17, v_run_1746_);
v___x_1751_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
lean_object* v___x_1752_; 
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*10 + 13, v___x_1182_);
v___x_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
return v___x_1752_;
}
}
}
}
else
{
lean_object* v_leanOpts_1755_; lean_object* v_forwardedArgs_1756_; uint8_t v_component_1757_; uint8_t v_printPrefix_1758_; uint8_t v_printLibDir_1759_; uint8_t v_useStdin_1760_; uint8_t v_onlySrcDeps_1761_; uint8_t v_depsJson_1762_; lean_object* v_opts_1763_; uint32_t v_trustLevel_1764_; uint32_t v_numThreads_1765_; lean_object* v_rootDir_x3f_1766_; lean_object* v_setupFileName_x3f_1767_; lean_object* v_oleanFileName_x3f_1768_; lean_object* v_ileanFileName_x3f_1769_; lean_object* v_cFileName_x3f_1770_; lean_object* v_bcFileName_x3f_1771_; uint8_t v_jsonOutput_1772_; lean_object* v_errorOnKinds_1773_; uint8_t v_printStats_1774_; uint8_t v_run_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1783_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_1755_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1756_ = lean_ctor_get(v_opts_941_, 1);
v_component_1757_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_1758_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_1759_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_1760_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlySrcDeps_1761_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_1762_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_1763_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1764_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_1765_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1766_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1767_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1768_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1769_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1770_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1771_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1772_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_1773_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1774_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_1775_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_1783_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1777_ = v_opts_941_;
v_isShared_1778_ = v_isSharedCheck_1783_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_errorOnKinds_1773_);
lean_inc(v_bcFileName_x3f_1771_);
lean_inc(v_cFileName_x3f_1770_);
lean_inc(v_ileanFileName_x3f_1769_);
lean_inc(v_oleanFileName_x3f_1768_);
lean_inc(v_setupFileName_x3f_1767_);
lean_inc(v_rootDir_x3f_1766_);
lean_inc(v_opts_1763_);
lean_inc(v_forwardedArgs_1756_);
lean_inc(v_leanOpts_1755_);
lean_dec(v_opts_941_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1783_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_leanOpts_1755_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_forwardedArgs_1756_);
lean_ctor_set(v_reuseFailAlloc_1782_, 2, v_opts_1763_);
lean_ctor_set(v_reuseFailAlloc_1782_, 3, v_rootDir_x3f_1766_);
lean_ctor_set(v_reuseFailAlloc_1782_, 4, v_setupFileName_x3f_1767_);
lean_ctor_set(v_reuseFailAlloc_1782_, 5, v_oleanFileName_x3f_1768_);
lean_ctor_set(v_reuseFailAlloc_1782_, 6, v_ileanFileName_x3f_1769_);
lean_ctor_set(v_reuseFailAlloc_1782_, 7, v_cFileName_x3f_1770_);
lean_ctor_set(v_reuseFailAlloc_1782_, 8, v_bcFileName_x3f_1771_);
lean_ctor_set(v_reuseFailAlloc_1782_, 9, v_errorOnKinds_1773_);
lean_ctor_set_uint8(v_reuseFailAlloc_1782_, sizeof(void*)*10 + 8, v_component_1757_);
lean_ctor_set_uint8(v_reuseFailAlloc_1782_, sizeof(void*)*10 + 9, v_printPrefix_1758_);
lean_ctor_set_uint8(v_reuseFailAlloc_1782_, sizeof(void*)*10 + 10, v_printLibDir_1759_);
lean_ctor_set_uint8(v_reuseFailAlloc_1782_, sizeof(void*)*10 + 11, v_useStdin_1760_);
lean_ctor_set_uint8(v_reuseFailAlloc_1782_, sizeof(void*)*10 + 13, v_onlySrcDeps_1761_);
lean_ctor_set_uint8(v_reuseFailAlloc_1782_, sizeof(void*)*10 + 14, v_depsJson_1762_);
lean_ctor_set_uint32(v_reuseFailAlloc_1782_, sizeof(void*)*10, v_trustLevel_1764_);
lean_ctor_set_uint32(v_reuseFailAlloc_1782_, sizeof(void*)*10 + 4, v_numThreads_1765_);
lean_ctor_set_uint8(v_reuseFailAlloc_1782_, sizeof(void*)*10 + 15, v_jsonOutput_1772_);
lean_ctor_set_uint8(v_reuseFailAlloc_1782_, sizeof(void*)*10 + 16, v_printStats_1774_);
lean_ctor_set_uint8(v_reuseFailAlloc_1782_, sizeof(void*)*10 + 17, v_run_1775_);
v___x_1780_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
lean_object* v___x_1781_; 
lean_ctor_set_uint8(v___x_1780_, sizeof(void*)*10 + 12, v___x_1180_);
v___x_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
return v___x_1781_;
}
}
}
}
else
{
lean_object* v_leanOpts_1784_; lean_object* v_forwardedArgs_1785_; uint8_t v_component_1786_; uint8_t v_printPrefix_1787_; uint8_t v_printLibDir_1788_; uint8_t v_useStdin_1789_; uint8_t v_onlyDeps_1790_; uint8_t v_onlySrcDeps_1791_; uint8_t v_depsJson_1792_; lean_object* v_opts_1793_; uint32_t v_trustLevel_1794_; uint32_t v_numThreads_1795_; lean_object* v_rootDir_x3f_1796_; lean_object* v_setupFileName_x3f_1797_; lean_object* v_oleanFileName_x3f_1798_; lean_object* v_ileanFileName_x3f_1799_; lean_object* v_cFileName_x3f_1800_; lean_object* v_bcFileName_x3f_1801_; uint8_t v_jsonOutput_1802_; lean_object* v_errorOnKinds_1803_; uint8_t v_printStats_1804_; uint8_t v_run_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1815_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_1784_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1785_ = lean_ctor_get(v_opts_941_, 1);
v_component_1786_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_1787_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_1788_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_1789_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_1790_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1791_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_1792_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_1793_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1794_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_1795_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1796_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1797_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1798_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1799_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1800_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1801_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1802_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_1803_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1804_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_1805_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1807_ = v_opts_941_;
v_isShared_1808_ = v_isSharedCheck_1815_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_errorOnKinds_1803_);
lean_inc(v_bcFileName_x3f_1801_);
lean_inc(v_cFileName_x3f_1800_);
lean_inc(v_ileanFileName_x3f_1799_);
lean_inc(v_oleanFileName_x3f_1798_);
lean_inc(v_setupFileName_x3f_1797_);
lean_inc(v_rootDir_x3f_1796_);
lean_inc(v_opts_1793_);
lean_inc(v_forwardedArgs_1785_);
lean_inc(v_leanOpts_1784_);
lean_dec(v_opts_941_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1815_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1812_; 
v___x_1809_ = l___private_Lean_Shell_0__Lean_verbose;
v___x_1810_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_1784_, v___x_1809_, v___x_1176_);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v___x_1810_);
v___x_1812_ = v___x_1807_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1810_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v_forwardedArgs_1785_);
lean_ctor_set(v_reuseFailAlloc_1814_, 2, v_opts_1793_);
lean_ctor_set(v_reuseFailAlloc_1814_, 3, v_rootDir_x3f_1796_);
lean_ctor_set(v_reuseFailAlloc_1814_, 4, v_setupFileName_x3f_1797_);
lean_ctor_set(v_reuseFailAlloc_1814_, 5, v_oleanFileName_x3f_1798_);
lean_ctor_set(v_reuseFailAlloc_1814_, 6, v_ileanFileName_x3f_1799_);
lean_ctor_set(v_reuseFailAlloc_1814_, 7, v_cFileName_x3f_1800_);
lean_ctor_set(v_reuseFailAlloc_1814_, 8, v_bcFileName_x3f_1801_);
lean_ctor_set(v_reuseFailAlloc_1814_, 9, v_errorOnKinds_1803_);
lean_ctor_set_uint8(v_reuseFailAlloc_1814_, sizeof(void*)*10 + 8, v_component_1786_);
lean_ctor_set_uint8(v_reuseFailAlloc_1814_, sizeof(void*)*10 + 9, v_printPrefix_1787_);
lean_ctor_set_uint8(v_reuseFailAlloc_1814_, sizeof(void*)*10 + 10, v_printLibDir_1788_);
lean_ctor_set_uint8(v_reuseFailAlloc_1814_, sizeof(void*)*10 + 11, v_useStdin_1789_);
lean_ctor_set_uint8(v_reuseFailAlloc_1814_, sizeof(void*)*10 + 12, v_onlyDeps_1790_);
lean_ctor_set_uint8(v_reuseFailAlloc_1814_, sizeof(void*)*10 + 13, v_onlySrcDeps_1791_);
lean_ctor_set_uint8(v_reuseFailAlloc_1814_, sizeof(void*)*10 + 14, v_depsJson_1792_);
lean_ctor_set_uint32(v_reuseFailAlloc_1814_, sizeof(void*)*10, v_trustLevel_1794_);
lean_ctor_set_uint32(v_reuseFailAlloc_1814_, sizeof(void*)*10 + 4, v_numThreads_1795_);
lean_ctor_set_uint8(v_reuseFailAlloc_1814_, sizeof(void*)*10 + 15, v_jsonOutput_1802_);
lean_ctor_set_uint8(v_reuseFailAlloc_1814_, sizeof(void*)*10 + 16, v_printStats_1804_);
lean_ctor_set_uint8(v_reuseFailAlloc_1814_, sizeof(void*)*10 + 17, v_run_1805_);
v___x_1812_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v___x_1813_; 
v___x_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
return v___x_1813_;
}
}
}
}
else
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1816_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10));
v___x_1817_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1816_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1868_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1820_ = v___x_1817_;
v_isShared_1821_ = v_isSharedCheck_1868_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1817_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1868_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1822_ = lean_unsigned_to_nat(0u);
v___x_1823_ = lean_string_utf8_byte_size(v_a_1818_);
lean_inc(v_a_1818_);
v___x_1824_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1824_, 0, v_a_1818_);
lean_ctor_set(v___x_1824_, 1, v___x_1822_);
lean_ctor_set(v___x_1824_, 2, v___x_1823_);
v___x_1825_ = l_String_Slice_toNat_x3f(v___x_1824_);
lean_dec_ref(v___x_1824_);
if (lean_obj_tag(v___x_1825_) == 1)
{
lean_object* v_val_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; 
v_val_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_val_1826_);
lean_dec_ref(v___x_1825_);
v___x_1827_ = lean_cstr_to_nat("4294967296");
v___x_1828_ = lean_nat_dec_lt(v_val_1826_, v___x_1827_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
lean_dec(v_val_1826_);
lean_del_object(v___x_1820_);
lean_dec(v_a_1818_);
lean_dec_ref(v_opts_941_);
v___x_1829_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11));
v___x_1830_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1829_);
lean_dec_ref(v___x_1830_);
goto v___jp_1011_;
}
else
{
lean_object* v_leanOpts_1831_; lean_object* v_forwardedArgs_1832_; uint8_t v_component_1833_; uint8_t v_printPrefix_1834_; uint8_t v_printLibDir_1835_; uint8_t v_useStdin_1836_; uint8_t v_onlyDeps_1837_; uint8_t v_onlySrcDeps_1838_; uint8_t v_depsJson_1839_; lean_object* v_opts_1840_; uint32_t v_numThreads_1841_; lean_object* v_rootDir_x3f_1842_; lean_object* v_setupFileName_x3f_1843_; lean_object* v_oleanFileName_x3f_1844_; lean_object* v_ileanFileName_x3f_1845_; lean_object* v_cFileName_x3f_1846_; lean_object* v_bcFileName_x3f_1847_; uint8_t v_jsonOutput_1848_; lean_object* v_errorOnKinds_1849_; uint8_t v_printStats_1850_; uint8_t v_run_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1865_; 
v_leanOpts_1831_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1832_ = lean_ctor_get(v_opts_941_, 1);
v_component_1833_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_1834_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_1835_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_1836_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_1837_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1838_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_1839_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_1840_ = lean_ctor_get(v_opts_941_, 2);
v_numThreads_1841_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1842_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1843_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1844_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1845_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1846_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1847_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1848_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_1849_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1850_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_1851_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_1865_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1853_ = v_opts_941_;
v_isShared_1854_ = v_isSharedCheck_1865_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_errorOnKinds_1849_);
lean_inc(v_bcFileName_x3f_1847_);
lean_inc(v_cFileName_x3f_1846_);
lean_inc(v_ileanFileName_x3f_1845_);
lean_inc(v_oleanFileName_x3f_1844_);
lean_inc(v_setupFileName_x3f_1843_);
lean_inc(v_rootDir_x3f_1842_);
lean_inc(v_opts_1840_);
lean_inc(v_forwardedArgs_1832_);
lean_inc(v_leanOpts_1831_);
lean_dec(v_opts_941_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1865_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
uint32_t v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1860_; 
v___x_1855_ = lean_uint32_of_nat(v_val_1826_);
lean_dec(v_val_1826_);
v___x_1856_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12));
v___x_1857_ = lean_string_append(v___x_1856_, v_a_1818_);
lean_dec(v_a_1818_);
v___x_1858_ = lean_array_push(v_forwardedArgs_1832_, v___x_1857_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 1, v___x_1858_);
v___x_1860_ = v___x_1853_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_leanOpts_1831_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v___x_1858_);
lean_ctor_set(v_reuseFailAlloc_1864_, 2, v_opts_1840_);
lean_ctor_set(v_reuseFailAlloc_1864_, 3, v_rootDir_x3f_1842_);
lean_ctor_set(v_reuseFailAlloc_1864_, 4, v_setupFileName_x3f_1843_);
lean_ctor_set(v_reuseFailAlloc_1864_, 5, v_oleanFileName_x3f_1844_);
lean_ctor_set(v_reuseFailAlloc_1864_, 6, v_ileanFileName_x3f_1845_);
lean_ctor_set(v_reuseFailAlloc_1864_, 7, v_cFileName_x3f_1846_);
lean_ctor_set(v_reuseFailAlloc_1864_, 8, v_bcFileName_x3f_1847_);
lean_ctor_set(v_reuseFailAlloc_1864_, 9, v_errorOnKinds_1849_);
lean_ctor_set_uint8(v_reuseFailAlloc_1864_, sizeof(void*)*10 + 8, v_component_1833_);
lean_ctor_set_uint8(v_reuseFailAlloc_1864_, sizeof(void*)*10 + 9, v_printPrefix_1834_);
lean_ctor_set_uint8(v_reuseFailAlloc_1864_, sizeof(void*)*10 + 10, v_printLibDir_1835_);
lean_ctor_set_uint8(v_reuseFailAlloc_1864_, sizeof(void*)*10 + 11, v_useStdin_1836_);
lean_ctor_set_uint8(v_reuseFailAlloc_1864_, sizeof(void*)*10 + 12, v_onlyDeps_1837_);
lean_ctor_set_uint8(v_reuseFailAlloc_1864_, sizeof(void*)*10 + 13, v_onlySrcDeps_1838_);
lean_ctor_set_uint8(v_reuseFailAlloc_1864_, sizeof(void*)*10 + 14, v_depsJson_1839_);
lean_ctor_set_uint32(v_reuseFailAlloc_1864_, sizeof(void*)*10 + 4, v_numThreads_1841_);
lean_ctor_set_uint8(v_reuseFailAlloc_1864_, sizeof(void*)*10 + 15, v_jsonOutput_1848_);
lean_ctor_set_uint8(v_reuseFailAlloc_1864_, sizeof(void*)*10 + 16, v_printStats_1850_);
lean_ctor_set_uint8(v_reuseFailAlloc_1864_, sizeof(void*)*10 + 17, v_run_1851_);
v___x_1860_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
lean_object* v___x_1862_; 
lean_ctor_set_uint32(v___x_1860_, sizeof(void*)*10, v___x_1855_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1860_);
v___x_1862_ = v___x_1820_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1860_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
}
else
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
lean_dec(v___x_1825_);
lean_del_object(v___x_1820_);
lean_dec(v_a_1818_);
lean_dec_ref(v_opts_941_);
v___x_1866_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13));
v___x_1867_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1866_);
lean_dec_ref(v___x_1867_);
goto v___jp_1008_;
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
lean_dec_ref(v_opts_941_);
v_a_1869_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_a_1869_);
lean_dec_ref(v___x_1817_);
v___x_1873_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1874_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1873_);
lean_dec_ref(v___x_1874_);
goto v___jp_1870_;
v___jp_1870_:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = lean_io_error_to_string(v_a_1869_);
v___x_1872_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1871_);
lean_dec_ref(v___x_1872_);
goto v___jp_1005_;
}
}
}
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14));
v___x_1876_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1875_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1925_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1879_ = v___x_1876_;
v_isShared_1880_ = v_isSharedCheck_1925_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1925_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1881_ = lean_unsigned_to_nat(0u);
v___x_1882_ = lean_string_utf8_byte_size(v_a_1877_);
lean_inc(v_a_1877_);
v___x_1883_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1883_, 0, v_a_1877_);
lean_ctor_set(v___x_1883_, 1, v___x_1881_);
lean_ctor_set(v___x_1883_, 2, v___x_1882_);
v___x_1884_ = l_String_Slice_toNat_x3f(v___x_1883_);
lean_dec_ref(v___x_1883_);
if (lean_obj_tag(v___x_1884_) == 1)
{
lean_object* v_val_1885_; lean_object* v_leanOpts_1886_; lean_object* v_forwardedArgs_1887_; uint8_t v_component_1888_; uint8_t v_printPrefix_1889_; uint8_t v_printLibDir_1890_; uint8_t v_useStdin_1891_; uint8_t v_onlyDeps_1892_; uint8_t v_onlySrcDeps_1893_; uint8_t v_depsJson_1894_; lean_object* v_opts_1895_; uint32_t v_trustLevel_1896_; uint32_t v_numThreads_1897_; lean_object* v_rootDir_x3f_1898_; lean_object* v_setupFileName_x3f_1899_; lean_object* v_oleanFileName_x3f_1900_; lean_object* v_ileanFileName_x3f_1901_; lean_object* v_cFileName_x3f_1902_; lean_object* v_bcFileName_x3f_1903_; uint8_t v_jsonOutput_1904_; lean_object* v_errorOnKinds_1905_; uint8_t v_printStats_1906_; uint8_t v_run_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1922_; 
v_val_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_val_1885_);
lean_dec_ref(v___x_1884_);
v_leanOpts_1886_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1887_ = lean_ctor_get(v_opts_941_, 1);
v_component_1888_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_1889_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_1890_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_1891_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_1892_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1893_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_1894_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_1895_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1896_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_1897_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1898_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1899_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1900_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1901_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1902_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1903_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1904_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_1905_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1906_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_1907_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1909_ = v_opts_941_;
v_isShared_1910_ = v_isSharedCheck_1922_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_errorOnKinds_1905_);
lean_inc(v_bcFileName_x3f_1903_);
lean_inc(v_cFileName_x3f_1902_);
lean_inc(v_ileanFileName_x3f_1901_);
lean_inc(v_oleanFileName_x3f_1900_);
lean_inc(v_setupFileName_x3f_1899_);
lean_inc(v_rootDir_x3f_1898_);
lean_inc(v_opts_1895_);
lean_inc(v_forwardedArgs_1887_);
lean_inc(v_leanOpts_1886_);
lean_dec(v_opts_941_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1922_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1917_; 
v___x_1911_ = l___private_Lean_Shell_0__Lean_timeout;
v___x_1912_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_1886_, v___x_1911_, v_val_1885_);
v___x_1913_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15));
v___x_1914_ = lean_string_append(v___x_1913_, v_a_1877_);
lean_dec(v_a_1877_);
v___x_1915_ = lean_array_push(v_forwardedArgs_1887_, v___x_1914_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 1, v___x_1915_);
lean_ctor_set(v___x_1909_, 0, v___x_1912_);
v___x_1917_ = v___x_1909_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1912_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v___x_1915_);
lean_ctor_set(v_reuseFailAlloc_1921_, 2, v_opts_1895_);
lean_ctor_set(v_reuseFailAlloc_1921_, 3, v_rootDir_x3f_1898_);
lean_ctor_set(v_reuseFailAlloc_1921_, 4, v_setupFileName_x3f_1899_);
lean_ctor_set(v_reuseFailAlloc_1921_, 5, v_oleanFileName_x3f_1900_);
lean_ctor_set(v_reuseFailAlloc_1921_, 6, v_ileanFileName_x3f_1901_);
lean_ctor_set(v_reuseFailAlloc_1921_, 7, v_cFileName_x3f_1902_);
lean_ctor_set(v_reuseFailAlloc_1921_, 8, v_bcFileName_x3f_1903_);
lean_ctor_set(v_reuseFailAlloc_1921_, 9, v_errorOnKinds_1905_);
lean_ctor_set_uint8(v_reuseFailAlloc_1921_, sizeof(void*)*10 + 8, v_component_1888_);
lean_ctor_set_uint8(v_reuseFailAlloc_1921_, sizeof(void*)*10 + 9, v_printPrefix_1889_);
lean_ctor_set_uint8(v_reuseFailAlloc_1921_, sizeof(void*)*10 + 10, v_printLibDir_1890_);
lean_ctor_set_uint8(v_reuseFailAlloc_1921_, sizeof(void*)*10 + 11, v_useStdin_1891_);
lean_ctor_set_uint8(v_reuseFailAlloc_1921_, sizeof(void*)*10 + 12, v_onlyDeps_1892_);
lean_ctor_set_uint8(v_reuseFailAlloc_1921_, sizeof(void*)*10 + 13, v_onlySrcDeps_1893_);
lean_ctor_set_uint8(v_reuseFailAlloc_1921_, sizeof(void*)*10 + 14, v_depsJson_1894_);
lean_ctor_set_uint32(v_reuseFailAlloc_1921_, sizeof(void*)*10, v_trustLevel_1896_);
lean_ctor_set_uint32(v_reuseFailAlloc_1921_, sizeof(void*)*10 + 4, v_numThreads_1897_);
lean_ctor_set_uint8(v_reuseFailAlloc_1921_, sizeof(void*)*10 + 15, v_jsonOutput_1904_);
lean_ctor_set_uint8(v_reuseFailAlloc_1921_, sizeof(void*)*10 + 16, v_printStats_1906_);
lean_ctor_set_uint8(v_reuseFailAlloc_1921_, sizeof(void*)*10 + 17, v_run_1907_);
v___x_1917_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
lean_object* v___x_1919_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v___x_1917_);
v___x_1919_ = v___x_1879_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1917_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
else
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
lean_dec(v___x_1884_);
lean_del_object(v___x_1879_);
lean_dec(v_a_1877_);
lean_dec_ref(v_opts_941_);
v___x_1923_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16));
v___x_1924_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1923_);
lean_dec_ref(v___x_1924_);
goto v___jp_1096_;
}
}
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
lean_dec_ref(v_opts_941_);
v_a_1926_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1926_);
lean_dec_ref(v___x_1876_);
v___x_1930_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1931_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1930_);
lean_dec_ref(v___x_1931_);
goto v___jp_1927_;
v___jp_1927_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_io_error_to_string(v_a_1926_);
v___x_1929_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1928_);
lean_dec_ref(v___x_1929_);
goto v___jp_1102_;
}
}
}
}
else
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17));
v___x_1933_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1932_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1982_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1936_ = v___x_1933_;
v_isShared_1937_ = v_isSharedCheck_1982_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1982_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1938_ = lean_unsigned_to_nat(0u);
v___x_1939_ = lean_string_utf8_byte_size(v_a_1934_);
lean_inc(v_a_1934_);
v___x_1940_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1940_, 0, v_a_1934_);
lean_ctor_set(v___x_1940_, 1, v___x_1938_);
lean_ctor_set(v___x_1940_, 2, v___x_1939_);
v___x_1941_ = l_String_Slice_toNat_x3f(v___x_1940_);
lean_dec_ref(v___x_1940_);
if (lean_obj_tag(v___x_1941_) == 1)
{
lean_object* v_val_1942_; lean_object* v_leanOpts_1943_; lean_object* v_forwardedArgs_1944_; uint8_t v_component_1945_; uint8_t v_printPrefix_1946_; uint8_t v_printLibDir_1947_; uint8_t v_useStdin_1948_; uint8_t v_onlyDeps_1949_; uint8_t v_onlySrcDeps_1950_; uint8_t v_depsJson_1951_; lean_object* v_opts_1952_; uint32_t v_trustLevel_1953_; uint32_t v_numThreads_1954_; lean_object* v_rootDir_x3f_1955_; lean_object* v_setupFileName_x3f_1956_; lean_object* v_oleanFileName_x3f_1957_; lean_object* v_ileanFileName_x3f_1958_; lean_object* v_cFileName_x3f_1959_; lean_object* v_bcFileName_x3f_1960_; uint8_t v_jsonOutput_1961_; lean_object* v_errorOnKinds_1962_; uint8_t v_printStats_1963_; uint8_t v_run_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1979_; 
v_val_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_val_1942_);
lean_dec_ref(v___x_1941_);
v_leanOpts_1943_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1944_ = lean_ctor_get(v_opts_941_, 1);
v_component_1945_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_1946_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_1947_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_1948_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_1949_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1950_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_1951_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_1952_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1953_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_1954_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1955_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1956_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1957_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1958_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1959_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1960_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1961_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_1962_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1963_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_1964_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_1979_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1966_ = v_opts_941_;
v_isShared_1967_ = v_isSharedCheck_1979_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_errorOnKinds_1962_);
lean_inc(v_bcFileName_x3f_1960_);
lean_inc(v_cFileName_x3f_1959_);
lean_inc(v_ileanFileName_x3f_1958_);
lean_inc(v_oleanFileName_x3f_1957_);
lean_inc(v_setupFileName_x3f_1956_);
lean_inc(v_rootDir_x3f_1955_);
lean_inc(v_opts_1952_);
lean_inc(v_forwardedArgs_1944_);
lean_inc(v_leanOpts_1943_);
lean_dec(v_opts_941_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1979_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1974_; 
v___x_1968_ = l___private_Lean_Shell_0__Lean_maxMemory;
v___x_1969_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_1943_, v___x_1968_, v_val_1942_);
v___x_1970_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18));
v___x_1971_ = lean_string_append(v___x_1970_, v_a_1934_);
lean_dec(v_a_1934_);
v___x_1972_ = lean_array_push(v_forwardedArgs_1944_, v___x_1971_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 1, v___x_1972_);
lean_ctor_set(v___x_1966_, 0, v___x_1969_);
v___x_1974_ = v___x_1966_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1969_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v___x_1972_);
lean_ctor_set(v_reuseFailAlloc_1978_, 2, v_opts_1952_);
lean_ctor_set(v_reuseFailAlloc_1978_, 3, v_rootDir_x3f_1955_);
lean_ctor_set(v_reuseFailAlloc_1978_, 4, v_setupFileName_x3f_1956_);
lean_ctor_set(v_reuseFailAlloc_1978_, 5, v_oleanFileName_x3f_1957_);
lean_ctor_set(v_reuseFailAlloc_1978_, 6, v_ileanFileName_x3f_1958_);
lean_ctor_set(v_reuseFailAlloc_1978_, 7, v_cFileName_x3f_1959_);
lean_ctor_set(v_reuseFailAlloc_1978_, 8, v_bcFileName_x3f_1960_);
lean_ctor_set(v_reuseFailAlloc_1978_, 9, v_errorOnKinds_1962_);
lean_ctor_set_uint8(v_reuseFailAlloc_1978_, sizeof(void*)*10 + 8, v_component_1945_);
lean_ctor_set_uint8(v_reuseFailAlloc_1978_, sizeof(void*)*10 + 9, v_printPrefix_1946_);
lean_ctor_set_uint8(v_reuseFailAlloc_1978_, sizeof(void*)*10 + 10, v_printLibDir_1947_);
lean_ctor_set_uint8(v_reuseFailAlloc_1978_, sizeof(void*)*10 + 11, v_useStdin_1948_);
lean_ctor_set_uint8(v_reuseFailAlloc_1978_, sizeof(void*)*10 + 12, v_onlyDeps_1949_);
lean_ctor_set_uint8(v_reuseFailAlloc_1978_, sizeof(void*)*10 + 13, v_onlySrcDeps_1950_);
lean_ctor_set_uint8(v_reuseFailAlloc_1978_, sizeof(void*)*10 + 14, v_depsJson_1951_);
lean_ctor_set_uint32(v_reuseFailAlloc_1978_, sizeof(void*)*10, v_trustLevel_1953_);
lean_ctor_set_uint32(v_reuseFailAlloc_1978_, sizeof(void*)*10 + 4, v_numThreads_1954_);
lean_ctor_set_uint8(v_reuseFailAlloc_1978_, sizeof(void*)*10 + 15, v_jsonOutput_1961_);
lean_ctor_set_uint8(v_reuseFailAlloc_1978_, sizeof(void*)*10 + 16, v_printStats_1963_);
lean_ctor_set_uint8(v_reuseFailAlloc_1978_, sizeof(void*)*10 + 17, v_run_1964_);
v___x_1974_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
lean_object* v___x_1976_; 
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v___x_1974_);
v___x_1976_ = v___x_1936_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1974_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
else
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
lean_dec(v___x_1941_);
lean_del_object(v___x_1936_);
lean_dec(v_a_1934_);
lean_dec_ref(v_opts_941_);
v___x_1980_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19));
v___x_1981_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1980_);
lean_dec_ref(v___x_1981_);
goto v___jp_999_;
}
}
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
lean_dec_ref(v_opts_941_);
v_a_1983_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1983_);
lean_dec_ref(v___x_1933_);
v___x_1987_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1988_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1987_);
lean_dec_ref(v___x_1988_);
goto v___jp_1984_;
v___jp_1984_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = lean_io_error_to_string(v_a_1983_);
v___x_1986_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1985_);
lean_dec_ref(v___x_1986_);
goto v___jp_996_;
}
}
}
}
else
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20));
v___x_1990_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1989_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2031_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_1993_ = v___x_1990_;
v_isShared_1994_ = v_isSharedCheck_2031_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2031_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v_leanOpts_1995_; lean_object* v_forwardedArgs_1996_; uint8_t v_component_1997_; uint8_t v_printPrefix_1998_; uint8_t v_printLibDir_1999_; uint8_t v_useStdin_2000_; uint8_t v_onlyDeps_2001_; uint8_t v_onlySrcDeps_2002_; uint8_t v_depsJson_2003_; lean_object* v_opts_2004_; uint32_t v_trustLevel_2005_; uint32_t v_numThreads_2006_; lean_object* v_setupFileName_x3f_2007_; lean_object* v_oleanFileName_x3f_2008_; lean_object* v_ileanFileName_x3f_2009_; lean_object* v_cFileName_x3f_2010_; lean_object* v_bcFileName_x3f_2011_; uint8_t v_jsonOutput_2012_; lean_object* v_errorOnKinds_2013_; uint8_t v_printStats_2014_; uint8_t v_run_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2029_; 
v_leanOpts_1995_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1996_ = lean_ctor_get(v_opts_941_, 1);
v_component_1997_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_1998_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_1999_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_2000_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_2001_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2002_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_2003_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_2004_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_2005_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_2006_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_setupFileName_x3f_2007_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_2008_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_2009_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_2010_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_2011_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_2012_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_2013_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_2014_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_2015_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_2029_ == 0)
{
lean_object* v_unused_2030_; 
v_unused_2030_ = lean_ctor_get(v_opts_941_, 3);
lean_dec(v_unused_2030_);
v___x_2017_ = v_opts_941_;
v_isShared_2018_ = v_isSharedCheck_2029_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_errorOnKinds_2013_);
lean_inc(v_bcFileName_x3f_2011_);
lean_inc(v_cFileName_x3f_2010_);
lean_inc(v_ileanFileName_x3f_2009_);
lean_inc(v_oleanFileName_x3f_2008_);
lean_inc(v_setupFileName_x3f_2007_);
lean_inc(v_opts_2004_);
lean_inc(v_forwardedArgs_1996_);
lean_inc(v_leanOpts_1995_);
lean_dec(v_opts_941_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2029_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2024_; 
v___x_2019_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21));
v___x_2020_ = lean_string_append(v___x_2019_, v_a_1991_);
v___x_2021_ = lean_array_push(v_forwardedArgs_1996_, v___x_2020_);
v___x_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2022_, 0, v_a_1991_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 3, v___x_2022_);
lean_ctor_set(v___x_2017_, 1, v___x_2021_);
v___x_2024_ = v___x_2017_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_leanOpts_1995_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v___x_2021_);
lean_ctor_set(v_reuseFailAlloc_2028_, 2, v_opts_2004_);
lean_ctor_set(v_reuseFailAlloc_2028_, 3, v___x_2022_);
lean_ctor_set(v_reuseFailAlloc_2028_, 4, v_setupFileName_x3f_2007_);
lean_ctor_set(v_reuseFailAlloc_2028_, 5, v_oleanFileName_x3f_2008_);
lean_ctor_set(v_reuseFailAlloc_2028_, 6, v_ileanFileName_x3f_2009_);
lean_ctor_set(v_reuseFailAlloc_2028_, 7, v_cFileName_x3f_2010_);
lean_ctor_set(v_reuseFailAlloc_2028_, 8, v_bcFileName_x3f_2011_);
lean_ctor_set(v_reuseFailAlloc_2028_, 9, v_errorOnKinds_2013_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, sizeof(void*)*10 + 8, v_component_1997_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, sizeof(void*)*10 + 9, v_printPrefix_1998_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, sizeof(void*)*10 + 10, v_printLibDir_1999_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, sizeof(void*)*10 + 11, v_useStdin_2000_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, sizeof(void*)*10 + 12, v_onlyDeps_2001_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, sizeof(void*)*10 + 13, v_onlySrcDeps_2002_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, sizeof(void*)*10 + 14, v_depsJson_2003_);
lean_ctor_set_uint32(v_reuseFailAlloc_2028_, sizeof(void*)*10, v_trustLevel_2005_);
lean_ctor_set_uint32(v_reuseFailAlloc_2028_, sizeof(void*)*10 + 4, v_numThreads_2006_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, sizeof(void*)*10 + 15, v_jsonOutput_2012_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, sizeof(void*)*10 + 16, v_printStats_2014_);
lean_ctor_set_uint8(v_reuseFailAlloc_2028_, sizeof(void*)*10 + 17, v_run_2015_);
v___x_2024_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
lean_object* v___x_2026_; 
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_2024_);
v___x_2026_ = v___x_1993_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
lean_dec_ref(v_opts_941_);
v_a_2032_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_2032_);
lean_dec_ref(v___x_1990_);
v___x_2036_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2037_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2036_);
lean_dec_ref(v___x_2037_);
goto v___jp_2033_;
v___jp_2033_:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = lean_io_error_to_string(v_a_2032_);
v___x_2035_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2034_);
lean_dec_ref(v___x_2035_);
goto v___jp_1108_;
}
}
}
}
else
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22));
v___x_2039_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2038_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2077_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2077_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2077_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v_leanOpts_2044_; lean_object* v_forwardedArgs_2045_; uint8_t v_component_2046_; uint8_t v_printPrefix_2047_; uint8_t v_printLibDir_2048_; uint8_t v_useStdin_2049_; uint8_t v_onlyDeps_2050_; uint8_t v_onlySrcDeps_2051_; uint8_t v_depsJson_2052_; lean_object* v_opts_2053_; uint32_t v_trustLevel_2054_; uint32_t v_numThreads_2055_; lean_object* v_rootDir_x3f_2056_; lean_object* v_setupFileName_x3f_2057_; lean_object* v_oleanFileName_x3f_2058_; lean_object* v_cFileName_x3f_2059_; lean_object* v_bcFileName_x3f_2060_; uint8_t v_jsonOutput_2061_; lean_object* v_errorOnKinds_2062_; uint8_t v_printStats_2063_; uint8_t v_run_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2075_; 
v_leanOpts_2044_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_2045_ = lean_ctor_get(v_opts_941_, 1);
v_component_2046_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_2047_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_2048_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_2049_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_2050_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2051_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_2052_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_2053_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_2054_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_2055_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2056_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_2057_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_2058_ = lean_ctor_get(v_opts_941_, 5);
v_cFileName_x3f_2059_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_2060_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_2061_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_2062_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_2063_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_2064_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_2075_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_2075_ == 0)
{
lean_object* v_unused_2076_; 
v_unused_2076_ = lean_ctor_get(v_opts_941_, 6);
lean_dec(v_unused_2076_);
v___x_2066_ = v_opts_941_;
v_isShared_2067_ = v_isSharedCheck_2075_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_errorOnKinds_2062_);
lean_inc(v_bcFileName_x3f_2060_);
lean_inc(v_cFileName_x3f_2059_);
lean_inc(v_oleanFileName_x3f_2058_);
lean_inc(v_setupFileName_x3f_2057_);
lean_inc(v_rootDir_x3f_2056_);
lean_inc(v_opts_2053_);
lean_inc(v_forwardedArgs_2045_);
lean_inc(v_leanOpts_2044_);
lean_dec(v_opts_941_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2075_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; lean_object* v___x_2070_; 
v___x_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2068_, 0, v_a_2040_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 6, v___x_2068_);
v___x_2070_ = v___x_2066_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_leanOpts_2044_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_forwardedArgs_2045_);
lean_ctor_set(v_reuseFailAlloc_2074_, 2, v_opts_2053_);
lean_ctor_set(v_reuseFailAlloc_2074_, 3, v_rootDir_x3f_2056_);
lean_ctor_set(v_reuseFailAlloc_2074_, 4, v_setupFileName_x3f_2057_);
lean_ctor_set(v_reuseFailAlloc_2074_, 5, v_oleanFileName_x3f_2058_);
lean_ctor_set(v_reuseFailAlloc_2074_, 6, v___x_2068_);
lean_ctor_set(v_reuseFailAlloc_2074_, 7, v_cFileName_x3f_2059_);
lean_ctor_set(v_reuseFailAlloc_2074_, 8, v_bcFileName_x3f_2060_);
lean_ctor_set(v_reuseFailAlloc_2074_, 9, v_errorOnKinds_2062_);
lean_ctor_set_uint8(v_reuseFailAlloc_2074_, sizeof(void*)*10 + 8, v_component_2046_);
lean_ctor_set_uint8(v_reuseFailAlloc_2074_, sizeof(void*)*10 + 9, v_printPrefix_2047_);
lean_ctor_set_uint8(v_reuseFailAlloc_2074_, sizeof(void*)*10 + 10, v_printLibDir_2048_);
lean_ctor_set_uint8(v_reuseFailAlloc_2074_, sizeof(void*)*10 + 11, v_useStdin_2049_);
lean_ctor_set_uint8(v_reuseFailAlloc_2074_, sizeof(void*)*10 + 12, v_onlyDeps_2050_);
lean_ctor_set_uint8(v_reuseFailAlloc_2074_, sizeof(void*)*10 + 13, v_onlySrcDeps_2051_);
lean_ctor_set_uint8(v_reuseFailAlloc_2074_, sizeof(void*)*10 + 14, v_depsJson_2052_);
lean_ctor_set_uint32(v_reuseFailAlloc_2074_, sizeof(void*)*10, v_trustLevel_2054_);
lean_ctor_set_uint32(v_reuseFailAlloc_2074_, sizeof(void*)*10 + 4, v_numThreads_2055_);
lean_ctor_set_uint8(v_reuseFailAlloc_2074_, sizeof(void*)*10 + 15, v_jsonOutput_2061_);
lean_ctor_set_uint8(v_reuseFailAlloc_2074_, sizeof(void*)*10 + 16, v_printStats_2063_);
lean_ctor_set_uint8(v_reuseFailAlloc_2074_, sizeof(void*)*10 + 17, v_run_2064_);
v___x_2070_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
lean_object* v___x_2072_; 
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2070_);
v___x_2072_ = v___x_2042_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
lean_dec_ref(v_opts_941_);
v_a_2078_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2078_);
lean_dec_ref(v___x_2039_);
v___x_2082_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2083_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2082_);
lean_dec_ref(v___x_2083_);
goto v___jp_2079_;
v___jp_2079_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2080_ = lean_io_error_to_string(v_a_2078_);
v___x_2081_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2080_);
lean_dec_ref(v___x_2081_);
goto v___jp_990_;
}
}
}
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23));
v___x_2085_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2084_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2123_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2088_ = v___x_2085_;
v_isShared_2089_ = v_isSharedCheck_2123_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2085_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2123_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v_leanOpts_2090_; lean_object* v_forwardedArgs_2091_; uint8_t v_component_2092_; uint8_t v_printPrefix_2093_; uint8_t v_printLibDir_2094_; uint8_t v_useStdin_2095_; uint8_t v_onlyDeps_2096_; uint8_t v_onlySrcDeps_2097_; uint8_t v_depsJson_2098_; lean_object* v_opts_2099_; uint32_t v_trustLevel_2100_; uint32_t v_numThreads_2101_; lean_object* v_rootDir_x3f_2102_; lean_object* v_setupFileName_x3f_2103_; lean_object* v_ileanFileName_x3f_2104_; lean_object* v_cFileName_x3f_2105_; lean_object* v_bcFileName_x3f_2106_; uint8_t v_jsonOutput_2107_; lean_object* v_errorOnKinds_2108_; uint8_t v_printStats_2109_; uint8_t v_run_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2121_; 
v_leanOpts_2090_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_2091_ = lean_ctor_get(v_opts_941_, 1);
v_component_2092_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_2093_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_2094_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_2095_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_2096_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2097_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_2098_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_2099_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_2100_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_2101_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2102_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_2103_ = lean_ctor_get(v_opts_941_, 4);
v_ileanFileName_x3f_2104_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_2105_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_2106_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_2107_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_2108_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_2109_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_2110_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_2121_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_2121_ == 0)
{
lean_object* v_unused_2122_; 
v_unused_2122_ = lean_ctor_get(v_opts_941_, 5);
lean_dec(v_unused_2122_);
v___x_2112_ = v_opts_941_;
v_isShared_2113_ = v_isSharedCheck_2121_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_errorOnKinds_2108_);
lean_inc(v_bcFileName_x3f_2106_);
lean_inc(v_cFileName_x3f_2105_);
lean_inc(v_ileanFileName_x3f_2104_);
lean_inc(v_setupFileName_x3f_2103_);
lean_inc(v_rootDir_x3f_2102_);
lean_inc(v_opts_2099_);
lean_inc(v_forwardedArgs_2091_);
lean_inc(v_leanOpts_2090_);
lean_dec(v_opts_941_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2121_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; lean_object* v___x_2116_; 
v___x_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2114_, 0, v_a_2086_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 5, v___x_2114_);
v___x_2116_ = v___x_2112_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_leanOpts_2090_);
lean_ctor_set(v_reuseFailAlloc_2120_, 1, v_forwardedArgs_2091_);
lean_ctor_set(v_reuseFailAlloc_2120_, 2, v_opts_2099_);
lean_ctor_set(v_reuseFailAlloc_2120_, 3, v_rootDir_x3f_2102_);
lean_ctor_set(v_reuseFailAlloc_2120_, 4, v_setupFileName_x3f_2103_);
lean_ctor_set(v_reuseFailAlloc_2120_, 5, v___x_2114_);
lean_ctor_set(v_reuseFailAlloc_2120_, 6, v_ileanFileName_x3f_2104_);
lean_ctor_set(v_reuseFailAlloc_2120_, 7, v_cFileName_x3f_2105_);
lean_ctor_set(v_reuseFailAlloc_2120_, 8, v_bcFileName_x3f_2106_);
lean_ctor_set(v_reuseFailAlloc_2120_, 9, v_errorOnKinds_2108_);
lean_ctor_set_uint8(v_reuseFailAlloc_2120_, sizeof(void*)*10 + 8, v_component_2092_);
lean_ctor_set_uint8(v_reuseFailAlloc_2120_, sizeof(void*)*10 + 9, v_printPrefix_2093_);
lean_ctor_set_uint8(v_reuseFailAlloc_2120_, sizeof(void*)*10 + 10, v_printLibDir_2094_);
lean_ctor_set_uint8(v_reuseFailAlloc_2120_, sizeof(void*)*10 + 11, v_useStdin_2095_);
lean_ctor_set_uint8(v_reuseFailAlloc_2120_, sizeof(void*)*10 + 12, v_onlyDeps_2096_);
lean_ctor_set_uint8(v_reuseFailAlloc_2120_, sizeof(void*)*10 + 13, v_onlySrcDeps_2097_);
lean_ctor_set_uint8(v_reuseFailAlloc_2120_, sizeof(void*)*10 + 14, v_depsJson_2098_);
lean_ctor_set_uint32(v_reuseFailAlloc_2120_, sizeof(void*)*10, v_trustLevel_2100_);
lean_ctor_set_uint32(v_reuseFailAlloc_2120_, sizeof(void*)*10 + 4, v_numThreads_2101_);
lean_ctor_set_uint8(v_reuseFailAlloc_2120_, sizeof(void*)*10 + 15, v_jsonOutput_2107_);
lean_ctor_set_uint8(v_reuseFailAlloc_2120_, sizeof(void*)*10 + 16, v_printStats_2109_);
lean_ctor_set_uint8(v_reuseFailAlloc_2120_, sizeof(void*)*10 + 17, v_run_2110_);
v___x_2116_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
lean_object* v___x_2118_; 
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v___x_2116_);
v___x_2118_ = v___x_2088_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2116_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
lean_dec_ref(v_opts_941_);
v_a_2124_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2124_);
lean_dec_ref(v___x_2085_);
v___x_2128_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2129_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2128_);
lean_dec_ref(v___x_2129_);
goto v___jp_2125_;
v___jp_2125_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = lean_io_error_to_string(v_a_2124_);
v___x_2127_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2126_);
lean_dec_ref(v___x_2127_);
goto v___jp_1114_;
}
}
}
}
else
{
lean_object* v_leanOpts_2130_; lean_object* v_forwardedArgs_2131_; uint8_t v_component_2132_; uint8_t v_printPrefix_2133_; uint8_t v_printLibDir_2134_; uint8_t v_useStdin_2135_; uint8_t v_onlyDeps_2136_; uint8_t v_onlySrcDeps_2137_; uint8_t v_depsJson_2138_; lean_object* v_opts_2139_; uint32_t v_trustLevel_2140_; uint32_t v_numThreads_2141_; lean_object* v_rootDir_x3f_2142_; lean_object* v_setupFileName_x3f_2143_; lean_object* v_oleanFileName_x3f_2144_; lean_object* v_ileanFileName_x3f_2145_; lean_object* v_cFileName_x3f_2146_; lean_object* v_bcFileName_x3f_2147_; uint8_t v_jsonOutput_2148_; lean_object* v_errorOnKinds_2149_; uint8_t v_printStats_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2158_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_2130_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_2131_ = lean_ctor_get(v_opts_941_, 1);
v_component_2132_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_2133_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_2134_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_2135_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_2136_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2137_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_2138_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_2139_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_2140_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_2141_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2142_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_2143_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_2144_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_2145_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_2146_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_2147_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_2148_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_2149_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_2150_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2152_ = v_opts_941_;
v_isShared_2153_ = v_isSharedCheck_2158_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_errorOnKinds_2149_);
lean_inc(v_bcFileName_x3f_2147_);
lean_inc(v_cFileName_x3f_2146_);
lean_inc(v_ileanFileName_x3f_2145_);
lean_inc(v_oleanFileName_x3f_2144_);
lean_inc(v_setupFileName_x3f_2143_);
lean_inc(v_rootDir_x3f_2142_);
lean_inc(v_opts_2139_);
lean_inc(v_forwardedArgs_2131_);
lean_inc(v_leanOpts_2130_);
lean_dec(v_opts_941_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2158_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_leanOpts_2130_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_forwardedArgs_2131_);
lean_ctor_set(v_reuseFailAlloc_2157_, 2, v_opts_2139_);
lean_ctor_set(v_reuseFailAlloc_2157_, 3, v_rootDir_x3f_2142_);
lean_ctor_set(v_reuseFailAlloc_2157_, 4, v_setupFileName_x3f_2143_);
lean_ctor_set(v_reuseFailAlloc_2157_, 5, v_oleanFileName_x3f_2144_);
lean_ctor_set(v_reuseFailAlloc_2157_, 6, v_ileanFileName_x3f_2145_);
lean_ctor_set(v_reuseFailAlloc_2157_, 7, v_cFileName_x3f_2146_);
lean_ctor_set(v_reuseFailAlloc_2157_, 8, v_bcFileName_x3f_2147_);
lean_ctor_set(v_reuseFailAlloc_2157_, 9, v_errorOnKinds_2149_);
lean_ctor_set_uint8(v_reuseFailAlloc_2157_, sizeof(void*)*10 + 8, v_component_2132_);
lean_ctor_set_uint8(v_reuseFailAlloc_2157_, sizeof(void*)*10 + 9, v_printPrefix_2133_);
lean_ctor_set_uint8(v_reuseFailAlloc_2157_, sizeof(void*)*10 + 10, v_printLibDir_2134_);
lean_ctor_set_uint8(v_reuseFailAlloc_2157_, sizeof(void*)*10 + 11, v_useStdin_2135_);
lean_ctor_set_uint8(v_reuseFailAlloc_2157_, sizeof(void*)*10 + 12, v_onlyDeps_2136_);
lean_ctor_set_uint8(v_reuseFailAlloc_2157_, sizeof(void*)*10 + 13, v_onlySrcDeps_2137_);
lean_ctor_set_uint8(v_reuseFailAlloc_2157_, sizeof(void*)*10 + 14, v_depsJson_2138_);
lean_ctor_set_uint32(v_reuseFailAlloc_2157_, sizeof(void*)*10, v_trustLevel_2140_);
lean_ctor_set_uint32(v_reuseFailAlloc_2157_, sizeof(void*)*10 + 4, v_numThreads_2141_);
lean_ctor_set_uint8(v_reuseFailAlloc_2157_, sizeof(void*)*10 + 15, v_jsonOutput_2148_);
lean_ctor_set_uint8(v_reuseFailAlloc_2157_, sizeof(void*)*10 + 16, v_printStats_2150_);
v___x_2155_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
lean_object* v___x_2156_; 
lean_ctor_set_uint8(v___x_2155_, sizeof(void*)*10 + 17, v___x_1164_);
v___x_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2155_);
return v___x_2156_;
}
}
}
}
else
{
lean_object* v_leanOpts_2159_; lean_object* v_forwardedArgs_2160_; uint8_t v_component_2161_; uint8_t v_printPrefix_2162_; uint8_t v_printLibDir_2163_; uint8_t v_onlyDeps_2164_; uint8_t v_onlySrcDeps_2165_; uint8_t v_depsJson_2166_; lean_object* v_opts_2167_; uint32_t v_trustLevel_2168_; uint32_t v_numThreads_2169_; lean_object* v_rootDir_x3f_2170_; lean_object* v_setupFileName_x3f_2171_; lean_object* v_oleanFileName_x3f_2172_; lean_object* v_ileanFileName_x3f_2173_; lean_object* v_cFileName_x3f_2174_; lean_object* v_bcFileName_x3f_2175_; uint8_t v_jsonOutput_2176_; lean_object* v_errorOnKinds_2177_; uint8_t v_printStats_2178_; uint8_t v_run_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2187_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_2159_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_2160_ = lean_ctor_get(v_opts_941_, 1);
v_component_2161_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_2162_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_2163_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_onlyDeps_2164_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2165_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_2166_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_2167_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_2168_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_2169_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2170_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_2171_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_2172_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_2173_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_2174_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_2175_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_2176_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_2177_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_2178_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_2179_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_2187_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2181_ = v_opts_941_;
v_isShared_2182_ = v_isSharedCheck_2187_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_errorOnKinds_2177_);
lean_inc(v_bcFileName_x3f_2175_);
lean_inc(v_cFileName_x3f_2174_);
lean_inc(v_ileanFileName_x3f_2173_);
lean_inc(v_oleanFileName_x3f_2172_);
lean_inc(v_setupFileName_x3f_2171_);
lean_inc(v_rootDir_x3f_2170_);
lean_inc(v_opts_2167_);
lean_inc(v_forwardedArgs_2160_);
lean_inc(v_leanOpts_2159_);
lean_dec(v_opts_941_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2187_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_leanOpts_2159_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_forwardedArgs_2160_);
lean_ctor_set(v_reuseFailAlloc_2186_, 2, v_opts_2167_);
lean_ctor_set(v_reuseFailAlloc_2186_, 3, v_rootDir_x3f_2170_);
lean_ctor_set(v_reuseFailAlloc_2186_, 4, v_setupFileName_x3f_2171_);
lean_ctor_set(v_reuseFailAlloc_2186_, 5, v_oleanFileName_x3f_2172_);
lean_ctor_set(v_reuseFailAlloc_2186_, 6, v_ileanFileName_x3f_2173_);
lean_ctor_set(v_reuseFailAlloc_2186_, 7, v_cFileName_x3f_2174_);
lean_ctor_set(v_reuseFailAlloc_2186_, 8, v_bcFileName_x3f_2175_);
lean_ctor_set(v_reuseFailAlloc_2186_, 9, v_errorOnKinds_2177_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, sizeof(void*)*10 + 8, v_component_2161_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, sizeof(void*)*10 + 9, v_printPrefix_2162_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, sizeof(void*)*10 + 10, v_printLibDir_2163_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, sizeof(void*)*10 + 12, v_onlyDeps_2164_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, sizeof(void*)*10 + 13, v_onlySrcDeps_2165_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, sizeof(void*)*10 + 14, v_depsJson_2166_);
lean_ctor_set_uint32(v_reuseFailAlloc_2186_, sizeof(void*)*10, v_trustLevel_2168_);
lean_ctor_set_uint32(v_reuseFailAlloc_2186_, sizeof(void*)*10 + 4, v_numThreads_2169_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, sizeof(void*)*10 + 15, v_jsonOutput_2176_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, sizeof(void*)*10 + 16, v_printStats_2178_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, sizeof(void*)*10 + 17, v_run_2179_);
v___x_2184_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2185_; 
lean_ctor_set_uint8(v___x_2184_, sizeof(void*)*10 + 11, v___x_1162_);
v___x_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
return v___x_2185_;
}
}
}
}
else
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24));
v___x_2189_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2188_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2248_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2192_ = v___x_2189_;
v_isShared_2193_ = v_isSharedCheck_2248_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2189_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2248_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2194_ = lean_unsigned_to_nat(0u);
v___x_2195_ = lean_string_utf8_byte_size(v_a_2190_);
lean_inc(v_a_2190_);
v___x_2196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2196_, 0, v_a_2190_);
lean_ctor_set(v___x_2196_, 1, v___x_2194_);
lean_ctor_set(v___x_2196_, 2, v___x_2195_);
v___x_2197_ = l_String_Slice_toNat_x3f(v___x_2196_);
lean_dec_ref(v___x_2196_);
if (lean_obj_tag(v___x_2197_) == 1)
{
lean_object* v_val_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; 
v_val_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_val_2198_);
lean_dec_ref(v___x_2197_);
v___x_2199_ = lean_unsigned_to_nat(4u);
v___x_2200_ = lean_unsigned_to_nat(2u);
v___x_2201_ = lean_nat_shiftr(v_val_2198_, v___x_2200_);
lean_dec(v_val_2198_);
v___x_2202_ = lean_nat_mul(v___x_2201_, v___x_2199_);
lean_dec(v___x_2201_);
v___x_2203_ = lean_unsigned_to_nat(1024u);
v___x_2204_ = lean_nat_mul(v___x_2202_, v___x_2203_);
lean_dec(v___x_2202_);
v___x_2205_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25, &l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25_once, _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25);
v___x_2206_ = lean_nat_dec_lt(v___x_2204_, v___x_2205_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_dec(v___x_2204_);
lean_del_object(v___x_2192_);
lean_dec(v_a_2190_);
lean_dec_ref(v_opts_941_);
v___x_2207_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26));
v___x_2208_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2207_);
lean_dec_ref(v___x_2208_);
goto v___jp_984_;
}
else
{
size_t v___x_2209_; lean_object* v___x_2210_; lean_object* v_leanOpts_2211_; lean_object* v_forwardedArgs_2212_; uint8_t v_component_2213_; uint8_t v_printPrefix_2214_; uint8_t v_printLibDir_2215_; uint8_t v_useStdin_2216_; uint8_t v_onlyDeps_2217_; uint8_t v_onlySrcDeps_2218_; uint8_t v_depsJson_2219_; lean_object* v_opts_2220_; uint32_t v_trustLevel_2221_; uint32_t v_numThreads_2222_; lean_object* v_rootDir_x3f_2223_; lean_object* v_setupFileName_x3f_2224_; lean_object* v_oleanFileName_x3f_2225_; lean_object* v_ileanFileName_x3f_2226_; lean_object* v_cFileName_x3f_2227_; lean_object* v_bcFileName_x3f_2228_; uint8_t v_jsonOutput_2229_; lean_object* v_errorOnKinds_2230_; uint8_t v_printStats_2231_; uint8_t v_run_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2245_; 
v___x_2209_ = lean_usize_of_nat(v___x_2204_);
lean_dec(v___x_2204_);
v___x_2210_ = lean_internal_set_thread_stack_size(v___x_2209_);
v_leanOpts_2211_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_2212_ = lean_ctor_get(v_opts_941_, 1);
v_component_2213_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_2214_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_2215_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_2216_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_2217_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2218_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_2219_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_2220_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_2221_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_2222_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2223_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_2224_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_2225_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_2226_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_2227_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_2228_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_2229_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_2230_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_2231_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_2232_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_2245_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2234_ = v_opts_941_;
v_isShared_2235_ = v_isSharedCheck_2245_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_errorOnKinds_2230_);
lean_inc(v_bcFileName_x3f_2228_);
lean_inc(v_cFileName_x3f_2227_);
lean_inc(v_ileanFileName_x3f_2226_);
lean_inc(v_oleanFileName_x3f_2225_);
lean_inc(v_setupFileName_x3f_2224_);
lean_inc(v_rootDir_x3f_2223_);
lean_inc(v_opts_2220_);
lean_inc(v_forwardedArgs_2212_);
lean_inc(v_leanOpts_2211_);
lean_dec(v_opts_941_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2245_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2240_; 
v___x_2236_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27));
v___x_2237_ = lean_string_append(v___x_2236_, v_a_2190_);
lean_dec(v_a_2190_);
v___x_2238_ = lean_array_push(v_forwardedArgs_2212_, v___x_2237_);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 1, v___x_2238_);
v___x_2240_ = v___x_2234_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_leanOpts_2211_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v___x_2238_);
lean_ctor_set(v_reuseFailAlloc_2244_, 2, v_opts_2220_);
lean_ctor_set(v_reuseFailAlloc_2244_, 3, v_rootDir_x3f_2223_);
lean_ctor_set(v_reuseFailAlloc_2244_, 4, v_setupFileName_x3f_2224_);
lean_ctor_set(v_reuseFailAlloc_2244_, 5, v_oleanFileName_x3f_2225_);
lean_ctor_set(v_reuseFailAlloc_2244_, 6, v_ileanFileName_x3f_2226_);
lean_ctor_set(v_reuseFailAlloc_2244_, 7, v_cFileName_x3f_2227_);
lean_ctor_set(v_reuseFailAlloc_2244_, 8, v_bcFileName_x3f_2228_);
lean_ctor_set(v_reuseFailAlloc_2244_, 9, v_errorOnKinds_2230_);
lean_ctor_set_uint8(v_reuseFailAlloc_2244_, sizeof(void*)*10 + 8, v_component_2213_);
lean_ctor_set_uint8(v_reuseFailAlloc_2244_, sizeof(void*)*10 + 9, v_printPrefix_2214_);
lean_ctor_set_uint8(v_reuseFailAlloc_2244_, sizeof(void*)*10 + 10, v_printLibDir_2215_);
lean_ctor_set_uint8(v_reuseFailAlloc_2244_, sizeof(void*)*10 + 11, v_useStdin_2216_);
lean_ctor_set_uint8(v_reuseFailAlloc_2244_, sizeof(void*)*10 + 12, v_onlyDeps_2217_);
lean_ctor_set_uint8(v_reuseFailAlloc_2244_, sizeof(void*)*10 + 13, v_onlySrcDeps_2218_);
lean_ctor_set_uint8(v_reuseFailAlloc_2244_, sizeof(void*)*10 + 14, v_depsJson_2219_);
lean_ctor_set_uint32(v_reuseFailAlloc_2244_, sizeof(void*)*10, v_trustLevel_2221_);
lean_ctor_set_uint32(v_reuseFailAlloc_2244_, sizeof(void*)*10 + 4, v_numThreads_2222_);
lean_ctor_set_uint8(v_reuseFailAlloc_2244_, sizeof(void*)*10 + 15, v_jsonOutput_2229_);
lean_ctor_set_uint8(v_reuseFailAlloc_2244_, sizeof(void*)*10 + 16, v_printStats_2231_);
lean_ctor_set_uint8(v_reuseFailAlloc_2244_, sizeof(void*)*10 + 17, v_run_2232_);
v___x_2240_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
lean_object* v___x_2242_; 
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v___x_2240_);
v___x_2242_ = v___x_2192_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
}
else
{
lean_object* v___x_2246_; lean_object* v___x_2247_; 
lean_dec(v___x_2197_);
lean_del_object(v___x_2192_);
lean_dec(v_a_2190_);
lean_dec_ref(v_opts_941_);
v___x_2246_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28));
v___x_2247_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2246_);
lean_dec_ref(v___x_2247_);
goto v___jp_981_;
}
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
lean_dec_ref(v_opts_941_);
v_a_2249_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2249_);
lean_dec_ref(v___x_2189_);
v___x_2253_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2254_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2253_);
lean_dec_ref(v___x_2254_);
goto v___jp_2250_;
v___jp_2250_:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2251_ = lean_io_error_to_string(v_a_2249_);
v___x_2252_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2251_);
lean_dec_ref(v___x_2252_);
goto v___jp_978_;
}
}
}
}
else
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29));
v___x_2256_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2255_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2294_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2294_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2294_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v_leanOpts_2261_; lean_object* v_forwardedArgs_2262_; uint8_t v_component_2263_; uint8_t v_printPrefix_2264_; uint8_t v_printLibDir_2265_; uint8_t v_useStdin_2266_; uint8_t v_onlyDeps_2267_; uint8_t v_onlySrcDeps_2268_; uint8_t v_depsJson_2269_; lean_object* v_opts_2270_; uint32_t v_trustLevel_2271_; uint32_t v_numThreads_2272_; lean_object* v_rootDir_x3f_2273_; lean_object* v_setupFileName_x3f_2274_; lean_object* v_oleanFileName_x3f_2275_; lean_object* v_ileanFileName_x3f_2276_; lean_object* v_cFileName_x3f_2277_; uint8_t v_jsonOutput_2278_; lean_object* v_errorOnKinds_2279_; uint8_t v_printStats_2280_; uint8_t v_run_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2292_; 
v_leanOpts_2261_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_2262_ = lean_ctor_get(v_opts_941_, 1);
v_component_2263_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_2264_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_2265_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_2266_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_2267_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2268_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_2269_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_2270_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_2271_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_2272_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2273_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_2274_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_2275_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_2276_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_2277_ = lean_ctor_get(v_opts_941_, 7);
v_jsonOutput_2278_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_2279_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_2280_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_2281_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_2292_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_2292_ == 0)
{
lean_object* v_unused_2293_; 
v_unused_2293_ = lean_ctor_get(v_opts_941_, 8);
lean_dec(v_unused_2293_);
v___x_2283_ = v_opts_941_;
v_isShared_2284_ = v_isSharedCheck_2292_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_errorOnKinds_2279_);
lean_inc(v_cFileName_x3f_2277_);
lean_inc(v_ileanFileName_x3f_2276_);
lean_inc(v_oleanFileName_x3f_2275_);
lean_inc(v_setupFileName_x3f_2274_);
lean_inc(v_rootDir_x3f_2273_);
lean_inc(v_opts_2270_);
lean_inc(v_forwardedArgs_2262_);
lean_inc(v_leanOpts_2261_);
lean_dec(v_opts_941_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2292_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2285_; lean_object* v___x_2287_; 
v___x_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2285_, 0, v_a_2257_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 8, v___x_2285_);
v___x_2287_ = v___x_2283_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_leanOpts_2261_);
lean_ctor_set(v_reuseFailAlloc_2291_, 1, v_forwardedArgs_2262_);
lean_ctor_set(v_reuseFailAlloc_2291_, 2, v_opts_2270_);
lean_ctor_set(v_reuseFailAlloc_2291_, 3, v_rootDir_x3f_2273_);
lean_ctor_set(v_reuseFailAlloc_2291_, 4, v_setupFileName_x3f_2274_);
lean_ctor_set(v_reuseFailAlloc_2291_, 5, v_oleanFileName_x3f_2275_);
lean_ctor_set(v_reuseFailAlloc_2291_, 6, v_ileanFileName_x3f_2276_);
lean_ctor_set(v_reuseFailAlloc_2291_, 7, v_cFileName_x3f_2277_);
lean_ctor_set(v_reuseFailAlloc_2291_, 8, v___x_2285_);
lean_ctor_set(v_reuseFailAlloc_2291_, 9, v_errorOnKinds_2279_);
lean_ctor_set_uint8(v_reuseFailAlloc_2291_, sizeof(void*)*10 + 8, v_component_2263_);
lean_ctor_set_uint8(v_reuseFailAlloc_2291_, sizeof(void*)*10 + 9, v_printPrefix_2264_);
lean_ctor_set_uint8(v_reuseFailAlloc_2291_, sizeof(void*)*10 + 10, v_printLibDir_2265_);
lean_ctor_set_uint8(v_reuseFailAlloc_2291_, sizeof(void*)*10 + 11, v_useStdin_2266_);
lean_ctor_set_uint8(v_reuseFailAlloc_2291_, sizeof(void*)*10 + 12, v_onlyDeps_2267_);
lean_ctor_set_uint8(v_reuseFailAlloc_2291_, sizeof(void*)*10 + 13, v_onlySrcDeps_2268_);
lean_ctor_set_uint8(v_reuseFailAlloc_2291_, sizeof(void*)*10 + 14, v_depsJson_2269_);
lean_ctor_set_uint32(v_reuseFailAlloc_2291_, sizeof(void*)*10, v_trustLevel_2271_);
lean_ctor_set_uint32(v_reuseFailAlloc_2291_, sizeof(void*)*10 + 4, v_numThreads_2272_);
lean_ctor_set_uint8(v_reuseFailAlloc_2291_, sizeof(void*)*10 + 15, v_jsonOutput_2278_);
lean_ctor_set_uint8(v_reuseFailAlloc_2291_, sizeof(void*)*10 + 16, v_printStats_2280_);
lean_ctor_set_uint8(v_reuseFailAlloc_2291_, sizeof(void*)*10 + 17, v_run_2281_);
v___x_2287_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
lean_object* v___x_2289_; 
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v___x_2287_);
v___x_2289_ = v___x_2259_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2287_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
}
else
{
lean_object* v_a_2295_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
lean_dec_ref(v_opts_941_);
v_a_2295_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2295_);
lean_dec_ref(v___x_2256_);
v___x_2299_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2300_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2299_);
lean_dec_ref(v___x_2300_);
goto v___jp_2296_;
v___jp_2296_:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2297_ = lean_io_error_to_string(v_a_2295_);
v___x_2298_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2297_);
lean_dec_ref(v___x_2298_);
goto v___jp_1120_;
}
}
}
}
else
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2301_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30));
v___x_2302_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2301_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2340_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2305_ = v___x_2302_;
v_isShared_2306_ = v_isSharedCheck_2340_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2302_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2340_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v_leanOpts_2307_; lean_object* v_forwardedArgs_2308_; uint8_t v_component_2309_; uint8_t v_printPrefix_2310_; uint8_t v_printLibDir_2311_; uint8_t v_useStdin_2312_; uint8_t v_onlyDeps_2313_; uint8_t v_onlySrcDeps_2314_; uint8_t v_depsJson_2315_; lean_object* v_opts_2316_; uint32_t v_trustLevel_2317_; uint32_t v_numThreads_2318_; lean_object* v_rootDir_x3f_2319_; lean_object* v_setupFileName_x3f_2320_; lean_object* v_oleanFileName_x3f_2321_; lean_object* v_ileanFileName_x3f_2322_; lean_object* v_bcFileName_x3f_2323_; uint8_t v_jsonOutput_2324_; lean_object* v_errorOnKinds_2325_; uint8_t v_printStats_2326_; uint8_t v_run_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2338_; 
v_leanOpts_2307_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_2308_ = lean_ctor_get(v_opts_941_, 1);
v_component_2309_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_2310_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_2311_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_2312_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_2313_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2314_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_2315_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_2316_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_2317_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_numThreads_2318_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2319_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_2320_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_2321_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_2322_ = lean_ctor_get(v_opts_941_, 6);
v_bcFileName_x3f_2323_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_2324_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_2325_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_2326_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_2327_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_2338_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_2338_ == 0)
{
lean_object* v_unused_2339_; 
v_unused_2339_ = lean_ctor_get(v_opts_941_, 7);
lean_dec(v_unused_2339_);
v___x_2329_ = v_opts_941_;
v_isShared_2330_ = v_isSharedCheck_2338_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_errorOnKinds_2325_);
lean_inc(v_bcFileName_x3f_2323_);
lean_inc(v_ileanFileName_x3f_2322_);
lean_inc(v_oleanFileName_x3f_2321_);
lean_inc(v_setupFileName_x3f_2320_);
lean_inc(v_rootDir_x3f_2319_);
lean_inc(v_opts_2316_);
lean_inc(v_forwardedArgs_2308_);
lean_inc(v_leanOpts_2307_);
lean_dec(v_opts_941_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2338_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2331_; lean_object* v___x_2333_; 
v___x_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2331_, 0, v_a_2303_);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 7, v___x_2331_);
v___x_2333_ = v___x_2329_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_leanOpts_2307_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v_forwardedArgs_2308_);
lean_ctor_set(v_reuseFailAlloc_2337_, 2, v_opts_2316_);
lean_ctor_set(v_reuseFailAlloc_2337_, 3, v_rootDir_x3f_2319_);
lean_ctor_set(v_reuseFailAlloc_2337_, 4, v_setupFileName_x3f_2320_);
lean_ctor_set(v_reuseFailAlloc_2337_, 5, v_oleanFileName_x3f_2321_);
lean_ctor_set(v_reuseFailAlloc_2337_, 6, v_ileanFileName_x3f_2322_);
lean_ctor_set(v_reuseFailAlloc_2337_, 7, v___x_2331_);
lean_ctor_set(v_reuseFailAlloc_2337_, 8, v_bcFileName_x3f_2323_);
lean_ctor_set(v_reuseFailAlloc_2337_, 9, v_errorOnKinds_2325_);
lean_ctor_set_uint8(v_reuseFailAlloc_2337_, sizeof(void*)*10 + 8, v_component_2309_);
lean_ctor_set_uint8(v_reuseFailAlloc_2337_, sizeof(void*)*10 + 9, v_printPrefix_2310_);
lean_ctor_set_uint8(v_reuseFailAlloc_2337_, sizeof(void*)*10 + 10, v_printLibDir_2311_);
lean_ctor_set_uint8(v_reuseFailAlloc_2337_, sizeof(void*)*10 + 11, v_useStdin_2312_);
lean_ctor_set_uint8(v_reuseFailAlloc_2337_, sizeof(void*)*10 + 12, v_onlyDeps_2313_);
lean_ctor_set_uint8(v_reuseFailAlloc_2337_, sizeof(void*)*10 + 13, v_onlySrcDeps_2314_);
lean_ctor_set_uint8(v_reuseFailAlloc_2337_, sizeof(void*)*10 + 14, v_depsJson_2315_);
lean_ctor_set_uint32(v_reuseFailAlloc_2337_, sizeof(void*)*10, v_trustLevel_2317_);
lean_ctor_set_uint32(v_reuseFailAlloc_2337_, sizeof(void*)*10 + 4, v_numThreads_2318_);
lean_ctor_set_uint8(v_reuseFailAlloc_2337_, sizeof(void*)*10 + 15, v_jsonOutput_2324_);
lean_ctor_set_uint8(v_reuseFailAlloc_2337_, sizeof(void*)*10 + 16, v_printStats_2326_);
lean_ctor_set_uint8(v_reuseFailAlloc_2337_, sizeof(void*)*10 + 17, v_run_2327_);
v___x_2333_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2335_; 
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v___x_2333_);
v___x_2335_ = v___x_2305_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
lean_dec_ref(v_opts_941_);
v_a_2341_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2341_);
lean_dec_ref(v___x_2302_);
v___x_2345_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2346_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2345_);
lean_dec_ref(v___x_2346_);
goto v___jp_2342_;
v___jp_2342_:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = lean_io_error_to_string(v_a_2341_);
v___x_2344_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2343_);
lean_dec_ref(v___x_2344_);
goto v___jp_972_;
}
}
}
}
else
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
lean_dec(v_optArg_x3f_943_);
lean_dec_ref(v_opts_941_);
v___x_2347_ = l___private_Lean_Shell_0__Lean_featuresString;
v___x_2348_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2347_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2356_; 
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2356_ == 0)
{
lean_object* v_unused_2357_; 
v_unused_2357_ = lean_ctor_get(v___x_2348_, 0);
lean_dec(v_unused_2357_);
v___x_2350_ = v___x_2348_;
v_isShared_2351_ = v_isSharedCheck_2356_;
goto v_resetjp_2349_;
}
else
{
lean_dec(v___x_2348_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2356_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2352_; lean_object* v___x_2354_; 
v___x_2352_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2351_ == 0)
{
lean_ctor_set_tag(v___x_2350_, 1);
lean_ctor_set(v___x_2350_, 0, v___x_2352_);
v___x_2354_ = v___x_2350_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2352_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v_a_2358_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2358_);
lean_dec_ref(v___x_2348_);
v___x_2362_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2363_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2362_);
lean_dec_ref(v___x_2363_);
goto v___jp_2359_;
v___jp_2359_:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = lean_io_error_to_string(v_a_2358_);
v___x_2361_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2360_);
lean_dec_ref(v___x_2361_);
goto v___jp_1126_;
}
}
}
}
else
{
lean_object* v___x_2364_; 
lean_dec(v_optArg_x3f_943_);
lean_dec_ref(v_opts_941_);
v___x_2364_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1150_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2372_; 
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2372_ == 0)
{
lean_object* v_unused_2373_; 
v_unused_2373_ = lean_ctor_get(v___x_2364_, 0);
lean_dec(v_unused_2373_);
v___x_2366_ = v___x_2364_;
v_isShared_2367_ = v_isSharedCheck_2372_;
goto v_resetjp_2365_;
}
else
{
lean_dec(v___x_2364_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2372_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; lean_object* v___x_2370_; 
v___x_2368_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2367_ == 0)
{
lean_ctor_set_tag(v___x_2366_, 1);
lean_ctor_set(v___x_2366_, 0, v___x_2368_);
v___x_2370_ = v___x_2366_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2368_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v_a_2374_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_a_2374_);
lean_dec_ref(v___x_2364_);
v___x_2378_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2379_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2378_);
lean_dec_ref(v___x_2379_);
goto v___jp_2375_;
v___jp_2375_:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2376_ = lean_io_error_to_string(v_a_2374_);
v___x_2377_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2376_);
lean_dec_ref(v___x_2377_);
goto v___jp_966_;
}
}
}
}
else
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
lean_dec(v_optArg_x3f_943_);
lean_dec_ref(v_opts_941_);
v___x_2380_ = l_Lean_githash;
v___x_2381_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2380_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2389_; 
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2389_ == 0)
{
lean_object* v_unused_2390_; 
v_unused_2390_ = lean_ctor_get(v___x_2381_, 0);
lean_dec(v_unused_2390_);
v___x_2383_ = v___x_2381_;
v_isShared_2384_ = v_isSharedCheck_2389_;
goto v_resetjp_2382_;
}
else
{
lean_dec(v___x_2381_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2389_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2385_; lean_object* v___x_2387_; 
v___x_2385_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2384_ == 0)
{
lean_ctor_set_tag(v___x_2383_, 1);
lean_ctor_set(v___x_2383_, 0, v___x_2385_);
v___x_2387_ = v___x_2383_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v_a_2391_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_a_2391_);
lean_dec_ref(v___x_2381_);
v___x_2395_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2396_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2395_);
lean_dec_ref(v___x_2396_);
goto v___jp_2392_;
v___jp_2392_:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = lean_io_error_to_string(v_a_2391_);
v___x_2394_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2393_);
lean_dec_ref(v___x_2394_);
goto v___jp_1132_;
}
}
}
}
else
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
lean_dec(v_optArg_x3f_943_);
lean_dec_ref(v_opts_941_);
v___x_2397_ = l___private_Lean_Shell_0__Lean_shortVersionString;
v___x_2398_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2397_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2406_; 
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2406_ == 0)
{
lean_object* v_unused_2407_; 
v_unused_2407_ = lean_ctor_get(v___x_2398_, 0);
lean_dec(v_unused_2407_);
v___x_2400_ = v___x_2398_;
v_isShared_2401_ = v_isSharedCheck_2406_;
goto v_resetjp_2399_;
}
else
{
lean_dec(v___x_2398_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2406_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; lean_object* v___x_2404_; 
v___x_2402_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2401_ == 0)
{
lean_ctor_set_tag(v___x_2400_, 1);
lean_ctor_set(v___x_2400_, 0, v___x_2402_);
v___x_2404_ = v___x_2400_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
else
{
lean_object* v_a_2408_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v_a_2408_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_a_2408_);
lean_dec_ref(v___x_2398_);
v___x_2412_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2413_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2412_);
lean_dec_ref(v___x_2413_);
goto v___jp_2409_;
v___jp_2409_:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = lean_io_error_to_string(v_a_2408_);
v___x_2411_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2410_);
lean_dec_ref(v___x_2411_);
goto v___jp_960_;
}
}
}
}
else
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
lean_dec(v_optArg_x3f_943_);
lean_dec_ref(v_opts_941_);
v___x_2414_ = l___private_Lean_Shell_0__Lean_versionHeader;
v___x_2415_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2414_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2423_; 
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2423_ == 0)
{
lean_object* v_unused_2424_; 
v_unused_2424_ = lean_ctor_get(v___x_2415_, 0);
lean_dec(v_unused_2424_);
v___x_2417_ = v___x_2415_;
v_isShared_2418_ = v_isSharedCheck_2423_;
goto v_resetjp_2416_;
}
else
{
lean_dec(v___x_2415_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2423_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2419_; lean_object* v___x_2421_; 
v___x_2419_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2418_ == 0)
{
lean_ctor_set_tag(v___x_2417_, 1);
lean_ctor_set(v___x_2417_, 0, v___x_2419_);
v___x_2421_ = v___x_2417_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2419_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v_a_2425_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2425_);
lean_dec_ref(v___x_2415_);
v___x_2429_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2430_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2429_);
lean_dec_ref(v___x_2430_);
goto v___jp_2426_;
v___jp_2426_:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = lean_io_error_to_string(v_a_2425_);
v___x_2428_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2427_);
lean_dec_ref(v___x_2428_);
goto v___jp_1138_;
}
}
}
}
else
{
lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2431_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31));
v___x_2432_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2431_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2483_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2435_ = v___x_2432_;
v_isShared_2436_ = v_isSharedCheck_2483_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2432_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2483_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2437_ = lean_unsigned_to_nat(0u);
v___x_2438_ = lean_string_utf8_byte_size(v_a_2433_);
lean_inc(v_a_2433_);
v___x_2439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2439_, 0, v_a_2433_);
lean_ctor_set(v___x_2439_, 1, v___x_2437_);
lean_ctor_set(v___x_2439_, 2, v___x_2438_);
v___x_2440_ = l_String_Slice_toNat_x3f(v___x_2439_);
lean_dec_ref(v___x_2439_);
if (lean_obj_tag(v___x_2440_) == 1)
{
lean_object* v_val_2441_; lean_object* v___x_2442_; uint8_t v___x_2443_; 
v_val_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_val_2441_);
lean_dec_ref(v___x_2440_);
v___x_2442_ = lean_cstr_to_nat("4294967296");
v___x_2443_ = lean_nat_dec_lt(v_val_2441_, v___x_2442_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
lean_dec(v_val_2441_);
lean_del_object(v___x_2435_);
lean_dec(v_a_2433_);
lean_dec_ref(v_opts_941_);
v___x_2444_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32));
v___x_2445_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2444_);
lean_dec_ref(v___x_2445_);
goto v___jp_954_;
}
else
{
lean_object* v_leanOpts_2446_; lean_object* v_forwardedArgs_2447_; uint8_t v_component_2448_; uint8_t v_printPrefix_2449_; uint8_t v_printLibDir_2450_; uint8_t v_useStdin_2451_; uint8_t v_onlyDeps_2452_; uint8_t v_onlySrcDeps_2453_; uint8_t v_depsJson_2454_; lean_object* v_opts_2455_; uint32_t v_trustLevel_2456_; lean_object* v_rootDir_x3f_2457_; lean_object* v_setupFileName_x3f_2458_; lean_object* v_oleanFileName_x3f_2459_; lean_object* v_ileanFileName_x3f_2460_; lean_object* v_cFileName_x3f_2461_; lean_object* v_bcFileName_x3f_2462_; uint8_t v_jsonOutput_2463_; lean_object* v_errorOnKinds_2464_; uint8_t v_printStats_2465_; uint8_t v_run_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2480_; 
v_leanOpts_2446_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_2447_ = lean_ctor_get(v_opts_941_, 1);
v_component_2448_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 8);
v_printPrefix_2449_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 9);
v_printLibDir_2450_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 10);
v_useStdin_2451_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 11);
v_onlyDeps_2452_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2453_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 13);
v_depsJson_2454_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 14);
v_opts_2455_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_2456_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*10);
v_rootDir_x3f_2457_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_2458_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_2459_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_2460_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_2461_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_2462_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_2463_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 15);
v_errorOnKinds_2464_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_2465_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 16);
v_run_2466_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*10 + 17);
v_isSharedCheck_2480_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2468_ = v_opts_941_;
v_isShared_2469_ = v_isSharedCheck_2480_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_errorOnKinds_2464_);
lean_inc(v_bcFileName_x3f_2462_);
lean_inc(v_cFileName_x3f_2461_);
lean_inc(v_ileanFileName_x3f_2460_);
lean_inc(v_oleanFileName_x3f_2459_);
lean_inc(v_setupFileName_x3f_2458_);
lean_inc(v_rootDir_x3f_2457_);
lean_inc(v_opts_2455_);
lean_inc(v_forwardedArgs_2447_);
lean_inc(v_leanOpts_2446_);
lean_dec(v_opts_941_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2480_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
uint32_t v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2475_; 
v___x_2470_ = lean_uint32_of_nat(v_val_2441_);
lean_dec(v_val_2441_);
v___x_2471_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33));
v___x_2472_ = lean_string_append(v___x_2471_, v_a_2433_);
lean_dec(v_a_2433_);
v___x_2473_ = lean_array_push(v_forwardedArgs_2447_, v___x_2472_);
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 1, v___x_2473_);
v___x_2475_ = v___x_2468_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_leanOpts_2446_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2479_, 2, v_opts_2455_);
lean_ctor_set(v_reuseFailAlloc_2479_, 3, v_rootDir_x3f_2457_);
lean_ctor_set(v_reuseFailAlloc_2479_, 4, v_setupFileName_x3f_2458_);
lean_ctor_set(v_reuseFailAlloc_2479_, 5, v_oleanFileName_x3f_2459_);
lean_ctor_set(v_reuseFailAlloc_2479_, 6, v_ileanFileName_x3f_2460_);
lean_ctor_set(v_reuseFailAlloc_2479_, 7, v_cFileName_x3f_2461_);
lean_ctor_set(v_reuseFailAlloc_2479_, 8, v_bcFileName_x3f_2462_);
lean_ctor_set(v_reuseFailAlloc_2479_, 9, v_errorOnKinds_2464_);
lean_ctor_set_uint8(v_reuseFailAlloc_2479_, sizeof(void*)*10 + 8, v_component_2448_);
lean_ctor_set_uint8(v_reuseFailAlloc_2479_, sizeof(void*)*10 + 9, v_printPrefix_2449_);
lean_ctor_set_uint8(v_reuseFailAlloc_2479_, sizeof(void*)*10 + 10, v_printLibDir_2450_);
lean_ctor_set_uint8(v_reuseFailAlloc_2479_, sizeof(void*)*10 + 11, v_useStdin_2451_);
lean_ctor_set_uint8(v_reuseFailAlloc_2479_, sizeof(void*)*10 + 12, v_onlyDeps_2452_);
lean_ctor_set_uint8(v_reuseFailAlloc_2479_, sizeof(void*)*10 + 13, v_onlySrcDeps_2453_);
lean_ctor_set_uint8(v_reuseFailAlloc_2479_, sizeof(void*)*10 + 14, v_depsJson_2454_);
lean_ctor_set_uint32(v_reuseFailAlloc_2479_, sizeof(void*)*10, v_trustLevel_2456_);
lean_ctor_set_uint8(v_reuseFailAlloc_2479_, sizeof(void*)*10 + 15, v_jsonOutput_2463_);
lean_ctor_set_uint8(v_reuseFailAlloc_2479_, sizeof(void*)*10 + 16, v_printStats_2465_);
lean_ctor_set_uint8(v_reuseFailAlloc_2479_, sizeof(void*)*10 + 17, v_run_2466_);
v___x_2475_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2477_; 
lean_ctor_set_uint32(v___x_2475_, sizeof(void*)*10 + 4, v___x_2470_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v___x_2475_);
v___x_2477_ = v___x_2435_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2475_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
}
else
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
lean_dec(v___x_2440_);
lean_del_object(v___x_2435_);
lean_dec(v_a_2433_);
lean_dec_ref(v_opts_941_);
v___x_2481_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34));
v___x_2482_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2481_);
lean_dec_ref(v___x_2482_);
goto v___jp_951_;
}
}
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
lean_dec_ref(v_opts_941_);
v_a_2484_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2484_);
lean_dec_ref(v___x_2432_);
v___x_2488_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2489_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2488_);
lean_dec_ref(v___x_2489_);
goto v___jp_2485_;
v___jp_2485_:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = lean_io_error_to_string(v_a_2484_);
v___x_2487_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2486_);
lean_dec_ref(v___x_2487_);
goto v___jp_948_;
}
}
}
}
else
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
lean_dec(v_optArg_x3f_943_);
v___x_2490_ = lean_internal_set_exit_on_panic(v___x_1142_);
v___x_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2491_, 0, v_opts_941_);
return v___x_2491_;
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
v___x_949_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_950_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_949_);
lean_dec_ref(v___x_950_);
goto v___jp_945_;
}
v___jp_951_:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
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
v___x_958_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
v___jp_960_:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_962_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_961_);
lean_dec_ref(v___x_962_);
goto v___jp_957_;
}
v___jp_963_:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
v___jp_966_:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_968_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_967_);
lean_dec_ref(v___x_968_);
goto v___jp_963_;
}
v___jp_969_:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
return v___x_971_;
}
v___jp_972_:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_974_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_973_);
lean_dec_ref(v___x_974_);
goto v___jp_969_;
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
v___x_979_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_980_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_979_);
lean_dec_ref(v___x_980_);
goto v___jp_975_;
}
v___jp_981_:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
return v___x_983_;
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
v___x_988_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
v___jp_990_:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_992_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_991_);
lean_dec_ref(v___x_992_);
goto v___jp_987_;
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
v___x_1006_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1007_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1006_);
lean_dec_ref(v___x_1007_);
goto v___jp_1002_;
}
v___jp_1008_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
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
v___x_1015_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
return v___x_1016_;
}
v___jp_1017_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1019_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1018_);
lean_dec_ref(v___x_1019_);
goto v___jp_1014_;
}
v___jp_1020_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
return v___x_1022_;
}
v___jp_1023_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1025_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1024_);
lean_dec_ref(v___x_1025_);
goto v___jp_1020_;
}
v___jp_1026_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
return v___x_1028_;
}
v___jp_1029_:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1031_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1030_);
lean_dec_ref(v___x_1031_);
goto v___jp_1026_;
}
v___jp_1032_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
return v___x_1034_;
}
v___jp_1035_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1037_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1036_);
lean_dec_ref(v___x_1037_);
goto v___jp_1032_;
}
v___jp_1038_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
return v___x_1040_;
}
v___jp_1041_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1043_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1042_);
lean_dec_ref(v___x_1043_);
goto v___jp_1038_;
}
v___jp_1044_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = lean_io_error_to_string(v___y_1045_);
v___x_1047_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1046_);
lean_dec_ref(v___x_1047_);
goto v___jp_1041_;
}
v___jp_1048_:
{
uint8_t v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = 1;
v___x_1050_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1049_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1058_; 
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1058_ == 0)
{
lean_object* v_unused_1059_; 
v_unused_1059_ = lean_ctor_get(v___x_1050_, 0);
lean_dec(v_unused_1059_);
v___x_1052_ = v___x_1050_;
v_isShared_1053_ = v_isSharedCheck_1058_;
goto v_resetjp_1051_;
}
else
{
lean_dec(v___x_1050_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1058_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1056_; 
v___x_1054_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_1053_ == 0)
{
lean_ctor_set_tag(v___x_1052_, 1);
lean_ctor_set(v___x_1052_, 0, v___x_1054_);
v___x_1056_ = v___x_1052_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v_a_1060_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1060_);
lean_dec_ref(v___x_1050_);
v___x_1061_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1062_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1061_);
lean_dec_ref(v___x_1062_);
v___y_1045_ = v_a_1060_;
goto v___jp_1044_;
}
}
v___jp_1063_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__0));
v___x_1065_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1064_);
lean_dec_ref(v___x_1065_);
goto v___jp_1048_;
}
v___jp_1066_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
return v___x_1068_;
}
v___jp_1069_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1071_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1070_);
lean_dec_ref(v___x_1071_);
goto v___jp_1066_;
}
v___jp_1072_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
return v___x_1074_;
}
v___jp_1075_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1077_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1076_);
lean_dec_ref(v___x_1077_);
goto v___jp_1072_;
}
v___jp_1078_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
return v___x_1080_;
}
v___jp_1081_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1083_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1082_);
lean_dec_ref(v___x_1083_);
goto v___jp_1078_;
}
v___jp_1084_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
return v___x_1086_;
}
v___jp_1087_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1089_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1088_);
lean_dec_ref(v___x_1089_);
goto v___jp_1084_;
}
v___jp_1090_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
return v___x_1092_;
}
v___jp_1093_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1095_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1094_);
lean_dec_ref(v___x_1095_);
goto v___jp_1090_;
}
v___jp_1096_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
return v___x_1098_;
}
v___jp_1099_:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
return v___x_1101_;
}
v___jp_1102_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1104_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1103_);
lean_dec_ref(v___x_1104_);
goto v___jp_1099_;
}
v___jp_1105_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
return v___x_1107_;
}
v___jp_1108_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1110_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1109_);
lean_dec_ref(v___x_1110_);
goto v___jp_1105_;
}
v___jp_1111_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
return v___x_1113_;
}
v___jp_1114_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1116_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1115_);
lean_dec_ref(v___x_1116_);
goto v___jp_1111_;
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed(lean_object* v_opts_2492_, lean_object* v_opt_2493_, lean_object* v_optArg_x3f_2494_, lean_object* v_a_2495_){
_start:
{
uint32_t v_opt_boxed_2496_; lean_object* v_res_2497_; 
v_opt_boxed_2496_ = lean_unbox_uint32(v_opt_2493_);
lean_dec(v_opt_2493_);
v_res_2497_ = lean_shell_options_process(v_opts_2492_, v_opt_boxed_2496_, v_optArg_x3f_2494_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(lean_object* v_opts_2498_, lean_object* v_opt_2499_){
_start:
{
lean_object* v_name_2500_; lean_object* v_defValue_2501_; lean_object* v_map_2502_; lean_object* v___x_2503_; 
v_name_2500_ = lean_ctor_get(v_opt_2499_, 0);
v_defValue_2501_ = lean_ctor_get(v_opt_2499_, 1);
v_map_2502_ = lean_ctor_get(v_opts_2498_, 0);
v___x_2503_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2502_, v_name_2500_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_inc(v_defValue_2501_);
return v_defValue_2501_;
}
else
{
lean_object* v_val_2504_; 
v_val_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_val_2504_);
lean_dec_ref(v___x_2503_);
if (lean_obj_tag(v_val_2504_) == 3)
{
lean_object* v_v_2505_; 
v_v_2505_ = lean_ctor_get(v_val_2504_, 0);
lean_inc(v_v_2505_);
lean_dec_ref(v_val_2504_);
return v_v_2505_;
}
else
{
lean_dec(v_val_2504_);
lean_inc(v_defValue_2501_);
return v_defValue_2501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___boxed(lean_object* v_opts_2506_, lean_object* v_opt_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_opts_2506_, v_opt_2507_);
lean_dec_ref(v_opt_2507_);
lean_dec_ref(v_opts_2506_);
return v_res_2508_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2510_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2511_ = lean_string_utf8_byte_size(v___x_2510_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(lean_object* v_s_2512_){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; uint8_t v___x_2516_; 
v___x_2513_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2514_ = lean_string_utf8_byte_size(v_s_2512_);
v___x_2515_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1);
v___x_2516_ = lean_nat_dec_le(v___x_2515_, v___x_2514_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; 
lean_dec_ref(v_s_2512_);
v___x_2517_ = lean_box(0);
return v___x_2517_;
}
else
{
lean_object* v___x_2518_; uint8_t v___x_2519_; 
v___x_2518_ = lean_unsigned_to_nat(0u);
v___x_2519_ = lean_string_memcmp(v_s_2512_, v___x_2513_, v___x_2518_, v___x_2518_, v___x_2515_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; 
lean_dec_ref(v_s_2512_);
v___x_2520_ = lean_box(0);
return v___x_2520_;
}
else
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
lean_inc_ref(v_s_2512_);
v___x_2521_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2521_, 0, v_s_2512_);
lean_ctor_set(v___x_2521_, 1, v___x_2518_);
lean_ctor_set(v___x_2521_, 2, v___x_2514_);
v___x_2522_ = l_String_Slice_pos_x21(v___x_2521_, v___x_2515_);
lean_dec_ref(v___x_2521_);
v___x_2523_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2523_, 0, v_s_2512_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
lean_ctor_set(v___x_2523_, 2, v___x_2514_);
v___x_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2523_);
return v___x_2524_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(lean_object* v_s_2525_, lean_object* v_pat_2526_){
_start:
{
lean_object* v___x_2527_; 
v___x_2527_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v_s_2525_);
return v___x_2527_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___boxed(lean_object* v_s_2528_, lean_object* v_pat_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(v_s_2528_, v_pat_2529_);
lean_dec_ref(v_pat_2529_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object* v___x_2532_, lean_object* v___x_2533_, lean_object* v_mainModuleName_2534_, lean_object* v_a_2535_, lean_object* v___x_2536_, lean_object* v_fileName_2537_, lean_object* v___x_2538_, lean_object* v___x_2539_, lean_object* v___x_2540_, lean_object* v___x_2541_, lean_object* v___x_2542_, lean_object* v___x_2543_, lean_object* v___x_2544_, lean_object* v___x_2545_, uint8_t v_printLibDir_2546_){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v_env_2553_; lean_object* v___x_2554_; uint8_t v___x_2555_; lean_object* v_fileName_2557_; lean_object* v_fileMap_2558_; lean_object* v_currRecDepth_2559_; lean_object* v_ref_2560_; lean_object* v_currNamespace_2561_; lean_object* v_openDecls_2562_; lean_object* v_initHeartbeats_2563_; lean_object* v_maxHeartbeats_2564_; lean_object* v_quotContext_2565_; lean_object* v_currMacroScope_2566_; lean_object* v_cancelTk_x3f_2567_; uint8_t v_suppressElabErrors_2568_; lean_object* v_inheritedTraceOptions_2569_; lean_object* v___y_2570_; uint8_t v___y_2599_; uint8_t v___x_2619_; 
v___x_2548_ = lean_io_get_num_heartbeats();
v___x_2549_ = lean_st_mk_ref(v___x_2532_);
v___x_2550_ = l_Lean_inheritedTraceOptions;
v___x_2551_ = lean_st_ref_get(v___x_2550_);
v___x_2552_ = lean_st_ref_get(v___x_2549_);
v_env_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc_ref(v_env_2553_);
lean_dec(v___x_2552_);
v___x_2554_ = l_Lean_diagnostics;
v___x_2555_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v___x_2533_, v___x_2554_);
v___x_2619_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2553_);
lean_dec_ref(v_env_2553_);
if (v___x_2619_ == 0)
{
if (v___x_2555_ == 0)
{
lean_dec_ref(v___x_2536_);
lean_inc(v___x_2549_);
lean_inc(v___x_2541_);
v_fileName_2557_ = v_fileName_2537_;
v_fileMap_2558_ = v___x_2538_;
v_currRecDepth_2559_ = v___x_2539_;
v_ref_2560_ = v___x_2540_;
v_currNamespace_2561_ = v___x_2541_;
v_openDecls_2562_ = v___x_2542_;
v_initHeartbeats_2563_ = v___x_2548_;
v_maxHeartbeats_2564_ = v___x_2543_;
v_quotContext_2565_ = v___x_2541_;
v_currMacroScope_2566_ = v___x_2544_;
v_cancelTk_x3f_2567_ = v___x_2545_;
v_suppressElabErrors_2568_ = v_printLibDir_2546_;
v_inheritedTraceOptions_2569_ = v___x_2551_;
v___y_2570_ = v___x_2549_;
goto v___jp_2556_;
}
else
{
v___y_2599_ = v___x_2619_;
goto v___jp_2598_;
}
}
else
{
v___y_2599_ = v___x_2555_;
goto v___jp_2598_;
}
v___jp_2556_:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2571_ = l_Lean_maxRecDepth;
v___x_2572_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_2533_, v___x_2571_);
v___x_2573_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2573_, 0, v_fileName_2557_);
lean_ctor_set(v___x_2573_, 1, v_fileMap_2558_);
lean_ctor_set(v___x_2573_, 2, v___x_2533_);
lean_ctor_set(v___x_2573_, 3, v_currRecDepth_2559_);
lean_ctor_set(v___x_2573_, 4, v___x_2572_);
lean_ctor_set(v___x_2573_, 5, v_ref_2560_);
lean_ctor_set(v___x_2573_, 6, v_currNamespace_2561_);
lean_ctor_set(v___x_2573_, 7, v_openDecls_2562_);
lean_ctor_set(v___x_2573_, 8, v_initHeartbeats_2563_);
lean_ctor_set(v___x_2573_, 9, v_maxHeartbeats_2564_);
lean_ctor_set(v___x_2573_, 10, v_quotContext_2565_);
lean_ctor_set(v___x_2573_, 11, v_currMacroScope_2566_);
lean_ctor_set(v___x_2573_, 12, v_cancelTk_x3f_2567_);
lean_ctor_set(v___x_2573_, 13, v_inheritedTraceOptions_2569_);
lean_ctor_set_uint8(v___x_2573_, sizeof(void*)*14, v___x_2555_);
lean_ctor_set_uint8(v___x_2573_, sizeof(void*)*14 + 1, v_suppressElabErrors_2568_);
v___x_2574_ = l_Lean_Compiler_LCNF_emitC(v_mainModuleName_2534_, v___x_2573_, v___y_2570_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_a_2575_);
lean_dec_ref(v___x_2574_);
v___x_2576_ = lean_st_ref_get(v___x_2549_);
lean_dec(v___x_2549_);
lean_dec(v___x_2576_);
v___x_2577_ = lean_string_to_utf8(v_a_2575_);
lean_dec(v_a_2575_);
v___x_2578_ = lean_io_prim_handle_write(v_a_2535_, v___x_2577_);
lean_dec_ref(v___x_2577_);
return v___x_2578_;
}
else
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2597_; 
lean_dec(v___x_2549_);
v_a_2579_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2581_ = v___x_2574_;
v_isShared_2582_ = v_isSharedCheck_2597_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2574_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2597_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
if (lean_obj_tag(v_a_2579_) == 0)
{
lean_object* v_msg_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2587_; 
v_msg_2583_ = lean_ctor_get(v_a_2579_, 1);
lean_inc_ref(v_msg_2583_);
lean_dec_ref(v_a_2579_);
v___x_2584_ = l_Lean_MessageData_toString(v_msg_2583_);
v___x_2585_ = lean_mk_io_user_error(v___x_2584_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 0, v___x_2585_);
v___x_2587_ = v___x_2581_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2585_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
else
{
lean_object* v_id_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2595_; 
v_id_2589_ = lean_ctor_get(v_a_2579_, 0);
lean_inc(v_id_2589_);
lean_dec_ref(v_a_2579_);
v___x_2590_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0));
v___x_2591_ = l_Nat_reprFast(v_id_2589_);
v___x_2592_ = lean_string_append(v___x_2590_, v___x_2591_);
lean_dec_ref(v___x_2591_);
v___x_2593_ = lean_mk_io_user_error(v___x_2592_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 0, v___x_2593_);
v___x_2595_ = v___x_2581_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2593_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
}
v___jp_2598_:
{
if (v___y_2599_ == 0)
{
lean_object* v___x_2600_; lean_object* v_env_2601_; lean_object* v_nextMacroScope_2602_; lean_object* v_ngen_2603_; lean_object* v_auxDeclNGen_2604_; lean_object* v_traceState_2605_; lean_object* v_messages_2606_; lean_object* v_infoState_2607_; lean_object* v_snapshotTasks_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2617_; 
v___x_2600_ = lean_st_ref_take(v___x_2549_);
v_env_2601_ = lean_ctor_get(v___x_2600_, 0);
v_nextMacroScope_2602_ = lean_ctor_get(v___x_2600_, 1);
v_ngen_2603_ = lean_ctor_get(v___x_2600_, 2);
v_auxDeclNGen_2604_ = lean_ctor_get(v___x_2600_, 3);
v_traceState_2605_ = lean_ctor_get(v___x_2600_, 4);
v_messages_2606_ = lean_ctor_get(v___x_2600_, 6);
v_infoState_2607_ = lean_ctor_get(v___x_2600_, 7);
v_snapshotTasks_2608_ = lean_ctor_get(v___x_2600_, 8);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2617_ == 0)
{
lean_object* v_unused_2618_; 
v_unused_2618_ = lean_ctor_get(v___x_2600_, 5);
lean_dec(v_unused_2618_);
v___x_2610_ = v___x_2600_;
v_isShared_2611_ = v_isSharedCheck_2617_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_snapshotTasks_2608_);
lean_inc(v_infoState_2607_);
lean_inc(v_messages_2606_);
lean_inc(v_traceState_2605_);
lean_inc(v_auxDeclNGen_2604_);
lean_inc(v_ngen_2603_);
lean_inc(v_nextMacroScope_2602_);
lean_inc(v_env_2601_);
lean_dec(v___x_2600_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2617_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2612_; lean_object* v___x_2614_; 
v___x_2612_ = l_Lean_Kernel_enableDiag(v_env_2601_, v___x_2555_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 5, v___x_2536_);
lean_ctor_set(v___x_2610_, 0, v___x_2612_);
v___x_2614_ = v___x_2610_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2612_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v_nextMacroScope_2602_);
lean_ctor_set(v_reuseFailAlloc_2616_, 2, v_ngen_2603_);
lean_ctor_set(v_reuseFailAlloc_2616_, 3, v_auxDeclNGen_2604_);
lean_ctor_set(v_reuseFailAlloc_2616_, 4, v_traceState_2605_);
lean_ctor_set(v_reuseFailAlloc_2616_, 5, v___x_2536_);
lean_ctor_set(v_reuseFailAlloc_2616_, 6, v_messages_2606_);
lean_ctor_set(v_reuseFailAlloc_2616_, 7, v_infoState_2607_);
lean_ctor_set(v_reuseFailAlloc_2616_, 8, v_snapshotTasks_2608_);
v___x_2614_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
lean_object* v___x_2615_; 
v___x_2615_ = lean_st_ref_set(v___x_2549_, v___x_2614_);
lean_inc(v___x_2549_);
lean_inc(v___x_2541_);
v_fileName_2557_ = v_fileName_2537_;
v_fileMap_2558_ = v___x_2538_;
v_currRecDepth_2559_ = v___x_2539_;
v_ref_2560_ = v___x_2540_;
v_currNamespace_2561_ = v___x_2541_;
v_openDecls_2562_ = v___x_2542_;
v_initHeartbeats_2563_ = v___x_2548_;
v_maxHeartbeats_2564_ = v___x_2543_;
v_quotContext_2565_ = v___x_2541_;
v_currMacroScope_2566_ = v___x_2544_;
v_cancelTk_x3f_2567_ = v___x_2545_;
v_suppressElabErrors_2568_ = v_printLibDir_2546_;
v_inheritedTraceOptions_2569_ = v___x_2551_;
v___y_2570_ = v___x_2549_;
goto v___jp_2556_;
}
}
}
else
{
lean_dec_ref(v___x_2536_);
lean_inc(v___x_2549_);
lean_inc(v___x_2541_);
v_fileName_2557_ = v_fileName_2537_;
v_fileMap_2558_ = v___x_2538_;
v_currRecDepth_2559_ = v___x_2539_;
v_ref_2560_ = v___x_2540_;
v_currNamespace_2561_ = v___x_2541_;
v_openDecls_2562_ = v___x_2542_;
v_initHeartbeats_2563_ = v___x_2548_;
v_maxHeartbeats_2564_ = v___x_2543_;
v_quotContext_2565_ = v___x_2541_;
v_currMacroScope_2566_ = v___x_2544_;
v_cancelTk_x3f_2567_ = v___x_2545_;
v_suppressElabErrors_2568_ = v_printLibDir_2546_;
v_inheritedTraceOptions_2569_ = v___x_2551_;
v___y_2570_ = v___x_2549_;
goto v___jp_2556_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object* v___x_2620_, lean_object* v___x_2621_, lean_object* v_mainModuleName_2622_, lean_object* v_a_2623_, lean_object* v___x_2624_, lean_object* v_fileName_2625_, lean_object* v___x_2626_, lean_object* v___x_2627_, lean_object* v___x_2628_, lean_object* v___x_2629_, lean_object* v___x_2630_, lean_object* v___x_2631_, lean_object* v___x_2632_, lean_object* v___x_2633_, lean_object* v_printLibDir_2634_, lean_object* v___y_2635_){
_start:
{
uint8_t v_printLibDir_boxed_2636_; lean_object* v_res_2637_; 
v_printLibDir_boxed_2636_ = lean_unbox(v_printLibDir_2634_);
v_res_2637_ = l___private_Lean_Shell_0__Lean_shellMain___lam__0(v___x_2620_, v___x_2621_, v_mainModuleName_2622_, v_a_2623_, v___x_2624_, v_fileName_2625_, v___x_2626_, v___x_2627_, v___x_2628_, v___x_2629_, v___x_2630_, v___x_2631_, v___x_2632_, v___x_2633_, v_printLibDir_boxed_2636_);
lean_dec(v_a_2623_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(lean_object* v_val_2638_, lean_object* v_a_2639_, lean_object* v_b_2640_){
_start:
{
lean_object* v_str_2641_; lean_object* v_startInclusive_2642_; lean_object* v_endExclusive_2643_; lean_object* v___x_2644_; uint8_t v___x_2645_; 
v_str_2641_ = lean_ctor_get(v_val_2638_, 0);
v_startInclusive_2642_ = lean_ctor_get(v_val_2638_, 1);
v_endExclusive_2643_ = lean_ctor_get(v_val_2638_, 2);
v___x_2644_ = lean_nat_sub(v_endExclusive_2643_, v_startInclusive_2642_);
v___x_2645_ = lean_nat_dec_eq(v_a_2639_, v___x_2644_);
lean_dec(v___x_2644_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2646_; uint32_t v___x_2647_; uint32_t v___x_2648_; uint8_t v___x_2649_; 
lean_dec(v_b_2640_);
v___x_2646_ = lean_nat_add(v_startInclusive_2642_, v_a_2639_);
v___x_2647_ = lean_string_utf8_get_fast(v_str_2641_, v___x_2646_);
v___x_2648_ = 10;
v___x_2649_ = lean_uint32_dec_eq(v___x_2647_, v___x_2648_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
lean_dec(v_a_2639_);
v___x_2650_ = lean_box(0);
v___x_2651_ = lean_string_utf8_next_fast(v_str_2641_, v___x_2646_);
lean_dec(v___x_2646_);
v___x_2652_ = lean_nat_sub(v___x_2651_, v_startInclusive_2642_);
v_a_2639_ = v___x_2652_;
v_b_2640_ = v___x_2650_;
goto _start;
}
else
{
lean_object* v___x_2654_; 
lean_dec(v___x_2646_);
v___x_2654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2654_, 0, v_a_2639_);
return v___x_2654_;
}
}
else
{
lean_dec(v_a_2639_);
return v_b_2640_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg___boxed(lean_object* v_val_2655_, lean_object* v_a_2656_, lean_object* v_b_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_2655_, v_a_2656_, v_b_2657_);
lean_dec_ref(v_val_2655_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(lean_object* v_s_2659_){
_start:
{
uint32_t v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2661_ = 10;
v___x_2662_ = lean_string_push(v_s_2659_, v___x_2661_);
v___x_2663_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4___boxed(lean_object* v_s_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_s_2664_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object* v_s_2667_){
_start:
{
uint32_t v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2669_ = 10;
v___x_2670_ = lean_string_push(v_s_2667_, v___x_2669_);
v___x_2671_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2670_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___boxed(lean_object* v_s_2672_, lean_object* v_a_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v_s_2672_);
return v_res_2674_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shellMain___closed__0(void){
_start:
{
lean_object* v___x_2675_; uint8_t v___x_2676_; 
v___x_2675_ = lean_box(0);
v___x_2676_ = lean_internal_has_address_sanitizer(v___x_2675_);
return v___x_2676_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__3(void){
_start:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2679_ = l_Lean_Options_empty;
v___x_2680_ = l_Lean_Core_getMaxHeartbeats(v___x_2679_);
return v___x_2680_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__4(void){
_start:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2681_ = lean_unsigned_to_nat(1u);
v___x_2682_ = l_Lean_firstFrontendMacroScope;
v___x_2683_ = lean_nat_add(v___x_2682_, v___x_2681_);
return v___x_2683_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__9(void){
_start:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2694_ = lean_unsigned_to_nat(32u);
v___x_2695_ = lean_mk_empty_array_with_capacity(v___x_2694_);
v___x_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2695_);
return v___x_2696_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10(void){
_start:
{
size_t v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2697_ = ((size_t)5ULL);
v___x_2698_ = lean_unsigned_to_nat(0u);
v___x_2699_ = lean_unsigned_to_nat(32u);
v___x_2700_ = lean_mk_empty_array_with_capacity(v___x_2699_);
v___x_2701_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__9, &l___private_Lean_Shell_0__Lean_shellMain___closed__9_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__9);
v___x_2702_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
lean_ctor_set(v___x_2702_, 1, v___x_2700_);
lean_ctor_set(v___x_2702_, 2, v___x_2698_);
lean_ctor_set(v___x_2702_, 3, v___x_2698_);
lean_ctor_set_usize(v___x_2702_, 4, v___x_2697_);
return v___x_2702_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11(void){
_start:
{
lean_object* v___x_2703_; uint64_t v___x_2704_; lean_object* v___x_2705_; 
v___x_2703_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__10, &l___private_Lean_Shell_0__Lean_shellMain___closed__10_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10);
v___x_2704_ = 0ULL;
v___x_2705_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2705_, 0, v___x_2703_);
lean_ctor_set_uint64(v___x_2705_, sizeof(void*)*1, v___x_2704_);
return v___x_2705_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__12(void){
_start:
{
lean_object* v___x_2706_; 
v___x_2706_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2706_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13(void){
_start:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2707_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__12, &l___private_Lean_Shell_0__Lean_shellMain___closed__12_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__12);
v___x_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
return v___x_2708_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14(void){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2709_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__13, &l___private_Lean_Shell_0__Lean_shellMain___closed__13_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13);
v___x_2710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
return v___x_2710_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__15(void){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2711_ = l_Lean_NameSet_empty;
v___x_2712_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__10, &l___private_Lean_Shell_0__Lean_shellMain___closed__10_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10);
v___x_2713_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2712_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
lean_ctor_set(v___x_2713_, 2, v___x_2711_);
return v___x_2713_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16(void){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; uint8_t v___x_2716_; lean_object* v___x_2717_; 
v___x_2714_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__10, &l___private_Lean_Shell_0__Lean_shellMain___closed__10_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10);
v___x_2715_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__13, &l___private_Lean_Shell_0__Lean_shellMain___closed__13_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13);
v___x_2716_ = 1;
v___x_2717_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2717_, 0, v___x_2715_);
lean_ctor_set(v___x_2717_, 1, v___x_2715_);
lean_ctor_set(v___x_2717_, 2, v___x_2714_);
lean_ctor_set_uint8(v___x_2717_, sizeof(void*)*3, v___x_2716_);
return v___x_2717_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__21(void){
_start:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2723_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__20));
v___x_2724_ = lean_string_utf8_byte_size(v___x_2723_);
return v___x_2724_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__22(void){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2725_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__21, &l___private_Lean_Shell_0__Lean_shellMain___closed__21_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__21);
v___x_2726_ = lean_unsigned_to_nat(0u);
v___x_2727_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__20));
v___x_2728_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2727_);
lean_ctor_set(v___x_2728_, 1, v___x_2726_);
lean_ctor_set(v___x_2728_, 2, v___x_2725_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* lean_shell_main(lean_object* v_args_2732_, lean_object* v_opts_2733_){
_start:
{
lean_object* v___y_2739_; lean_object* v_fns_2756_; lean_object* v_leanOpts_2775_; lean_object* v_forwardedArgs_2776_; uint8_t v_component_2777_; uint8_t v_printPrefix_2778_; uint8_t v_printLibDir_2779_; uint8_t v_useStdin_2780_; uint8_t v_onlyDeps_2781_; uint8_t v_onlySrcDeps_2782_; uint8_t v_depsJson_2783_; uint32_t v_trustLevel_2784_; lean_object* v_rootDir_x3f_2785_; lean_object* v_setupFileName_x3f_2786_; lean_object* v_oleanFileName_x3f_2787_; lean_object* v_ileanFileName_x3f_2788_; lean_object* v_cFileName_x3f_2789_; lean_object* v_bcFileName_x3f_2790_; uint8_t v_jsonOutput_2791_; lean_object* v_errorOnKinds_2792_; uint8_t v_printStats_2793_; uint8_t v_run_2794_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; 
v_leanOpts_2775_ = lean_ctor_get(v_opts_2733_, 0);
lean_inc_ref(v_leanOpts_2775_);
v_forwardedArgs_2776_ = lean_ctor_get(v_opts_2733_, 1);
lean_inc_ref(v_forwardedArgs_2776_);
v_component_2777_ = lean_ctor_get_uint8(v_opts_2733_, sizeof(void*)*10 + 8);
v_printPrefix_2778_ = lean_ctor_get_uint8(v_opts_2733_, sizeof(void*)*10 + 9);
v_printLibDir_2779_ = lean_ctor_get_uint8(v_opts_2733_, sizeof(void*)*10 + 10);
v_useStdin_2780_ = lean_ctor_get_uint8(v_opts_2733_, sizeof(void*)*10 + 11);
v_onlyDeps_2781_ = lean_ctor_get_uint8(v_opts_2733_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2782_ = lean_ctor_get_uint8(v_opts_2733_, sizeof(void*)*10 + 13);
v_depsJson_2783_ = lean_ctor_get_uint8(v_opts_2733_, sizeof(void*)*10 + 14);
v_trustLevel_2784_ = lean_ctor_get_uint32(v_opts_2733_, sizeof(void*)*10);
v_rootDir_x3f_2785_ = lean_ctor_get(v_opts_2733_, 3);
lean_inc(v_rootDir_x3f_2785_);
v_setupFileName_x3f_2786_ = lean_ctor_get(v_opts_2733_, 4);
lean_inc(v_setupFileName_x3f_2786_);
v_oleanFileName_x3f_2787_ = lean_ctor_get(v_opts_2733_, 5);
lean_inc(v_oleanFileName_x3f_2787_);
v_ileanFileName_x3f_2788_ = lean_ctor_get(v_opts_2733_, 6);
lean_inc(v_ileanFileName_x3f_2788_);
v_cFileName_x3f_2789_ = lean_ctor_get(v_opts_2733_, 7);
lean_inc(v_cFileName_x3f_2789_);
v_bcFileName_x3f_2790_ = lean_ctor_get(v_opts_2733_, 8);
lean_inc(v_bcFileName_x3f_2790_);
v_jsonOutput_2791_ = lean_ctor_get_uint8(v_opts_2733_, sizeof(void*)*10 + 15);
v_errorOnKinds_2792_ = lean_ctor_get(v_opts_2733_, 9);
lean_inc_ref(v_errorOnKinds_2792_);
v_printStats_2793_ = lean_ctor_get_uint8(v_opts_2733_, sizeof(void*)*10 + 16);
v_run_2794_ = lean_ctor_get_uint8(v_opts_2733_, sizeof(void*)*10 + 17);
lean_dec_ref(v_opts_2733_);
if (v_printPrefix_2778_ == 0)
{
if (v_printLibDir_2779_ == 0)
{
uint8_t v___x_2821_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v_mainModuleName_2828_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v_contents_2928_; lean_object* v___y_2954_; lean_object* v_str_2955_; lean_object* v_startInclusive_2956_; lean_object* v_endExclusive_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v_fileName_3060_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v_fst_3098_; lean_object* v_snd_3099_; lean_object* v___x_3159_; lean_object* v_maxMemory_3160_; lean_object* v___x_3161_; uint8_t v___x_3162_; 
v___x_2821_ = 1;
v___x_3159_ = l___private_Lean_Shell_0__Lean_maxMemory;
v_maxMemory_3160_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_leanOpts_2775_, v___x_3159_);
v___x_3161_ = lean_unsigned_to_nat(0u);
v___x_3162_ = lean_nat_dec_eq(v_maxMemory_3160_, v___x_3161_);
if (v___x_3162_ == 0)
{
size_t v___x_3163_; size_t v___x_3164_; size_t v___x_3165_; size_t v___x_3166_; lean_object* v___x_3167_; 
v___x_3163_ = lean_usize_of_nat(v_maxMemory_3160_);
lean_dec(v_maxMemory_3160_);
v___x_3164_ = ((size_t)1024ULL);
v___x_3165_ = lean_usize_mul(v___x_3163_, v___x_3164_);
v___x_3166_ = lean_usize_mul(v___x_3165_, v___x_3164_);
v___x_3167_ = lean_internal_set_max_memory(v___x_3166_);
goto v___jp_3150_;
}
else
{
lean_dec(v_maxMemory_3160_);
goto v___jp_3150_;
}
v___jp_2822_:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2829_ = lean_unsigned_to_nat(0u);
v___x_2830_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1));
lean_inc(v_mainModuleName_2828_);
lean_inc_ref(v_leanOpts_2775_);
v___x_2831_ = l_Lean_Elab_runFrontend(v___y_2825_, v_leanOpts_2775_, v___y_2827_, v_mainModuleName_2828_, v_trustLevel_2784_, v_oleanFileName_x3f_2787_, v_ileanFileName_x3f_2788_, v_jsonOutput_2791_, v_errorOnKinds_2792_, v___x_2830_, v_printStats_2793_, v___y_2824_);
lean_dec_ref(v_errorOnKinds_2792_);
lean_dec(v_ileanFileName_x3f_2788_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2898_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2834_ = v___x_2831_;
v_isShared_2835_ = v_isSharedCheck_2898_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2831_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2898_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
if (lean_obj_tag(v_a_2832_) == 1)
{
if (v_run_2794_ == 0)
{
lean_del_object(v___x_2834_);
lean_dec(v___y_2826_);
if (lean_obj_tag(v_cFileName_x3f_2789_) == 1)
{
lean_object* v_val_2836_; lean_object* v_val_2837_; uint8_t v___x_2838_; lean_object* v___x_2839_; 
v_val_2836_ = lean_ctor_get(v_a_2832_, 0);
lean_inc(v_val_2836_);
v_val_2837_ = lean_ctor_get(v_cFileName_x3f_2789_, 0);
lean_inc(v_val_2837_);
lean_dec_ref(v_cFileName_x3f_2789_);
v___x_2838_ = 1;
v___x_2839_ = lean_io_prim_handle_mk(v_val_2837_, v___x_2838_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___f_2859_; lean_object* v___x_2860_; 
lean_dec(v_val_2837_);
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
lean_dec_ref(v___x_2839_);
v___x_2841_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__2));
v___x_2842_ = l_Lean_instInhabitedFileMap_default;
v___x_2843_ = l_Lean_Options_empty;
v___x_2844_ = lean_box(0);
v___x_2845_ = lean_box(0);
v___x_2846_ = lean_box(0);
v___x_2847_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__3, &l___private_Lean_Shell_0__Lean_shellMain___closed__3_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__3);
v___x_2848_ = l_Lean_firstFrontendMacroScope;
v___x_2849_ = lean_box(0);
v___x_2850_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__4, &l___private_Lean_Shell_0__Lean_shellMain___closed__4_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__4);
v___x_2851_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__7));
v___x_2852_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__8));
v___x_2853_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__11, &l___private_Lean_Shell_0__Lean_shellMain___closed__11_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11);
v___x_2854_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__14, &l___private_Lean_Shell_0__Lean_shellMain___closed__14_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14);
v___x_2855_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__15, &l___private_Lean_Shell_0__Lean_shellMain___closed__15_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__15);
v___x_2856_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__16, &l___private_Lean_Shell_0__Lean_shellMain___closed__16_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16);
lean_inc(v_val_2836_);
v___x_2857_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2857_, 0, v_val_2836_);
lean_ctor_set(v___x_2857_, 1, v___x_2850_);
lean_ctor_set(v___x_2857_, 2, v___x_2851_);
lean_ctor_set(v___x_2857_, 3, v___x_2852_);
lean_ctor_set(v___x_2857_, 4, v___x_2853_);
lean_ctor_set(v___x_2857_, 5, v___x_2854_);
lean_ctor_set(v___x_2857_, 6, v___x_2855_);
lean_ctor_set(v___x_2857_, 7, v___x_2856_);
lean_ctor_set(v___x_2857_, 8, v___x_2830_);
v___x_2858_ = lean_box(v_printLibDir_2779_);
lean_inc(v_mainModuleName_2828_);
v___f_2859_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed), 16, 15);
lean_closure_set(v___f_2859_, 0, v___x_2857_);
lean_closure_set(v___f_2859_, 1, v___x_2843_);
lean_closure_set(v___f_2859_, 2, v_mainModuleName_2828_);
lean_closure_set(v___f_2859_, 3, v_a_2840_);
lean_closure_set(v___f_2859_, 4, v___x_2854_);
lean_closure_set(v___f_2859_, 5, v___y_2823_);
lean_closure_set(v___f_2859_, 6, v___x_2842_);
lean_closure_set(v___f_2859_, 7, v___x_2829_);
lean_closure_set(v___f_2859_, 8, v___x_2844_);
lean_closure_set(v___f_2859_, 9, v___x_2845_);
lean_closure_set(v___f_2859_, 10, v___x_2846_);
lean_closure_set(v___f_2859_, 11, v___x_2847_);
lean_closure_set(v___f_2859_, 12, v___x_2848_);
lean_closure_set(v___f_2859_, 13, v___x_2849_);
lean_closure_set(v___f_2859_, 14, v___x_2858_);
v___x_2860_ = l_Lean_profileitIOUnsafe___redArg(v___x_2841_, v_leanOpts_2775_, v___f_2859_, v___x_2845_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_dec_ref(v___x_2860_);
v___y_2796_ = v_mainModuleName_2828_;
v___y_2797_ = v_a_2832_;
v___y_2798_ = v_val_2836_;
goto v___jp_2795_;
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2868_; 
lean_dec(v_val_2836_);
lean_dec_ref(v_a_2832_);
lean_dec(v_mainModuleName_2828_);
lean_dec(v_bcFileName_x3f_2790_);
lean_dec_ref(v_leanOpts_2775_);
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2863_ = v___x_2860_;
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2860_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
else
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
lean_dec_ref(v___x_2839_);
lean_dec(v_val_2836_);
lean_dec_ref(v_a_2832_);
lean_dec(v_mainModuleName_2828_);
lean_dec_ref(v___y_2823_);
lean_dec(v_bcFileName_x3f_2790_);
lean_dec_ref(v_leanOpts_2775_);
v___x_2869_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__17));
v___x_2870_ = lean_string_append(v___x_2869_, v_val_2837_);
lean_dec(v_val_2837_);
v___x_2871_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__1));
v___x_2872_ = lean_string_append(v___x_2870_, v___x_2871_);
v___x_2873_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_2872_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2881_; 
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2881_ == 0)
{
lean_object* v_unused_2882_; 
v_unused_2882_ = lean_ctor_get(v___x_2873_, 0);
lean_dec(v_unused_2882_);
v___x_2875_ = v___x_2873_;
v_isShared_2876_ = v_isSharedCheck_2881_;
goto v_resetjp_2874_;
}
else
{
lean_dec(v___x_2873_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2881_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2877_; lean_object* v___x_2879_; 
v___x_2877_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 0, v___x_2877_);
v___x_2879_ = v___x_2875_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2877_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
else
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
v_a_2883_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v___x_2873_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___x_2873_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
}
else
{
lean_object* v_val_2891_; 
lean_dec_ref(v___y_2823_);
lean_dec(v_cFileName_x3f_2789_);
v_val_2891_ = lean_ctor_get(v_a_2832_, 0);
lean_inc(v_val_2891_);
v___y_2796_ = v_mainModuleName_2828_;
v___y_2797_ = v_a_2832_;
v___y_2798_ = v_val_2891_;
goto v___jp_2795_;
}
}
else
{
lean_object* v_val_2892_; uint32_t v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2896_; 
lean_dec(v_mainModuleName_2828_);
lean_dec_ref(v___y_2823_);
lean_dec(v_bcFileName_x3f_2790_);
lean_dec(v_cFileName_x3f_2789_);
v_val_2892_ = lean_ctor_get(v_a_2832_, 0);
lean_inc(v_val_2892_);
lean_dec_ref(v_a_2832_);
v___x_2893_ = lean_run_main(v_val_2892_, v_leanOpts_2775_, v___y_2826_);
lean_dec(v___y_2826_);
lean_dec_ref(v_leanOpts_2775_);
lean_dec(v_val_2892_);
v___x_2894_ = lean_box_uint32(v___x_2893_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v___x_2894_);
v___x_2896_ = v___x_2834_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2894_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
else
{
lean_del_object(v___x_2834_);
lean_dec(v_mainModuleName_2828_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2823_);
lean_dec(v_bcFileName_x3f_2790_);
lean_dec(v_cFileName_x3f_2789_);
lean_dec_ref(v_leanOpts_2775_);
v___y_2739_ = v_a_2832_;
goto v___jp_2738_;
}
}
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
lean_dec(v_mainModuleName_2828_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2823_);
lean_dec(v_bcFileName_x3f_2790_);
lean_dec(v_cFileName_x3f_2789_);
lean_dec_ref(v_leanOpts_2775_);
v_a_2899_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2831_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2831_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
v___jp_2907_:
{
if (lean_obj_tag(v___y_2913_) == 0)
{
lean_object* v_a_2914_; 
v_a_2914_ = lean_ctor_get(v___y_2913_, 0);
lean_inc(v_a_2914_);
lean_dec_ref(v___y_2913_);
v___y_2823_ = v___y_2908_;
v___y_2824_ = v___y_2909_;
v___y_2825_ = v___y_2910_;
v___y_2826_ = v___y_2912_;
v___y_2827_ = v___y_2911_;
v_mainModuleName_2828_ = v_a_2914_;
goto v___jp_2822_;
}
else
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec_ref(v_errorOnKinds_2792_);
lean_dec(v_bcFileName_x3f_2790_);
lean_dec(v_cFileName_x3f_2789_);
lean_dec(v_ileanFileName_x3f_2788_);
lean_dec(v_oleanFileName_x3f_2787_);
lean_dec_ref(v_leanOpts_2775_);
v_a_2915_ = lean_ctor_get(v___y_2913_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___y_2913_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___y_2913_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___y_2913_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
v___jp_2923_:
{
if (lean_obj_tag(v_setupFileName_x3f_2786_) == 0)
{
lean_object* v___x_2929_; 
v___x_2929_ = lean_box(0);
if (lean_obj_tag(v___y_2927_) == 1)
{
lean_object* v_val_2930_; lean_object* v___x_2931_; 
v_val_2930_ = lean_ctor_get(v___y_2927_, 0);
lean_inc(v_val_2930_);
lean_dec_ref(v___y_2927_);
v___x_2931_ = l_Lean_moduleNameOfFileName(v_val_2930_, v_rootDir_x3f_2785_);
if (lean_obj_tag(v___x_2931_) == 0)
{
v___y_2908_ = v___y_2924_;
v___y_2909_ = v___x_2929_;
v___y_2910_ = v_contents_2928_;
v___y_2911_ = v___y_2926_;
v___y_2912_ = v___y_2925_;
v___y_2913_ = v___x_2931_;
goto v___jp_2907_;
}
else
{
if (lean_obj_tag(v_oleanFileName_x3f_2787_) == 0)
{
if (lean_obj_tag(v_cFileName_x3f_2789_) == 0)
{
lean_object* v___x_2932_; 
lean_dec_ref(v___x_2931_);
v___x_2932_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__19));
v___y_2823_ = v___y_2924_;
v___y_2824_ = v___x_2929_;
v___y_2825_ = v_contents_2928_;
v___y_2826_ = v___y_2925_;
v___y_2827_ = v___y_2926_;
v_mainModuleName_2828_ = v___x_2932_;
goto v___jp_2822_;
}
else
{
v___y_2908_ = v___y_2924_;
v___y_2909_ = v___x_2929_;
v___y_2910_ = v_contents_2928_;
v___y_2911_ = v___y_2926_;
v___y_2912_ = v___y_2925_;
v___y_2913_ = v___x_2931_;
goto v___jp_2907_;
}
}
else
{
v___y_2908_ = v___y_2924_;
v___y_2909_ = v___x_2929_;
v___y_2910_ = v_contents_2928_;
v___y_2911_ = v___y_2926_;
v___y_2912_ = v___y_2925_;
v___y_2913_ = v___x_2931_;
goto v___jp_2907_;
}
}
}
else
{
lean_object* v___x_2933_; 
lean_dec(v___y_2927_);
lean_dec(v_rootDir_x3f_2785_);
v___x_2933_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__19));
v___y_2823_ = v___y_2924_;
v___y_2824_ = v___x_2929_;
v___y_2825_ = v_contents_2928_;
v___y_2826_ = v___y_2925_;
v___y_2827_ = v___y_2926_;
v_mainModuleName_2828_ = v___x_2933_;
goto v___jp_2822_;
}
}
else
{
lean_object* v_val_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2952_; 
lean_dec(v___y_2927_);
lean_dec(v_rootDir_x3f_2785_);
v_val_2934_ = lean_ctor_get(v_setupFileName_x3f_2786_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v_setupFileName_x3f_2786_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2936_ = v_setupFileName_x3f_2786_;
v_isShared_2937_ = v_isSharedCheck_2952_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_val_2934_);
lean_dec(v_setupFileName_x3f_2786_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2952_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2938_; 
v___x_2938_ = l_Lean_ModuleSetup_load(v_val_2934_);
lean_dec(v_val_2934_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v_name_2940_; lean_object* v___x_2942_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref(v___x_2938_);
v_name_2940_ = lean_ctor_get(v_a_2939_, 0);
lean_inc(v_name_2940_);
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 0, v_a_2939_);
v___x_2942_ = v___x_2936_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2939_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
v___y_2823_ = v___y_2924_;
v___y_2824_ = v___x_2942_;
v___y_2825_ = v_contents_2928_;
v___y_2826_ = v___y_2925_;
v___y_2827_ = v___y_2926_;
v_mainModuleName_2828_ = v_name_2940_;
goto v___jp_2822_;
}
}
else
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2951_; 
lean_del_object(v___x_2936_);
lean_dec_ref(v_contents_2928_);
lean_dec_ref(v___y_2926_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec_ref(v_errorOnKinds_2792_);
lean_dec(v_bcFileName_x3f_2790_);
lean_dec(v_cFileName_x3f_2789_);
lean_dec(v_ileanFileName_x3f_2788_);
lean_dec(v_oleanFileName_x3f_2787_);
lean_dec_ref(v_leanOpts_2775_);
v_a_2944_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2946_ = v___x_2938_;
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2938_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2949_; 
if (v_isShared_2947_ == 0)
{
v___x_2949_ = v___x_2946_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2944_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
}
}
v___jp_2953_:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; uint8_t v___x_2966_; 
v___x_2962_ = lean_nat_add(v_startInclusive_2956_, v___y_2961_);
lean_dec(v___y_2961_);
lean_inc(v___x_2962_);
lean_inc_ref(v_str_2955_);
v___x_2963_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2963_, 0, v_str_2955_);
lean_ctor_set(v___x_2963_, 1, v_startInclusive_2956_);
lean_ctor_set(v___x_2963_, 2, v___x_2962_);
v___x_2964_ = l_String_Slice_trimAscii(v___x_2963_);
v___x_2965_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__22, &l___private_Lean_Shell_0__Lean_shellMain___closed__22_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__22);
v___x_2966_ = l_String_Slice_beq(v___x_2964_, v___x_2965_);
if (v___x_2966_ == 0)
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
lean_dec(v___x_2962_);
lean_dec(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v_endExclusive_2957_);
lean_dec_ref(v_str_2955_);
lean_dec_ref(v___y_2954_);
lean_dec_ref(v_errorOnKinds_2792_);
lean_dec(v_bcFileName_x3f_2790_);
lean_dec(v_cFileName_x3f_2789_);
lean_dec(v_ileanFileName_x3f_2788_);
lean_dec(v_oleanFileName_x3f_2787_);
lean_dec(v_setupFileName_x3f_2786_);
lean_dec(v_rootDir_x3f_2785_);
lean_dec_ref(v_leanOpts_2775_);
v___x_2967_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__23));
v___x_2968_ = l_String_Slice_toString(v___x_2964_);
lean_dec_ref(v___x_2964_);
v___x_2969_ = lean_string_append(v___x_2967_, v___x_2968_);
lean_dec_ref(v___x_2968_);
v___x_2970_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
v___x_2971_ = lean_string_append(v___x_2969_, v___x_2970_);
v___x_2972_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_2971_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2980_; 
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_2980_ == 0)
{
lean_object* v_unused_2981_; 
v_unused_2981_ = lean_ctor_get(v___x_2972_, 0);
lean_dec(v_unused_2981_);
v___x_2974_ = v___x_2972_;
v_isShared_2975_ = v_isSharedCheck_2980_;
goto v_resetjp_2973_;
}
else
{
lean_dec(v___x_2972_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2980_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2976_; lean_object* v___x_2978_; 
v___x_2976_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 0, v___x_2976_);
v___x_2978_ = v___x_2974_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2976_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
else
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2989_; 
v_a_2982_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2984_ = v___x_2972_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2972_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2982_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
else
{
lean_object* v___x_2990_; 
lean_dec_ref(v___x_2964_);
v___x_2990_ = lean_string_utf8_extract(v_str_2955_, v___x_2962_, v_endExclusive_2957_);
lean_dec(v_endExclusive_2957_);
lean_dec(v___x_2962_);
lean_dec_ref(v_str_2955_);
v___y_2924_ = v___y_2954_;
v___y_2925_ = v___y_2959_;
v___y_2926_ = v___y_2958_;
v___y_2927_ = v___y_2960_;
v_contents_2928_ = v___x_2990_;
goto v___jp_2923_;
}
}
v___jp_2991_:
{
if (lean_obj_tag(v___y_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v___x_2997_; 
v_a_2996_ = lean_ctor_get(v___y_2995_, 0);
lean_inc(v_a_2996_);
lean_dec_ref(v___y_2995_);
v___x_2997_ = lean_decode_lossy_utf8(v_a_2996_);
lean_dec(v_a_2996_);
if (v_onlyDeps_2781_ == 0)
{
if (v_onlySrcDeps_2782_ == 0)
{
lean_object* v___x_2998_; 
lean_inc_ref(v___x_2997_);
v___x_2998_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v___x_2997_);
if (lean_obj_tag(v___x_2998_) == 1)
{
lean_object* v_val_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
lean_dec_ref(v___x_2997_);
v_val_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_val_2999_);
lean_dec_ref(v___x_2998_);
v___x_3000_ = lean_unsigned_to_nat(0u);
v___x_3001_ = lean_box(0);
v___x_3002_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_2999_, v___x_3000_, v___x_3001_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_str_3003_; lean_object* v_startInclusive_3004_; lean_object* v_endExclusive_3005_; lean_object* v___x_3006_; 
v_str_3003_ = lean_ctor_get(v_val_2999_, 0);
lean_inc_ref(v_str_3003_);
v_startInclusive_3004_ = lean_ctor_get(v_val_2999_, 1);
lean_inc(v_startInclusive_3004_);
v_endExclusive_3005_ = lean_ctor_get(v_val_2999_, 2);
lean_inc(v_endExclusive_3005_);
lean_dec(v_val_2999_);
v___x_3006_ = lean_nat_sub(v_endExclusive_3005_, v_startInclusive_3004_);
lean_inc_ref(v___y_2994_);
v___y_2954_ = v___y_2994_;
v_str_2955_ = v_str_3003_;
v_startInclusive_2956_ = v_startInclusive_3004_;
v_endExclusive_2957_ = v_endExclusive_3005_;
v___y_2958_ = v___y_2994_;
v___y_2959_ = v___y_2992_;
v___y_2960_ = v___y_2993_;
v___y_2961_ = v___x_3006_;
goto v___jp_2953_;
}
else
{
lean_object* v_val_3007_; lean_object* v_str_3008_; lean_object* v_startInclusive_3009_; lean_object* v_endExclusive_3010_; 
v_val_3007_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_val_3007_);
lean_dec_ref(v___x_3002_);
v_str_3008_ = lean_ctor_get(v_val_2999_, 0);
lean_inc_ref(v_str_3008_);
v_startInclusive_3009_ = lean_ctor_get(v_val_2999_, 1);
lean_inc(v_startInclusive_3009_);
v_endExclusive_3010_ = lean_ctor_get(v_val_2999_, 2);
lean_inc(v_endExclusive_3010_);
lean_dec(v_val_2999_);
lean_inc_ref(v___y_2994_);
v___y_2954_ = v___y_2994_;
v_str_2955_ = v_str_3008_;
v_startInclusive_2956_ = v_startInclusive_3009_;
v_endExclusive_2957_ = v_endExclusive_3010_;
v___y_2958_ = v___y_2994_;
v___y_2959_ = v___y_2992_;
v___y_2960_ = v___y_2993_;
v___y_2961_ = v_val_3007_;
goto v___jp_2953_;
}
}
else
{
lean_dec(v___x_2998_);
lean_inc_ref(v___y_2994_);
v___y_2924_ = v___y_2994_;
v___y_2925_ = v___y_2992_;
v___y_2926_ = v___y_2994_;
v___y_2927_ = v___y_2993_;
v_contents_2928_ = v___x_2997_;
goto v___jp_2923_;
}
}
else
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
lean_dec(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec_ref(v_errorOnKinds_2792_);
lean_dec(v_bcFileName_x3f_2790_);
lean_dec(v_cFileName_x3f_2789_);
lean_dec(v_ileanFileName_x3f_2788_);
lean_dec(v_oleanFileName_x3f_2787_);
lean_dec(v_setupFileName_x3f_2786_);
lean_dec(v_rootDir_x3f_2785_);
lean_dec_ref(v_leanOpts_2775_);
v___x_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3011_, 0, v___y_2994_);
v___x_3012_ = l_Lean_Elab_printImportSrcs(v___x_2997_, v___x_3011_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3020_; 
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3020_ == 0)
{
lean_object* v_unused_3021_; 
v_unused_3021_ = lean_ctor_get(v___x_3012_, 0);
lean_dec(v_unused_3021_);
v___x_3014_ = v___x_3012_;
v_isShared_3015_ = v_isSharedCheck_3020_;
goto v_resetjp_3013_;
}
else
{
lean_dec(v___x_3012_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3020_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3016_; lean_object* v___x_3018_; 
v___x_3016_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3015_ == 0)
{
lean_ctor_set(v___x_3014_, 0, v___x_3016_);
v___x_3018_ = v___x_3014_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_3016_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
v_a_3022_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_3012_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3012_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3022_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
}
}
else
{
lean_object* v___x_3030_; lean_object* v___x_3031_; 
lean_dec(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec_ref(v_errorOnKinds_2792_);
lean_dec(v_bcFileName_x3f_2790_);
lean_dec(v_cFileName_x3f_2789_);
lean_dec(v_ileanFileName_x3f_2788_);
lean_dec(v_oleanFileName_x3f_2787_);
lean_dec(v_setupFileName_x3f_2786_);
lean_dec(v_rootDir_x3f_2785_);
lean_dec_ref(v_leanOpts_2775_);
v___x_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3030_, 0, v___y_2994_);
v___x_3031_ = l_Lean_Elab_printImports(v___x_2997_, v___x_3030_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3039_; 
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3039_ == 0)
{
lean_object* v_unused_3040_; 
v_unused_3040_ = lean_ctor_get(v___x_3031_, 0);
lean_dec(v_unused_3040_);
v___x_3033_ = v___x_3031_;
v_isShared_3034_ = v_isSharedCheck_3039_;
goto v_resetjp_3032_;
}
else
{
lean_dec(v___x_3031_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3039_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3035_; lean_object* v___x_3037_; 
v___x_3035_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 0, v___x_3035_);
v___x_3037_ = v___x_3033_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3035_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
else
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
v_a_3041_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3043_ = v___x_3031_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3031_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
if (v_isShared_3044_ == 0)
{
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3041_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec_ref(v_errorOnKinds_2792_);
lean_dec(v_bcFileName_x3f_2790_);
lean_dec(v_cFileName_x3f_2789_);
lean_dec(v_ileanFileName_x3f_2788_);
lean_dec(v_oleanFileName_x3f_2787_);
lean_dec(v_setupFileName_x3f_2786_);
lean_dec(v_rootDir_x3f_2785_);
lean_dec_ref(v_leanOpts_2775_);
v_a_3049_ = lean_ctor_get(v___y_2995_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___y_2995_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___y_2995_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___y_2995_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
v___jp_3057_:
{
if (v_useStdin_2780_ == 0)
{
lean_object* v___x_3061_; 
v___x_3061_ = l_IO_FS_readBinFile(v_fileName_3060_);
v___y_2992_ = v___y_3058_;
v___y_2993_ = v___y_3059_;
v___y_2994_ = v_fileName_3060_;
v___y_2995_ = v___x_3061_;
goto v___jp_2991_;
}
else
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3062_ = lean_get_stdin();
v___x_3063_ = l_IO_FS_Stream_readBinToEnd(v___x_3062_);
v___y_2992_ = v___y_3058_;
v___y_2993_ = v___y_3059_;
v___y_2994_ = v_fileName_3060_;
v___y_2995_ = v___x_3063_;
goto v___jp_2991_;
}
}
v___jp_3064_:
{
if (lean_obj_tag(v___y_3066_) == 1)
{
lean_object* v_val_3067_; 
v_val_3067_ = lean_ctor_get(v___y_3066_, 0);
lean_inc(v_val_3067_);
v___y_3058_ = v___y_3065_;
v___y_3059_ = v___y_3066_;
v_fileName_3060_ = v_val_3067_;
goto v___jp_3057_;
}
else
{
if (v_useStdin_2780_ == 0)
{
lean_object* v___x_3068_; lean_object* v___x_3069_; 
lean_dec(v___y_3066_);
lean_dec(v___y_3065_);
lean_dec_ref(v_errorOnKinds_2792_);
lean_dec(v_bcFileName_x3f_2790_);
lean_dec(v_cFileName_x3f_2789_);
lean_dec(v_ileanFileName_x3f_2788_);
lean_dec(v_oleanFileName_x3f_2787_);
lean_dec(v_setupFileName_x3f_2786_);
lean_dec(v_rootDir_x3f_2785_);
lean_dec_ref(v_leanOpts_2775_);
v___x_3068_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__24));
v___x_3069_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3068_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_object* v___x_3070_; 
lean_dec_ref(v___x_3069_);
v___x_3070_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_2821_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3078_; 
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3078_ == 0)
{
lean_object* v_unused_3079_; 
v_unused_3079_ = lean_ctor_get(v___x_3070_, 0);
lean_dec(v_unused_3079_);
v___x_3072_ = v___x_3070_;
v_isShared_3073_ = v_isSharedCheck_3078_;
goto v_resetjp_3071_;
}
else
{
lean_dec(v___x_3070_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3078_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3074_; lean_object* v___x_3076_; 
v___x_3074_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v___x_3074_);
v___x_3076_ = v___x_3072_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3074_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
v_a_3080_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3070_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3070_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
v_a_3088_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_3069_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3069_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3088_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
else
{
lean_object* v___x_3096_; 
v___x_3096_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__25));
v___y_3058_ = v___y_3065_;
v___y_3059_ = v___y_3066_;
v_fileName_3060_ = v___x_3096_;
goto v___jp_3057_;
}
}
}
v___jp_3097_:
{
if (v_run_2794_ == 0)
{
uint8_t v___x_3100_; 
v___x_3100_ = l_List_isEmpty___redArg(v_snd_3099_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
lean_dec(v_snd_3099_);
lean_dec(v_fst_3098_);
lean_dec_ref(v_errorOnKinds_2792_);
lean_dec(v_bcFileName_x3f_2790_);
lean_dec(v_cFileName_x3f_2789_);
lean_dec(v_ileanFileName_x3f_2788_);
lean_dec(v_oleanFileName_x3f_2787_);
lean_dec(v_setupFileName_x3f_2786_);
lean_dec(v_rootDir_x3f_2785_);
lean_dec_ref(v_leanOpts_2775_);
v___x_3101_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__24));
v___x_3102_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3101_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v___x_3103_; 
lean_dec_ref(v___x_3102_);
v___x_3103_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_2821_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3111_; 
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3111_ == 0)
{
lean_object* v_unused_3112_; 
v_unused_3112_ = lean_ctor_get(v___x_3103_, 0);
lean_dec(v_unused_3112_);
v___x_3105_ = v___x_3103_;
v_isShared_3106_ = v_isSharedCheck_3111_;
goto v_resetjp_3104_;
}
else
{
lean_dec(v___x_3103_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3111_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3107_; lean_object* v___x_3109_; 
v___x_3107_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 0, v___x_3107_);
v___x_3109_ = v___x_3105_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3107_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
else
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
v_a_3113_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3103_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3103_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3118_; 
if (v_isShared_3116_ == 0)
{
v___x_3118_ = v___x_3115_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
v_a_3121_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3102_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3102_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
else
{
v___y_3065_ = v_snd_3099_;
v___y_3066_ = v_fst_3098_;
goto v___jp_3064_;
}
}
else
{
v___y_3065_ = v_snd_3099_;
v___y_3066_ = v_fst_3098_;
goto v___jp_3064_;
}
}
v___jp_3129_:
{
if (lean_obj_tag(v_args_2732_) == 0)
{
lean_object* v___x_3130_; 
v___x_3130_ = lean_box(0);
v_fst_3098_ = v___x_3130_;
v_snd_3099_ = v_args_2732_;
goto v___jp_3097_;
}
else
{
lean_object* v_head_3131_; lean_object* v_tail_3132_; lean_object* v___x_3133_; 
v_head_3131_ = lean_ctor_get(v_args_2732_, 0);
lean_inc(v_head_3131_);
v_tail_3132_ = lean_ctor_get(v_args_2732_, 1);
lean_inc(v_tail_3132_);
lean_dec_ref(v_args_2732_);
v___x_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3133_, 0, v_head_3131_);
v_fst_3098_ = v___x_3133_;
v_snd_3099_ = v_tail_3132_;
goto v___jp_3097_;
}
}
v___jp_3134_:
{
switch(v_component_2777_)
{
case 0:
{
lean_dec_ref(v_forwardedArgs_2776_);
if (v_onlyDeps_2781_ == 0)
{
goto v___jp_3129_;
}
else
{
if (v_depsJson_2783_ == 0)
{
goto v___jp_3129_;
}
else
{
lean_dec_ref(v_errorOnKinds_2792_);
lean_dec(v_bcFileName_x3f_2790_);
lean_dec(v_cFileName_x3f_2789_);
lean_dec(v_ileanFileName_x3f_2788_);
lean_dec(v_oleanFileName_x3f_2787_);
lean_dec(v_setupFileName_x3f_2786_);
lean_dec(v_rootDir_x3f_2785_);
lean_dec_ref(v_leanOpts_2775_);
if (v_useStdin_2780_ == 0)
{
lean_object* v___x_3135_; 
v___x_3135_ = lean_array_mk(v_args_2732_);
v_fns_2756_ = v___x_3135_;
goto v___jp_2755_;
}
else
{
lean_object* v___x_3136_; lean_object* v___x_3137_; 
lean_dec(v_args_2732_);
v___x_3136_ = lean_get_stdin();
v___x_3137_ = l_IO_FS_Stream_lines(v___x_3136_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_a_3138_);
lean_dec_ref(v___x_3137_);
v_fns_2756_ = v_a_3138_;
goto v___jp_2755_;
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
v_a_3139_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3137_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3137_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v___x_3147_; lean_object* v___x_3148_; 
lean_dec_ref(v_errorOnKinds_2792_);
lean_dec(v_bcFileName_x3f_2790_);
lean_dec(v_cFileName_x3f_2789_);
lean_dec(v_ileanFileName_x3f_2788_);
lean_dec(v_oleanFileName_x3f_2787_);
lean_dec(v_setupFileName_x3f_2786_);
lean_dec(v_rootDir_x3f_2785_);
lean_dec_ref(v_leanOpts_2775_);
lean_dec(v_args_2732_);
v___x_3147_ = lean_array_to_list(v_forwardedArgs_2776_);
v___x_3148_ = l_Lean_Server_Watchdog_watchdogMain(v___x_3147_);
return v___x_3148_;
}
default: 
{
lean_object* v___x_3149_; 
lean_dec_ref(v_errorOnKinds_2792_);
lean_dec(v_bcFileName_x3f_2790_);
lean_dec(v_cFileName_x3f_2789_);
lean_dec(v_ileanFileName_x3f_2788_);
lean_dec(v_oleanFileName_x3f_2787_);
lean_dec(v_setupFileName_x3f_2786_);
lean_dec(v_rootDir_x3f_2785_);
lean_dec_ref(v_forwardedArgs_2776_);
lean_dec(v_args_2732_);
v___x_3149_ = l_Lean_Server_FileWorker_workerMain(v_leanOpts_2775_);
return v___x_3149_;
}
}
}
v___jp_3150_:
{
lean_object* v___x_3151_; lean_object* v_timeout_3152_; lean_object* v___x_3153_; uint8_t v___x_3154_; 
v___x_3151_ = l___private_Lean_Shell_0__Lean_timeout;
v_timeout_3152_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_leanOpts_2775_, v___x_3151_);
v___x_3153_ = lean_unsigned_to_nat(0u);
v___x_3154_ = lean_nat_dec_eq(v_timeout_3152_, v___x_3153_);
if (v___x_3154_ == 0)
{
size_t v___x_3155_; size_t v___x_3156_; size_t v___x_3157_; lean_object* v___x_3158_; 
v___x_3155_ = lean_usize_of_nat(v_timeout_3152_);
lean_dec(v_timeout_3152_);
v___x_3156_ = ((size_t)1000ULL);
v___x_3157_ = lean_usize_mul(v___x_3155_, v___x_3156_);
v___x_3158_ = lean_internal_set_max_heartbeat(v___x_3157_);
goto v___jp_3134_;
}
else
{
lean_dec(v_timeout_3152_);
goto v___jp_3134_;
}
}
}
else
{
lean_object* v___x_3168_; 
lean_dec_ref(v_errorOnKinds_2792_);
lean_dec(v_bcFileName_x3f_2790_);
lean_dec(v_cFileName_x3f_2789_);
lean_dec(v_ileanFileName_x3f_2788_);
lean_dec(v_oleanFileName_x3f_2787_);
lean_dec(v_setupFileName_x3f_2786_);
lean_dec(v_rootDir_x3f_2785_);
lean_dec_ref(v_forwardedArgs_2776_);
lean_dec_ref(v_leanOpts_2775_);
lean_dec(v_args_2732_);
v___x_3168_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v_a_3169_; lean_object* v___x_3170_; 
v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
lean_inc(v_a_3169_);
lean_dec_ref(v___x_3168_);
v___x_3170_ = l_Lean_getLibDir(v_a_3169_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_object* v_a_3171_; lean_object* v___x_3172_; 
v_a_3171_ = lean_ctor_get(v___x_3170_, 0);
lean_inc(v_a_3171_);
lean_dec_ref(v___x_3170_);
v___x_3172_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3171_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3180_; 
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3180_ == 0)
{
lean_object* v_unused_3181_; 
v_unused_3181_ = lean_ctor_get(v___x_3172_, 0);
lean_dec(v_unused_3181_);
v___x_3174_ = v___x_3172_;
v_isShared_3175_ = v_isSharedCheck_3180_;
goto v_resetjp_3173_;
}
else
{
lean_dec(v___x_3172_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3180_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3176_; lean_object* v___x_3178_; 
v___x_3176_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 0, v___x_3176_);
v___x_3178_ = v___x_3174_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3176_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
v_a_3182_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3172_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3172_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
v_a_3190_ = lean_ctor_get(v___x_3170_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3170_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3170_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
else
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
v_a_3198_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3168_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3168_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
}
else
{
lean_object* v___x_3206_; 
lean_dec_ref(v_errorOnKinds_2792_);
lean_dec(v_bcFileName_x3f_2790_);
lean_dec(v_cFileName_x3f_2789_);
lean_dec(v_ileanFileName_x3f_2788_);
lean_dec(v_oleanFileName_x3f_2787_);
lean_dec(v_setupFileName_x3f_2786_);
lean_dec(v_rootDir_x3f_2785_);
lean_dec_ref(v_forwardedArgs_2776_);
lean_dec_ref(v_leanOpts_2775_);
lean_dec(v_args_2732_);
v___x_3206_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v_a_3207_; lean_object* v___x_3208_; 
v_a_3207_ = lean_ctor_get(v___x_3206_, 0);
lean_inc(v_a_3207_);
lean_dec_ref(v___x_3206_);
v___x_3208_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3207_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3216_; 
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3216_ == 0)
{
lean_object* v_unused_3217_; 
v_unused_3217_ = lean_ctor_get(v___x_3208_, 0);
lean_dec(v_unused_3217_);
v___x_3210_ = v___x_3208_;
v_isShared_3211_ = v_isSharedCheck_3216_;
goto v_resetjp_3209_;
}
else
{
lean_dec(v___x_3208_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3216_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3212_; lean_object* v___x_3214_; 
v___x_3212_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 0, v___x_3212_);
v___x_3214_ = v___x_3210_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3212_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
else
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
v_a_3218_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___x_3208_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3208_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
v_a_3226_ = lean_ctor_get(v___x_3206_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3206_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3206_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3226_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
v___jp_2735_:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2736_);
return v___x_2737_;
}
v___jp_2738_:
{
lean_object* v___x_2740_; uint8_t v___x_2741_; 
v___x_2740_ = lean_display_cumulative_profiling_times();
v___x_2741_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__0, &l___private_Lean_Shell_0__Lean_shellMain___closed__0_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__0);
if (v___x_2741_ == 0)
{
if (lean_obj_tag(v___y_2739_) == 0)
{
uint8_t v___x_2742_; lean_object* v___x_2743_; 
v___x_2742_ = 1;
v___x_2743_ = lean_io_exit(v___x_2742_);
return v___x_2743_;
}
else
{
uint8_t v___x_2744_; lean_object* v___x_2745_; 
lean_dec_ref(v___y_2739_);
v___x_2744_ = 0;
v___x_2745_ = lean_io_exit(v___x_2744_);
return v___x_2745_;
}
}
else
{
if (lean_obj_tag(v___y_2739_) == 0)
{
goto v___jp_2735_;
}
else
{
lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2753_; 
v_isSharedCheck_2753_ = !lean_is_exclusive(v___y_2739_);
if (v_isSharedCheck_2753_ == 0)
{
lean_object* v_unused_2754_; 
v_unused_2754_ = lean_ctor_get(v___y_2739_, 0);
lean_dec(v_unused_2754_);
v___x_2747_ = v___y_2739_;
v_isShared_2748_ = v_isSharedCheck_2753_;
goto v_resetjp_2746_;
}
else
{
lean_dec(v___y_2739_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2753_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
if (v___x_2741_ == 0)
{
lean_del_object(v___x_2747_);
goto v___jp_2735_;
}
else
{
lean_object* v___x_2749_; lean_object* v___x_2751_; 
v___x_2749_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2748_ == 0)
{
lean_ctor_set_tag(v___x_2747_, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2749_);
v___x_2751_ = v___x_2747_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___x_2749_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
}
}
v___jp_2755_:
{
lean_object* v___x_2757_; 
v___x_2757_ = l_Lean_printImportsJson(v_fns_2756_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2765_; 
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2765_ == 0)
{
lean_object* v_unused_2766_; 
v_unused_2766_ = lean_ctor_get(v___x_2757_, 0);
lean_dec(v_unused_2766_);
v___x_2759_ = v___x_2757_;
v_isShared_2760_ = v_isSharedCheck_2765_;
goto v_resetjp_2758_;
}
else
{
lean_dec(v___x_2757_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2765_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2761_; lean_object* v___x_2763_; 
v___x_2761_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 0, v___x_2761_);
v___x_2763_ = v___x_2759_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2761_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
v_a_2767_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2757_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2757_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
v___jp_2795_:
{
if (lean_obj_tag(v_bcFileName_x3f_2790_) == 1)
{
lean_object* v_val_2799_; lean_object* v___x_2800_; 
v_val_2799_ = lean_ctor_get(v_bcFileName_x3f_2790_, 0);
lean_inc(v_val_2799_);
lean_dec_ref(v_bcFileName_x3f_2790_);
v___x_2800_ = lean_init_llvm();
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
lean_dec_ref(v___x_2800_);
v___x_2801_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__1));
v___x_2802_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_emitLLVM___boxed), 4, 3);
lean_closure_set(v___x_2802_, 0, v___y_2798_);
lean_closure_set(v___x_2802_, 1, v___y_2796_);
lean_closure_set(v___x_2802_, 2, v_val_2799_);
v___x_2803_ = lean_box(0);
v___x_2804_ = l_Lean_profileitIOUnsafe___redArg(v___x_2801_, v_leanOpts_2775_, v___x_2802_, v___x_2803_);
lean_dec_ref(v_leanOpts_2775_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_dec_ref(v___x_2804_);
v___y_2739_ = v___y_2797_;
goto v___jp_2738_;
}
else
{
lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2812_; 
lean_dec(v___y_2797_);
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2807_ = v___x_2804_;
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2804_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2810_; 
if (v_isShared_2808_ == 0)
{
v___x_2810_ = v___x_2807_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2805_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
lean_dec(v_val_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v_leanOpts_2775_);
v_a_2813_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2800_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2800_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
else
{
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2796_);
lean_dec(v_bcFileName_x3f_2790_);
lean_dec_ref(v_leanOpts_2775_);
v___y_2739_ = v___y_2797_;
goto v___jp_2738_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object* v_args_3234_, lean_object* v_opts_3235_, lean_object* v_a_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = lean_shell_main(v_args_3234_, v_opts_3235_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(lean_object* v_val_3238_, lean_object* v_inst_3239_, lean_object* v_R_3240_, lean_object* v_a_3241_, lean_object* v_b_3242_, lean_object* v_c_3243_){
_start:
{
lean_object* v___x_3244_; 
v___x_3244_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3238_, v_a_3241_, v_b_3242_);
return v___x_3244_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___boxed(lean_object* v_val_3245_, lean_object* v_inst_3246_, lean_object* v_R_3247_, lean_object* v_a_3248_, lean_object* v_b_3249_, lean_object* v_c_3250_){
_start:
{
lean_object* v_res_3251_; 
v_res_3251_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(v_val_3245_, v_inst_3246_, v_R_3247_, v_a_3248_, v_b_3249_, v_c_3250_);
lean_dec_ref(v_val_3245_);
return v_res_3251_;
}
}
lean_object* runtime_initialize_Lean_Elab_Frontend(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ParseImportsFast(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Watchdog(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_FileWorker(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_EmitC(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Shell(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
