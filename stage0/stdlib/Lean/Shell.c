// Lean compiler output
// Module: Lean.Shell
// Imports: import Lean.Elab.Frontend import Lean.Elab.ParseImportsFast import Lean.Server.Watchdog import Lean.Server.FileWorker import Lean.Compiler.LCNF.EmitC import Init.System.Platform import Lean.Compiler.Options
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
extern lean_object* l_Lean_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
lean_object* l_IO_eprint___redArg(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stderr();
uint32_t lean_internal_get_hardware_concurrency(lean_object*);
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
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
uint32_t lean_uint32_add(uint32_t, uint32_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* lean_io_exit(uint8_t);
lean_object* lean_display_cumulative_profiling_times();
lean_object* l_Lean_printImportsJson(lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_runFrontend(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedFileMap_default;
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "#lang"};
static const lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0 = (const lean_object*)&l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object**);
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
static const lean_array_object l___private_Lean_Shell_0__Lean_shellMain___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__2 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__2_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "C code generation"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__3 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__3_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__4;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__5;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__6 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__6_value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_shellMain___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__6_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__7 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__7_value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_shellMain___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__8 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__8_value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_shellMain___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__9 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__9_value;
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
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__17;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "failed to create '"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__18 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__18_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_stdin"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__19 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__19_value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_shellMain___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__19_value),LEAN_SCALAR_PTR_LITERAL(37, 142, 62, 167, 41, 238, 22, 79)}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__20 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__20_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "lean4"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__21 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__21_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__22;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__23;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unknown language '"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__24 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__24_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Expected exactly one file name"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__25 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__25_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "<stdin>"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__26 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__26_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx(uint8_t v_x_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(v_x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx___boxed(lean_object* v_x_305_){
_start:
{
uint8_t v_x_4__boxed_306_; lean_object* v_res_307_; 
v_x_4__boxed_306_ = lean_unbox(v_x_305_);
v_res_307_ = l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx(v_x_4__boxed_306_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg(lean_object* v_k_308_){
_start:
{
lean_inc(v_k_308_);
return v_k_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg___boxed(lean_object* v_k_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg(v_k_309_);
lean_dec(v_k_309_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim(lean_object* v_motive_311_, lean_object* v_ctorIdx_312_, uint8_t v_t_313_, lean_object* v_h_314_, lean_object* v_k_315_){
_start:
{
lean_inc(v_k_315_);
return v_k_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___boxed(lean_object* v_motive_316_, lean_object* v_ctorIdx_317_, lean_object* v_t_318_, lean_object* v_h_319_, lean_object* v_k_320_){
_start:
{
uint8_t v_t_boxed_321_; lean_object* v_res_322_; 
v_t_boxed_321_ = lean_unbox(v_t_318_);
v_res_322_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim(v_motive_316_, v_ctorIdx_317_, v_t_boxed_321_, v_h_319_, v_k_320_);
lean_dec(v_k_320_);
lean_dec(v_ctorIdx_317_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg(lean_object* v_frontend_323_){
_start:
{
lean_inc(v_frontend_323_);
return v_frontend_323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg___boxed(lean_object* v_frontend_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg(v_frontend_324_);
lean_dec(v_frontend_324_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim(lean_object* v_motive_326_, uint8_t v_t_327_, lean_object* v_h_328_, lean_object* v_frontend_329_){
_start:
{
lean_inc(v_frontend_329_);
return v_frontend_329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___boxed(lean_object* v_motive_330_, lean_object* v_t_331_, lean_object* v_h_332_, lean_object* v_frontend_333_){
_start:
{
uint8_t v_t_boxed_334_; lean_object* v_res_335_; 
v_t_boxed_334_ = lean_unbox(v_t_331_);
v_res_335_ = l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim(v_motive_330_, v_t_boxed_334_, v_h_332_, v_frontend_333_);
lean_dec(v_frontend_333_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg(lean_object* v_watchdog_336_){
_start:
{
lean_inc(v_watchdog_336_);
return v_watchdog_336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg___boxed(lean_object* v_watchdog_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg(v_watchdog_337_);
lean_dec(v_watchdog_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim(lean_object* v_motive_339_, uint8_t v_t_340_, lean_object* v_h_341_, lean_object* v_watchdog_342_){
_start:
{
lean_inc(v_watchdog_342_);
return v_watchdog_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___boxed(lean_object* v_motive_343_, lean_object* v_t_344_, lean_object* v_h_345_, lean_object* v_watchdog_346_){
_start:
{
uint8_t v_t_boxed_347_; lean_object* v_res_348_; 
v_t_boxed_347_ = lean_unbox(v_t_344_);
v_res_348_ = l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim(v_motive_343_, v_t_boxed_347_, v_h_345_, v_watchdog_346_);
lean_dec(v_watchdog_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg(lean_object* v_worker_349_){
_start:
{
lean_inc(v_worker_349_);
return v_worker_349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg___boxed(lean_object* v_worker_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg(v_worker_350_);
lean_dec(v_worker_350_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim(lean_object* v_motive_352_, uint8_t v_t_353_, lean_object* v_h_354_, lean_object* v_worker_355_){
_start:
{
lean_inc(v_worker_355_);
return v_worker_355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___boxed(lean_object* v_motive_356_, lean_object* v_t_357_, lean_object* v_h_358_, lean_object* v_worker_359_){
_start:
{
uint8_t v_t_boxed_360_; lean_object* v_res_361_; 
v_t_boxed_360_ = lean_unbox(v_t_357_);
v_res_361_ = l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim(v_motive_356_, v_t_boxed_360_, v_h_358_, v_worker_359_);
lean_dec(v_worker_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(lean_object* v_name_362_, lean_object* v_decl_363_, lean_object* v_ref_364_){
_start:
{
lean_object* v_defValue_366_; lean_object* v_descr_367_; lean_object* v_deprecation_x3f_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_defValue_366_ = lean_ctor_get(v_decl_363_, 0);
v_descr_367_ = lean_ctor_get(v_decl_363_, 1);
v_deprecation_x3f_368_ = lean_ctor_get(v_decl_363_, 2);
lean_inc(v_defValue_366_);
v___x_369_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_369_, 0, v_defValue_366_);
lean_inc(v_deprecation_x3f_368_);
lean_inc_ref(v_descr_367_);
lean_inc_n(v_name_362_, 2);
v___x_370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_370_, 0, v_name_362_);
lean_ctor_set(v___x_370_, 1, v_ref_364_);
lean_ctor_set(v___x_370_, 2, v___x_369_);
lean_ctor_set(v___x_370_, 3, v_descr_367_);
lean_ctor_set(v___x_370_, 4, v_deprecation_x3f_368_);
v___x_371_ = lean_register_option(v_name_362_, v___x_370_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_379_; 
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; 
v_unused_380_ = lean_ctor_get(v___x_371_, 0);
lean_dec(v_unused_380_);
v___x_373_ = v___x_371_;
v_isShared_374_ = v_isSharedCheck_379_;
goto v_resetjp_372_;
}
else
{
lean_dec(v___x_371_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_379_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; lean_object* v___x_377_; 
lean_inc(v_defValue_366_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v_name_362_);
lean_ctor_set(v___x_375_, 1, v_defValue_366_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_375_);
v___x_377_ = v___x_373_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec(v_name_362_);
v_a_381_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_371_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_371_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0___boxed(lean_object* v_name_389_, lean_object* v_decl_390_, lean_object* v_ref_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v_name_389_, v_decl_390_, v_ref_391_);
lean_dec_ref(v_decl_390_);
return v_res_393_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_box(0);
v___x_398_ = lean_internal_get_default_max_memory(v___x_397_);
return v___x_398_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_399_ = lean_box(0);
v___x_400_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_401_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
v___x_402_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v___x_400_);
lean_ctor_set(v___x_402_, 2, v___x_399_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_426_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_));
v___x_427_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
v___x_428_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__13_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_));
v___x_429_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v___x_426_, v___x_427_, v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2____boxed(lean_object* v_a_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
return v_res_431_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_box(0);
v___x_436_ = lean_internal_get_default_max_heartbeat(v___x_435_);
return v___x_436_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_437_ = lean_box(0);
v___x_438_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_439_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
v___x_440_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v___x_438_);
lean_ctor_set(v___x_440_, 2, v___x_437_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_445_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_));
v___x_446_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
v___x_447_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_));
v___x_448_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v___x_445_, v___x_446_, v___x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2____boxed(lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_();
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(lean_object* v_name_451_, lean_object* v_decl_452_, lean_object* v_ref_453_){
_start:
{
lean_object* v_defValue_455_; lean_object* v_descr_456_; lean_object* v_deprecation_x3f_457_; lean_object* v___x_458_; uint8_t v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v_defValue_455_ = lean_ctor_get(v_decl_452_, 0);
v_descr_456_ = lean_ctor_get(v_decl_452_, 1);
v_deprecation_x3f_457_ = lean_ctor_get(v_decl_452_, 2);
v___x_458_ = lean_alloc_ctor(1, 0, 1);
v___x_459_ = lean_unbox(v_defValue_455_);
lean_ctor_set_uint8(v___x_458_, 0, v___x_459_);
lean_inc(v_deprecation_x3f_457_);
lean_inc_ref(v_descr_456_);
lean_inc_n(v_name_451_, 2);
v___x_460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_460_, 0, v_name_451_);
lean_ctor_set(v___x_460_, 1, v_ref_453_);
lean_ctor_set(v___x_460_, 2, v___x_458_);
lean_ctor_set(v___x_460_, 3, v_descr_456_);
lean_ctor_set(v___x_460_, 4, v_deprecation_x3f_457_);
v___x_461_ = lean_register_option(v_name_451_, v___x_460_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_469_; 
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; 
v_unused_470_ = lean_ctor_get(v___x_461_, 0);
lean_dec(v_unused_470_);
v___x_463_ = v___x_461_;
v_isShared_464_ = v_isSharedCheck_469_;
goto v_resetjp_462_;
}
else
{
lean_dec(v___x_461_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_469_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_467_; 
lean_inc(v_defValue_455_);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v_name_451_);
lean_ctor_set(v___x_465_, 1, v_defValue_455_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___x_465_);
v___x_467_ = v___x_463_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_dec(v_name_451_);
v_a_471_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_461_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_461_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0___boxed(lean_object* v_name_479_, lean_object* v_decl_480_, lean_object* v_ref_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(v_name_479_, v_decl_480_, v_ref_481_);
lean_dec_ref(v_decl_480_);
return v_res_483_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_487_ = lean_box(0);
v___x_488_ = lean_internal_get_default_verbose(v___x_487_);
return v___x_488_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_489_ = lean_box(0);
v___x_490_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_491_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_);
v___x_492_ = lean_box(v___x_491_);
v___x_493_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
lean_ctor_set(v___x_493_, 1, v___x_490_);
lean_ctor_set(v___x_493_, 2, v___x_489_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_498_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_));
v___x_499_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_);
v___x_500_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_));
v___x_501_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(v___x_498_, v___x_499_, v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2____boxed(lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_();
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultOptions___boxed(lean_object* v_x_00___x40_Lean_Shell_2553953037____hygCtx___hyg_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = lean_internal_get_default_options(v_x_00___x40_Lean_Shell_2553953037____hygCtx___hyg_505_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getBelieverTrustLevel___boxed(lean_object* v_x_00___x40_Lean_Shell_1075205639____hygCtx___hyg_508_){
_start:
{
uint32_t v_res_509_; lean_object* v_r_510_; 
v_res_509_ = lean_internal_get_believer_trust_level(v_x_00___x40_Lean_Shell_1075205639____hygCtx___hyg_508_);
v_r_510_ = lean_box_uint32(v_res_509_);
return v_r_510_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0(void){
_start:
{
lean_object* v___x_511_; uint32_t v___x_512_; 
v___x_511_ = lean_box(0);
v___x_512_ = lean_internal_get_believer_trust_level(v___x_511_);
return v___x_512_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1(void){
_start:
{
uint32_t v___x_513_; uint32_t v___x_514_; uint32_t v___x_515_; 
v___x_513_ = 1;
v___x_514_ = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0, &l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0_once, _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0);
v___x_515_ = lean_uint32_add(v___x_514_, v___x_513_);
return v___x_515_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel(void){
_start:
{
uint32_t v___x_516_; 
v___x_516_ = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1, &l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1_once, _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1);
return v___x_516_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0(void){
_start:
{
lean_object* v___x_517_; uint32_t v___x_518_; 
v___x_517_ = lean_box(0);
v___x_518_ = lean_internal_get_hardware_concurrency(v___x_517_);
return v___x_518_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultNumThreads(void){
_start:
{
uint8_t v___x_519_; 
v___x_519_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__40, &l___private_Lean_Shell_0__Lean_displayHelp___closed__40_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__40);
if (v___x_519_ == 0)
{
uint32_t v___x_520_; 
v___x_520_ = 0;
return v___x_520_;
}
else
{
uint32_t v___x_521_; 
v___x_521_ = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0, &l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0_once, _init_l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0);
return v___x_521_;
}
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_box(0);
v___x_523_ = lean_internal_get_default_options(v___x_522_);
return v___x_523_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2(void){
_start:
{
lean_object* v___x_526_; uint32_t v___x_527_; uint32_t v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; uint8_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_526_ = lean_box(0);
v___x_527_ = l___private_Lean_Shell_0__Lean_defaultNumThreads;
v___x_528_ = l___private_Lean_Shell_0__Lean_defaultTrustLevel;
v___x_529_ = l_Lean_Options_empty;
v___x_530_ = 0;
v___x_531_ = 0;
v___x_532_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1));
v___x_533_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0, &l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0_once, _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0);
v___x_534_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v___x_534_, 0, v___x_533_);
lean_ctor_set(v___x_534_, 1, v___x_532_);
lean_ctor_set(v___x_534_, 2, v___x_529_);
lean_ctor_set(v___x_534_, 3, v___x_526_);
lean_ctor_set(v___x_534_, 4, v___x_526_);
lean_ctor_set(v___x_534_, 5, v___x_526_);
lean_ctor_set(v___x_534_, 6, v___x_526_);
lean_ctor_set(v___x_534_, 7, v___x_526_);
lean_ctor_set(v___x_534_, 8, v___x_526_);
lean_ctor_set(v___x_534_, 9, v___x_532_);
lean_ctor_set(v___x_534_, 10, v___x_526_);
lean_ctor_set(v___x_534_, 11, v___x_526_);
lean_ctor_set(v___x_534_, 12, v___x_526_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*13 + 8, v___x_531_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*13 + 9, v___x_530_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*13 + 10, v___x_530_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*13 + 11, v___x_530_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*13 + 12, v___x_530_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*13 + 13, v___x_530_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*13 + 14, v___x_530_);
lean_ctor_set_uint32(v___x_534_, sizeof(void*)*13, v___x_528_);
lean_ctor_set_uint32(v___x_534_, sizeof(void*)*13 + 4, v___x_527_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*13 + 15, v___x_530_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*13 + 16, v___x_530_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*13 + 17, v___x_530_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* lean_shell_options_mk(lean_object* v_x_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2, &l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2_once, _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2);
return v___x_536_;
}
}
LEAN_EXPORT uint8_t lean_shell_options_get_run(lean_object* v_opts_537_){
_start:
{
uint8_t v_run_538_; 
v_run_538_ = lean_ctor_get_uint8(v_opts_537_, sizeof(void*)*13 + 17);
lean_dec_ref(v_opts_537_);
return v_run_538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getRun___boxed(lean_object* v_opts_539_){
_start:
{
uint8_t v_res_540_; lean_object* v_r_541_; 
v_res_540_ = lean_shell_options_get_run(v_opts_539_);
v_r_541_ = lean_box(v_res_540_);
return v_r_541_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(lean_object* v_opts_542_, lean_object* v_opt_543_){
_start:
{
lean_object* v_name_544_; lean_object* v_defValue_545_; lean_object* v_map_546_; lean_object* v___x_547_; 
v_name_544_ = lean_ctor_get(v_opt_543_, 0);
v_defValue_545_ = lean_ctor_get(v_opt_543_, 1);
v_map_546_ = lean_ctor_get(v_opts_542_, 0);
v___x_547_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_546_, v_name_544_);
if (lean_obj_tag(v___x_547_) == 0)
{
uint8_t v___x_548_; 
v___x_548_ = lean_unbox(v_defValue_545_);
return v___x_548_;
}
else
{
lean_object* v_val_549_; 
v_val_549_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_val_549_);
lean_dec_ref_known(v___x_547_, 1);
if (lean_obj_tag(v_val_549_) == 1)
{
uint8_t v_v_550_; 
v_v_550_ = lean_ctor_get_uint8(v_val_549_, 0);
lean_dec_ref_known(v_val_549_, 0);
return v_v_550_;
}
else
{
uint8_t v___x_551_; 
lean_dec(v_val_549_);
v___x_551_ = lean_unbox(v_defValue_545_);
return v___x_551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0___boxed(lean_object* v_opts_552_, lean_object* v_opt_553_){
_start:
{
uint8_t v_res_554_; lean_object* v_r_555_; 
v_res_554_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v_opts_552_, v_opt_553_);
lean_dec_ref(v_opt_553_);
lean_dec_ref(v_opts_552_);
v_r_555_ = lean_box(v_res_554_);
return v_r_555_;
}
}
LEAN_EXPORT uint8_t lean_shell_options_get_profiler(lean_object* v_opts_556_){
_start:
{
lean_object* v_leanOpts_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v_leanOpts_557_ = lean_ctor_get(v_opts_556_, 0);
lean_inc_ref(v_leanOpts_557_);
lean_dec_ref(v_opts_556_);
v___x_558_ = l_Lean_profiler;
v___x_559_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v_leanOpts_557_, v___x_558_);
lean_dec_ref(v_leanOpts_557_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getProfiler___boxed(lean_object* v_opts_560_){
_start:
{
uint8_t v_res_561_; lean_object* v_r_562_; 
v_res_561_ = lean_shell_options_get_profiler(v_opts_560_);
v_r_562_ = lean_box(v_res_561_);
return v_r_562_;
}
}
LEAN_EXPORT uint32_t lean_shell_options_get_num_threads(lean_object* v_opts_563_){
_start:
{
uint32_t v_numThreads_564_; 
v_numThreads_564_ = lean_ctor_get_uint32(v_opts_563_, sizeof(void*)*13 + 4);
lean_dec_ref(v_opts_563_);
return v_numThreads_564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getNumThreads___boxed(lean_object* v_opts_565_){
_start:
{
uint32_t v_res_566_; lean_object* v_r_567_; 
v_res_566_ = lean_shell_options_get_num_threads(v_opts_565_);
v_r_567_ = lean_box_uint32(v_res_566_);
return v_r_567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_checkOptArg(lean_object* v_optName_570_, lean_object* v_optArg_x3f_571_){
_start:
{
if (lean_obj_tag(v_optArg_x3f_571_) == 1)
{
lean_object* v_val_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
v_val_573_ = lean_ctor_get(v_optArg_x3f_571_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v_optArg_x3f_571_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v_optArg_x3f_571_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_val_573_);
lean_dec(v_optArg_x3f_571_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set_tag(v___x_575_, 0);
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_val_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
lean_dec(v_optArg_x3f_571_);
v___x_581_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__0));
v___x_582_ = lean_string_append(v___x_581_, v_optName_570_);
v___x_583_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__1));
v___x_584_ = lean_string_append(v___x_582_, v___x_583_);
v___x_585_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
v___x_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
return v___x_586_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_checkOptArg___boxed(lean_object* v_optName_587_, lean_object* v_optArg_x3f_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l___private_Lean_Shell_0__Lean_checkOptArg(v_optName_587_, v_optArg_x3f_588_);
lean_dec_ref(v_optName_587_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0(lean_object* v_o_594_, lean_object* v_k_595_, lean_object* v_v_596_){
_start:
{
lean_object* v_map_597_; uint8_t v_hasTrace_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_612_; 
v_map_597_ = lean_ctor_get(v_o_594_, 0);
v_hasTrace_598_ = lean_ctor_get_uint8(v_o_594_, sizeof(void*)*1);
v_isSharedCheck_612_ = !lean_is_exclusive(v_o_594_);
if (v_isSharedCheck_612_ == 0)
{
v___x_600_ = v_o_594_;
v_isShared_601_ = v_isSharedCheck_612_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_map_597_);
lean_dec(v_o_594_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_612_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v_v_596_);
lean_inc(v_k_595_);
v___x_603_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_595_, v___x_602_, v_map_597_);
if (v_hasTrace_598_ == 0)
{
lean_object* v___x_604_; uint8_t v___x_605_; lean_object* v___x_607_; 
v___x_604_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_605_ = l_Lean_Name_isPrefixOf(v___x_604_, v_k_595_);
lean_dec(v_k_595_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_603_);
v___x_607_ = v___x_600_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_603_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_ctor_set_uint8(v___x_607_, sizeof(void*)*1, v___x_605_);
return v___x_607_;
}
}
else
{
lean_object* v___x_610_; 
lean_dec(v_k_595_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_603_);
v___x_610_ = v___x_600_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_603_);
lean_ctor_set_uint8(v_reuseFailAlloc_611_, sizeof(void*)*1, v_hasTrace_598_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(lean_object* v___x_613_, lean_object* v_arg_614_, lean_object* v_a_615_, lean_object* v_b_616_){
_start:
{
lean_object* v_startInclusive_617_; lean_object* v_endExclusive_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v_startInclusive_617_ = lean_ctor_get(v___x_613_, 1);
v_endExclusive_618_ = lean_ctor_get(v___x_613_, 2);
v___x_619_ = lean_nat_sub(v_endExclusive_618_, v_startInclusive_617_);
v___x_620_ = lean_nat_dec_eq(v_a_615_, v___x_619_);
lean_dec(v___x_619_);
if (v___x_620_ == 0)
{
uint32_t v___x_621_; uint32_t v___x_622_; uint8_t v___x_623_; 
v___x_621_ = lean_string_utf8_get_fast(v_arg_614_, v_a_615_);
v___x_622_ = 61;
v___x_623_ = lean_uint32_dec_eq(v___x_621_, v___x_622_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_box(0);
v___x_625_ = lean_string_utf8_next_fast(v_arg_614_, v_a_615_);
lean_dec(v_a_615_);
v_a_615_ = v___x_625_;
v_b_616_ = v___x_624_;
goto _start;
}
else
{
lean_object* v___x_627_; 
v___x_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_627_, 0, v_a_615_);
return v___x_627_;
}
}
else
{
lean_dec(v_a_615_);
lean_inc(v_b_616_);
return v_b_616_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg___boxed(lean_object* v___x_628_, lean_object* v_arg_629_, lean_object* v_a_630_, lean_object* v_b_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_628_, v_arg_629_, v_a_630_, v_b_631_);
lean_dec(v_b_631_);
lean_dec_ref(v_arg_629_);
lean_dec_ref(v___x_628_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_setConfigOption(lean_object* v_opts_636_, lean_object* v_arg_637_){
_start:
{
lean_object* v___y_640_; lean_object* v_searcher_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_searcher_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_string_utf8_byte_size(v_arg_637_);
lean_inc_ref(v_arg_637_);
v___x_673_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_673_, 0, v_arg_637_);
lean_ctor_set(v___x_673_, 1, v_searcher_671_);
lean_ctor_set(v___x_673_, 2, v___x_672_);
v___x_674_ = lean_box(0);
v___x_675_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_673_, v_arg_637_, v_searcher_671_, v___x_674_);
lean_dec_ref_known(v___x_673_, 3);
if (lean_obj_tag(v___x_675_) == 0)
{
v___y_640_ = v___x_672_;
goto v___jp_639_;
}
else
{
lean_object* v_val_676_; 
v_val_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_val_676_);
lean_dec_ref_known(v___x_675_, 1);
v___y_640_ = v_val_676_;
goto v___jp_639_;
}
v___jp_639_:
{
lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_641_ = lean_string_utf8_byte_size(v_arg_637_);
v___x_642_ = lean_nat_dec_eq(v___y_640_, v___x_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_660_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_660_ == 0)
{
v___x_646_ = v___x_643_;
v_isShared_647_ = v_isSharedCheck_660_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_643_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_660_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v_name_651_; lean_object* v_val_652_; lean_object* v___x_653_; 
v___x_648_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_640_);
lean_inc_ref(v_arg_637_);
v___x_649_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_649_, 0, v_arg_637_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
lean_ctor_set(v___x_649_, 2, v___y_640_);
v___x_650_ = lean_string_utf8_next_fast(v_arg_637_, v___y_640_);
lean_dec(v___y_640_);
v_name_651_ = l_String_Slice_toName(v___x_649_);
lean_dec_ref_known(v___x_649_, 3);
v_val_652_ = lean_string_utf8_extract(v_arg_637_, v___x_650_, v___x_641_);
lean_dec_ref(v_arg_637_);
v___x_653_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_644_, v_name_651_);
lean_dec(v_a_644_);
if (lean_obj_tag(v___x_653_) == 1)
{
lean_object* v_val_654_; lean_object* v___x_655_; 
lean_del_object(v___x_646_);
v_val_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_val_654_);
lean_dec_ref_known(v___x_653_, 1);
v___x_655_ = l_Lean_Language_Lean_setOption(v_opts_636_, v_val_654_, v_name_651_, v_val_652_);
return v___x_655_;
}
else
{
lean_object* v___x_656_; lean_object* v___x_658_; 
lean_dec(v___x_653_);
v___x_656_ = l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0(v_opts_636_, v_name_651_, v_val_652_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v___x_656_);
v___x_658_ = v___x_646_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec(v___y_640_);
lean_dec_ref(v_arg_637_);
lean_dec_ref(v_opts_636_);
v_a_661_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_643_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_643_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; 
lean_dec(v___y_640_);
lean_dec_ref(v_arg_637_);
lean_dec_ref(v_opts_636_);
v___x_669_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_setConfigOption___closed__1));
v___x_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
return v___x_670_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_setConfigOption___boxed(lean_object* v_opts_677_, lean_object* v_arg_678_, lean_object* v_a_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_opts_677_, v_arg_678_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(lean_object* v___x_681_, lean_object* v_arg_682_, lean_object* v_inst_683_, lean_object* v_R_684_, lean_object* v_a_685_, lean_object* v_b_686_, lean_object* v_c_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_681_, v_arg_682_, v_a_685_, v_b_686_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___boxed(lean_object* v___x_689_, lean_object* v_arg_690_, lean_object* v_inst_691_, lean_object* v_R_692_, lean_object* v_a_693_, lean_object* v_b_694_, lean_object* v_c_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(v___x_689_, v_arg_690_, v_inst_691_, v_R_692_, v_a_693_, v_b_694_, v_c_695_);
lean_dec(v_b_694_);
lean_dec_ref(v_arg_690_);
lean_dec_ref(v___x_689_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(lean_object* v_msg_698_){
_start:
{
lean_object* v___f_700_; lean_object* v___x_701_; 
v___f_700_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_701_ = l_IO_eprint___redArg(v___f_700_, v_msg_698_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_701_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_701_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
else
{
lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_717_; 
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_717_ == 0)
{
lean_object* v_unused_718_; 
v_unused_718_ = lean_ctor_get(v___x_701_, 0);
lean_dec(v_unused_718_);
v___x_711_ = v___x_701_;
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
else
{
lean_dec(v___x_701_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_713_ = lean_box(0);
if (v_isShared_712_ == 0)
{
lean_ctor_set_tag(v___x_711_, 0);
lean_ctor_set(v___x_711_, 0, v___x_713_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___boxed(lean_object* v_msg_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(v_msg_719_);
return v_res_721_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_724_; lean_object* v___x_725_; 
v___x_724_ = 1;
v___x_725_ = lean_box_uint32(v___x_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(lean_object* v_x_726_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = lean_apply_1(v_x_726_, lean_box(0));
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_749_; lean_object* v___f_750_; lean_object* v___x_751_; 
v_a_744_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_744_);
lean_dec_ref_known(v___x_735_, 1);
v___x_749_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___f_750_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_751_ = l_IO_eprint___redArg(v___f_750_, v___x_749_);
lean_dec_ref(v___x_751_);
goto v___jp_745_;
v___jp_745_:
{
lean_object* v___x_746_; lean_object* v___f_747_; lean_object* v___x_748_; 
v___x_746_ = lean_io_error_to_string(v_a_744_);
v___f_747_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_748_ = l_IO_eprint___redArg(v___f_747_, v___x_746_);
lean_dec_ref(v___x_748_);
goto v___jp_731_;
}
}
v___jp_728_:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
v___jp_731_:
{
lean_object* v___x_732_; lean_object* v___f_733_; lean_object* v___x_734_; 
v___x_732_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___f_733_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_734_ = l_IO_eprint___redArg(v___f_733_, v___x_732_);
lean_dec_ref(v___x_734_);
goto v___jp_728_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed(lean_object* v_x_752_, lean_object* v_a_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(v_x_752_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(lean_object* v_00_u03b1_755_, lean_object* v_x_756_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = lean_apply_1(v_x_756_, lean_box(0));
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_779_; lean_object* v___f_780_; lean_object* v___x_781_; 
v_a_774_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_774_);
lean_dec_ref_known(v___x_765_, 1);
v___x_779_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___f_780_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_781_ = l_IO_eprint___redArg(v___f_780_, v___x_779_);
lean_dec_ref(v___x_781_);
goto v___jp_775_;
v___jp_775_:
{
lean_object* v___x_776_; lean_object* v___f_777_; lean_object* v___x_778_; 
v___x_776_ = lean_io_error_to_string(v_a_774_);
v___f_777_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_778_ = l_IO_eprint___redArg(v___f_777_, v___x_776_);
lean_dec_ref(v___x_778_);
goto v___jp_761_;
}
}
v___jp_758_:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
return v___x_760_;
}
v___jp_761_:
{
lean_object* v___x_762_; lean_object* v___f_763_; lean_object* v___x_764_; 
v___x_762_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___f_763_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_764_ = l_IO_eprint___redArg(v___f_763_, v___x_762_);
lean_dec_ref(v___x_764_);
goto v___jp_758_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___boxed(lean_object* v_00_u03b1_782_, lean_object* v_x_783_, lean_object* v_a_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(v_00_u03b1_782_, v_x_783_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(lean_object* v_opt_788_){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___f_797_; lean_object* v___x_798_; 
v___x_793_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__0));
v___x_794_ = lean_string_append(v___x_793_, v_opt_788_);
v___x_795_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
v___x_796_ = lean_string_append(v___x_794_, v___x_795_);
v___f_797_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_798_ = l_IO_eprint___redArg(v___f_797_, v___x_796_);
lean_dec_ref(v___x_798_);
goto v___jp_790_;
v___jp_790_:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___boxed(lean_object* v_opt_799_, lean_object* v_a_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(v_opt_799_);
lean_dec_ref(v_opt_799_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(lean_object* v_opt_804_){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___f_813_; lean_object* v___x_814_; 
v___x_809_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__0));
v___x_810_ = lean_string_append(v___x_809_, v_opt_804_);
v___x_811_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__1));
v___x_812_ = lean_string_append(v___x_810_, v___x_811_);
v___f_813_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_814_ = l_IO_eprint___redArg(v___f_813_, v___x_812_);
lean_dec_ref(v___x_814_);
goto v___jp_806_;
v___jp_806_:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___boxed(lean_object* v_opt_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(v_opt_815_);
lean_dec_ref(v_opt_815_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(lean_object* v_s_818_){
_start:
{
lean_object* v___x_820_; lean_object* v_putStr_821_; lean_object* v___x_822_; 
v___x_820_ = lean_get_stderr();
v_putStr_821_ = lean_ctor_get(v___x_820_, 4);
lean_inc_ref(v_putStr_821_);
lean_dec_ref(v___x_820_);
v___x_822_ = lean_apply_2(v_putStr_821_, v_s_818_, lean_box(0));
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0___boxed(lean_object* v_s_823_, lean_object* v_a_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v_s_823_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(lean_object* v_s_826_){
_start:
{
lean_object* v___x_828_; lean_object* v_putStr_829_; lean_object* v___x_830_; 
v___x_828_ = lean_get_stdout();
v_putStr_829_ = lean_ctor_get(v___x_828_, 4);
lean_inc_ref(v_putStr_829_);
lean_dec_ref(v___x_828_);
v___x_830_ = lean_apply_2(v_putStr_829_, v_s_826_, lean_box(0));
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5___boxed(lean_object* v_s_831_, lean_object* v_a_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v_s_831_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(lean_object* v_s_834_){
_start:
{
uint32_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_836_ = 10;
v___x_837_ = lean_string_push(v_s_834_, v___x_836_);
v___x_838_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3___boxed(lean_object* v_s_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v_s_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(lean_object* v_o_842_, lean_object* v_k_843_, uint8_t v_v_844_){
_start:
{
lean_object* v_map_845_; uint8_t v_hasTrace_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_860_; 
v_map_845_ = lean_ctor_get(v_o_842_, 0);
v_hasTrace_846_ = lean_ctor_get_uint8(v_o_842_, sizeof(void*)*1);
v_isSharedCheck_860_ = !lean_is_exclusive(v_o_842_);
if (v_isSharedCheck_860_ == 0)
{
v___x_848_ = v_o_842_;
v_isShared_849_ = v_isSharedCheck_860_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_map_845_);
lean_dec(v_o_842_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_860_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_850_, 0, v_v_844_);
lean_inc(v_k_843_);
v___x_851_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_843_, v___x_850_, v_map_845_);
if (v_hasTrace_846_ == 0)
{
lean_object* v___x_852_; uint8_t v___x_853_; lean_object* v___x_855_; 
v___x_852_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_853_ = l_Lean_Name_isPrefixOf(v___x_852_, v_k_843_);
lean_dec(v_k_843_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v___x_851_);
v___x_855_ = v___x_848_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_851_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_ctor_set_uint8(v___x_855_, sizeof(void*)*1, v___x_853_);
return v___x_855_;
}
}
else
{
lean_object* v___x_858_; 
lean_dec(v_k_843_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v___x_851_);
v___x_858_ = v___x_848_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_851_);
lean_ctor_set_uint8(v_reuseFailAlloc_859_, sizeof(void*)*1, v_hasTrace_846_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1___boxed(lean_object* v_o_861_, lean_object* v_k_862_, lean_object* v_v_863_){
_start:
{
uint8_t v_v_boxed_864_; lean_object* v_res_865_; 
v_v_boxed_864_ = lean_unbox(v_v_863_);
v_res_865_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(v_o_861_, v_k_862_, v_v_boxed_864_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(lean_object* v_opts_866_, lean_object* v_opt_867_, uint8_t v_val_868_){
_start:
{
lean_object* v_name_869_; lean_object* v___x_870_; 
v_name_869_ = lean_ctor_get(v_opt_867_, 0);
lean_inc(v_name_869_);
lean_dec_ref(v_opt_867_);
v___x_870_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(v_opts_866_, v_name_869_, v_val_868_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1___boxed(lean_object* v_opts_871_, lean_object* v_opt_872_, lean_object* v_val_873_){
_start:
{
uint8_t v_val_boxed_874_; lean_object* v_res_875_; 
v_val_boxed_874_ = lean_unbox(v_val_873_);
v_res_875_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_opts_871_, v_opt_872_, v_val_boxed_874_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__3(lean_object* v_o_876_, lean_object* v_k_877_, lean_object* v_v_878_){
_start:
{
lean_object* v_map_879_; uint8_t v_hasTrace_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_894_; 
v_map_879_ = lean_ctor_get(v_o_876_, 0);
v_hasTrace_880_ = lean_ctor_get_uint8(v_o_876_, sizeof(void*)*1);
v_isSharedCheck_894_ = !lean_is_exclusive(v_o_876_);
if (v_isSharedCheck_894_ == 0)
{
v___x_882_ = v_o_876_;
v_isShared_883_ = v_isSharedCheck_894_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_map_879_);
lean_dec(v_o_876_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_894_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_884_, 0, v_v_878_);
lean_inc(v_k_877_);
v___x_885_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_877_, v___x_884_, v_map_879_);
if (v_hasTrace_880_ == 0)
{
lean_object* v___x_886_; uint8_t v___x_887_; lean_object* v___x_889_; 
v___x_886_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_887_ = l_Lean_Name_isPrefixOf(v___x_886_, v_k_877_);
lean_dec(v_k_877_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_885_);
v___x_889_ = v___x_882_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_885_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_ctor_set_uint8(v___x_889_, sizeof(void*)*1, v___x_887_);
return v___x_889_;
}
}
else
{
lean_object* v___x_892_; 
lean_dec(v_k_877_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_885_);
v___x_892_ = v___x_882_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_885_);
lean_ctor_set_uint8(v_reuseFailAlloc_893_, sizeof(void*)*1, v_hasTrace_880_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(lean_object* v_opts_895_, lean_object* v_opt_896_, lean_object* v_val_897_){
_start:
{
lean_object* v_name_898_; lean_object* v___x_899_; 
v_name_898_ = lean_ctor_get(v_opt_896_, 0);
lean_inc(v_name_898_);
lean_dec_ref(v_opt_896_);
v___x_899_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__3(v_opts_895_, v_name_898_, v_val_897_);
return v___x_899_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_928_ = l_System_Platform_numBits;
v___x_929_ = lean_unsigned_to_nat(2u);
v___x_930_ = lean_nat_pow(v___x_929_, v___x_928_);
return v___x_930_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1(void){
_start:
{
uint32_t v___x_940_; lean_object* v___x_941_; 
v___x_940_ = 0;
v___x_941_ = lean_box_uint32(v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* lean_shell_options_process(lean_object* v_opts_942_, uint32_t v_opt_943_, lean_object* v_optArg_x3f_944_){
_start:
{
lean_object* v___y_1058_; lean_object* v___y_1104_; uint32_t v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = 101;
v___x_1165_ = lean_uint32_dec_eq(v_opt_943_, v___x_1164_);
if (v___x_1165_ == 0)
{
uint32_t v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = 106;
v___x_1167_ = lean_uint32_dec_eq(v_opt_943_, v___x_1166_);
if (v___x_1167_ == 0)
{
uint32_t v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = 118;
v___x_1169_ = lean_uint32_dec_eq(v_opt_943_, v___x_1168_);
if (v___x_1169_ == 0)
{
uint32_t v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = 86;
v___x_1171_ = lean_uint32_dec_eq(v_opt_943_, v___x_1170_);
if (v___x_1171_ == 0)
{
uint32_t v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = 103;
v___x_1173_ = lean_uint32_dec_eq(v_opt_943_, v___x_1172_);
if (v___x_1173_ == 0)
{
uint32_t v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = 104;
v___x_1175_ = lean_uint32_dec_eq(v_opt_943_, v___x_1174_);
if (v___x_1175_ == 0)
{
uint32_t v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = 102;
v___x_1177_ = lean_uint32_dec_eq(v_opt_943_, v___x_1176_);
if (v___x_1177_ == 0)
{
uint32_t v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = 99;
v___x_1179_ = lean_uint32_dec_eq(v_opt_943_, v___x_1178_);
if (v___x_1179_ == 0)
{
uint32_t v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = 98;
v___x_1181_ = lean_uint32_dec_eq(v_opt_943_, v___x_1180_);
if (v___x_1181_ == 0)
{
uint32_t v___x_1182_; uint8_t v___x_1183_; 
v___x_1182_ = 115;
v___x_1183_ = lean_uint32_dec_eq(v_opt_943_, v___x_1182_);
if (v___x_1183_ == 0)
{
uint32_t v___x_1184_; uint8_t v___x_1185_; 
v___x_1184_ = 73;
v___x_1185_ = lean_uint32_dec_eq(v_opt_943_, v___x_1184_);
if (v___x_1185_ == 0)
{
uint32_t v___x_1186_; uint8_t v___x_1187_; 
v___x_1186_ = 114;
v___x_1187_ = lean_uint32_dec_eq(v_opt_943_, v___x_1186_);
if (v___x_1187_ == 0)
{
uint32_t v___x_1188_; uint8_t v___x_1189_; 
v___x_1188_ = 111;
v___x_1189_ = lean_uint32_dec_eq(v_opt_943_, v___x_1188_);
if (v___x_1189_ == 0)
{
uint32_t v___x_1190_; uint8_t v___x_1191_; 
v___x_1190_ = 105;
v___x_1191_ = lean_uint32_dec_eq(v_opt_943_, v___x_1190_);
if (v___x_1191_ == 0)
{
uint32_t v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = 82;
v___x_1193_ = lean_uint32_dec_eq(v_opt_943_, v___x_1192_);
if (v___x_1193_ == 0)
{
uint32_t v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = 77;
v___x_1195_ = lean_uint32_dec_eq(v_opt_943_, v___x_1194_);
if (v___x_1195_ == 0)
{
uint32_t v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = 84;
v___x_1197_ = lean_uint32_dec_eq(v_opt_943_, v___x_1196_);
if (v___x_1197_ == 0)
{
uint32_t v___x_1198_; uint8_t v___x_1199_; 
v___x_1198_ = 116;
v___x_1199_ = lean_uint32_dec_eq(v_opt_943_, v___x_1198_);
if (v___x_1199_ == 0)
{
uint32_t v___x_1200_; uint8_t v___x_1201_; 
v___x_1200_ = 113;
v___x_1201_ = lean_uint32_dec_eq(v_opt_943_, v___x_1200_);
if (v___x_1201_ == 0)
{
uint32_t v___x_1202_; uint8_t v___x_1203_; 
v___x_1202_ = 100;
v___x_1203_ = lean_uint32_dec_eq(v_opt_943_, v___x_1202_);
if (v___x_1203_ == 0)
{
uint32_t v___x_1204_; uint8_t v___x_1205_; 
v___x_1204_ = 79;
v___x_1205_ = lean_uint32_dec_eq(v_opt_943_, v___x_1204_);
if (v___x_1205_ == 0)
{
uint32_t v___x_1206_; uint8_t v___x_1207_; 
v___x_1206_ = 78;
v___x_1207_ = lean_uint32_dec_eq(v_opt_943_, v___x_1206_);
if (v___x_1207_ == 0)
{
uint32_t v___x_1208_; uint8_t v___x_1209_; 
v___x_1208_ = 74;
v___x_1209_ = lean_uint32_dec_eq(v_opt_943_, v___x_1208_);
if (v___x_1209_ == 0)
{
uint32_t v___x_1210_; uint8_t v___x_1211_; 
v___x_1210_ = 97;
v___x_1211_ = lean_uint32_dec_eq(v_opt_943_, v___x_1210_);
if (v___x_1211_ == 0)
{
uint32_t v___x_1212_; uint8_t v___x_1213_; 
v___x_1212_ = 120;
v___x_1213_ = lean_uint32_dec_eq(v_opt_943_, v___x_1212_);
if (v___x_1213_ == 0)
{
uint32_t v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = 76;
v___x_1215_ = lean_uint32_dec_eq(v_opt_943_, v___x_1214_);
if (v___x_1215_ == 0)
{
uint32_t v___x_1216_; uint8_t v___x_1217_; 
v___x_1216_ = 68;
v___x_1217_ = lean_uint32_dec_eq(v_opt_943_, v___x_1216_);
if (v___x_1217_ == 0)
{
uint32_t v___x_1218_; uint8_t v___x_1219_; 
v___x_1218_ = 83;
v___x_1219_ = lean_uint32_dec_eq(v_opt_943_, v___x_1218_);
if (v___x_1219_ == 0)
{
uint32_t v___x_1220_; uint8_t v___x_1221_; 
v___x_1220_ = 87;
v___x_1221_ = lean_uint32_dec_eq(v_opt_943_, v___x_1220_);
if (v___x_1221_ == 0)
{
uint32_t v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = 80;
v___x_1223_ = lean_uint32_dec_eq(v_opt_943_, v___x_1222_);
if (v___x_1223_ == 0)
{
uint32_t v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = 66;
v___x_1225_ = lean_uint32_dec_eq(v_opt_943_, v___x_1224_);
if (v___x_1225_ == 0)
{
uint32_t v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = 112;
v___x_1227_ = lean_uint32_dec_eq(v_opt_943_, v___x_1226_);
if (v___x_1227_ == 0)
{
uint32_t v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = 108;
v___x_1229_ = lean_uint32_dec_eq(v_opt_943_, v___x_1228_);
if (v___x_1229_ == 0)
{
uint32_t v___x_1230_; uint8_t v___x_1231_; 
v___x_1230_ = 117;
v___x_1231_ = lean_uint32_dec_eq(v_opt_943_, v___x_1230_);
if (v___x_1231_ == 0)
{
uint32_t v___x_1232_; uint8_t v___x_1233_; 
v___x_1232_ = 69;
v___x_1233_ = lean_uint32_dec_eq(v_opt_943_, v___x_1232_);
if (v___x_1233_ == 0)
{
uint32_t v___x_1234_; uint8_t v___x_1235_; 
v___x_1234_ = 89;
v___x_1235_ = lean_uint32_dec_eq(v_opt_943_, v___x_1234_);
if (v___x_1235_ == 0)
{
uint32_t v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = 90;
v___x_1237_ = lean_uint32_dec_eq(v_opt_943_, v___x_1236_);
if (v___x_1237_ == 0)
{
uint32_t v___x_1238_; uint8_t v___x_1239_; 
v___x_1238_ = 72;
v___x_1239_ = lean_uint32_dec_eq(v_opt_943_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_dec(v_optArg_x3f_944_);
lean_dec_ref(v_opts_942_);
goto v___jp_1076_;
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1));
v___x_1241_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1240_, v_optArg_x3f_944_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1282_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1244_ = v___x_1241_;
v_isShared_1245_ = v_isSharedCheck_1282_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1241_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1282_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v_leanOpts_1246_; lean_object* v_forwardedArgs_1247_; uint8_t v_component_1248_; uint8_t v_printPrefix_1249_; uint8_t v_printLibDir_1250_; uint8_t v_useStdin_1251_; uint8_t v_onlyDeps_1252_; uint8_t v_onlySrcDeps_1253_; uint8_t v_depsJson_1254_; lean_object* v_opts_1255_; uint32_t v_trustLevel_1256_; uint32_t v_numThreads_1257_; lean_object* v_rootDir_x3f_1258_; lean_object* v_setupFileName_x3f_1259_; lean_object* v_oleanFileName_x3f_1260_; lean_object* v_ileanFileName_x3f_1261_; lean_object* v_cFileName_x3f_1262_; lean_object* v_bcFileName_x3f_1263_; uint8_t v_jsonOutput_1264_; lean_object* v_errorOnKinds_1265_; uint8_t v_printStats_1266_; uint8_t v_run_1267_; lean_object* v_incrSaveFileName_x3f_1268_; lean_object* v_incrLoadFileName_x3f_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1280_; 
v_leanOpts_1246_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_1247_ = lean_ctor_get(v_opts_942_, 1);
v_component_1248_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_1249_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_1250_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_1251_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_1252_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1253_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_1254_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_1255_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_1256_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_1257_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1258_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_1259_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_1260_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_1261_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_1262_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_1263_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_1264_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_1265_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_1266_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_1267_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1268_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_1269_ = lean_ctor_get(v_opts_942_, 11);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_1280_ == 0)
{
lean_object* v_unused_1281_; 
v_unused_1281_ = lean_ctor_get(v_opts_942_, 12);
lean_dec(v_unused_1281_);
v___x_1271_ = v_opts_942_;
v_isShared_1272_ = v_isSharedCheck_1280_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_incrLoadFileName_x3f_1269_);
lean_inc(v_incrSaveFileName_x3f_1268_);
lean_inc(v_errorOnKinds_1265_);
lean_inc(v_bcFileName_x3f_1263_);
lean_inc(v_cFileName_x3f_1262_);
lean_inc(v_ileanFileName_x3f_1261_);
lean_inc(v_oleanFileName_x3f_1260_);
lean_inc(v_setupFileName_x3f_1259_);
lean_inc(v_rootDir_x3f_1258_);
lean_inc(v_opts_1255_);
lean_inc(v_forwardedArgs_1247_);
lean_inc(v_leanOpts_1246_);
lean_dec(v_opts_942_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1280_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; lean_object* v___x_1275_; 
v___x_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1273_, 0, v_a_1242_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 12, v___x_1273_);
v___x_1275_ = v___x_1271_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_leanOpts_1246_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_forwardedArgs_1247_);
lean_ctor_set(v_reuseFailAlloc_1279_, 2, v_opts_1255_);
lean_ctor_set(v_reuseFailAlloc_1279_, 3, v_rootDir_x3f_1258_);
lean_ctor_set(v_reuseFailAlloc_1279_, 4, v_setupFileName_x3f_1259_);
lean_ctor_set(v_reuseFailAlloc_1279_, 5, v_oleanFileName_x3f_1260_);
lean_ctor_set(v_reuseFailAlloc_1279_, 6, v_ileanFileName_x3f_1261_);
lean_ctor_set(v_reuseFailAlloc_1279_, 7, v_cFileName_x3f_1262_);
lean_ctor_set(v_reuseFailAlloc_1279_, 8, v_bcFileName_x3f_1263_);
lean_ctor_set(v_reuseFailAlloc_1279_, 9, v_errorOnKinds_1265_);
lean_ctor_set(v_reuseFailAlloc_1279_, 10, v_incrSaveFileName_x3f_1268_);
lean_ctor_set(v_reuseFailAlloc_1279_, 11, v_incrLoadFileName_x3f_1269_);
lean_ctor_set(v_reuseFailAlloc_1279_, 12, v___x_1273_);
lean_ctor_set_uint8(v_reuseFailAlloc_1279_, sizeof(void*)*13 + 8, v_component_1248_);
lean_ctor_set_uint8(v_reuseFailAlloc_1279_, sizeof(void*)*13 + 9, v_printPrefix_1249_);
lean_ctor_set_uint8(v_reuseFailAlloc_1279_, sizeof(void*)*13 + 10, v_printLibDir_1250_);
lean_ctor_set_uint8(v_reuseFailAlloc_1279_, sizeof(void*)*13 + 11, v_useStdin_1251_);
lean_ctor_set_uint8(v_reuseFailAlloc_1279_, sizeof(void*)*13 + 12, v_onlyDeps_1252_);
lean_ctor_set_uint8(v_reuseFailAlloc_1279_, sizeof(void*)*13 + 13, v_onlySrcDeps_1253_);
lean_ctor_set_uint8(v_reuseFailAlloc_1279_, sizeof(void*)*13 + 14, v_depsJson_1254_);
lean_ctor_set_uint32(v_reuseFailAlloc_1279_, sizeof(void*)*13, v_trustLevel_1256_);
lean_ctor_set_uint32(v_reuseFailAlloc_1279_, sizeof(void*)*13 + 4, v_numThreads_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1279_, sizeof(void*)*13 + 15, v_jsonOutput_1264_);
lean_ctor_set_uint8(v_reuseFailAlloc_1279_, sizeof(void*)*13 + 16, v_printStats_1266_);
lean_ctor_set_uint8(v_reuseFailAlloc_1279_, sizeof(void*)*13 + 17, v_run_1267_);
v___x_1275_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
lean_object* v___x_1277_; 
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1275_);
v___x_1277_ = v___x_1244_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
lean_dec_ref(v_opts_942_);
v_a_1283_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1283_);
lean_dec_ref_known(v___x_1241_, 1);
v___x_1287_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1288_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1287_);
lean_dec_ref(v___x_1288_);
goto v___jp_1284_;
v___jp_1284_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = lean_io_error_to_string(v_a_1283_);
v___x_1286_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1285_);
lean_dec_ref(v___x_1286_);
goto v___jp_1048_;
}
}
}
}
else
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2));
v___x_1290_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1289_, v_optArg_x3f_944_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1331_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1293_ = v___x_1290_;
v_isShared_1294_ = v_isSharedCheck_1331_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1290_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1331_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v_leanOpts_1295_; lean_object* v_forwardedArgs_1296_; uint8_t v_component_1297_; uint8_t v_printPrefix_1298_; uint8_t v_printLibDir_1299_; uint8_t v_useStdin_1300_; uint8_t v_onlyDeps_1301_; uint8_t v_onlySrcDeps_1302_; uint8_t v_depsJson_1303_; lean_object* v_opts_1304_; uint32_t v_trustLevel_1305_; uint32_t v_numThreads_1306_; lean_object* v_rootDir_x3f_1307_; lean_object* v_setupFileName_x3f_1308_; lean_object* v_oleanFileName_x3f_1309_; lean_object* v_ileanFileName_x3f_1310_; lean_object* v_cFileName_x3f_1311_; lean_object* v_bcFileName_x3f_1312_; uint8_t v_jsonOutput_1313_; lean_object* v_errorOnKinds_1314_; uint8_t v_printStats_1315_; uint8_t v_run_1316_; lean_object* v_incrSaveFileName_x3f_1317_; lean_object* v_incrHeaderSaveFileName_x3f_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1329_; 
v_leanOpts_1295_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_1296_ = lean_ctor_get(v_opts_942_, 1);
v_component_1297_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_1298_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_1299_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_1300_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_1301_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1302_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_1303_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_1304_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_1305_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_1306_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1307_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_1308_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_1309_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_1310_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_1311_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_1312_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_1313_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_1314_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_1315_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_1316_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1317_ = lean_ctor_get(v_opts_942_, 10);
v_incrHeaderSaveFileName_x3f_1318_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_1329_ == 0)
{
lean_object* v_unused_1330_; 
v_unused_1330_ = lean_ctor_get(v_opts_942_, 11);
lean_dec(v_unused_1330_);
v___x_1320_ = v_opts_942_;
v_isShared_1321_ = v_isSharedCheck_1329_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1318_);
lean_inc(v_incrSaveFileName_x3f_1317_);
lean_inc(v_errorOnKinds_1314_);
lean_inc(v_bcFileName_x3f_1312_);
lean_inc(v_cFileName_x3f_1311_);
lean_inc(v_ileanFileName_x3f_1310_);
lean_inc(v_oleanFileName_x3f_1309_);
lean_inc(v_setupFileName_x3f_1308_);
lean_inc(v_rootDir_x3f_1307_);
lean_inc(v_opts_1304_);
lean_inc(v_forwardedArgs_1296_);
lean_inc(v_leanOpts_1295_);
lean_dec(v_opts_942_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1329_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___x_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1322_, 0, v_a_1291_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 11, v___x_1322_);
v___x_1324_ = v___x_1320_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_leanOpts_1295_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v_forwardedArgs_1296_);
lean_ctor_set(v_reuseFailAlloc_1328_, 2, v_opts_1304_);
lean_ctor_set(v_reuseFailAlloc_1328_, 3, v_rootDir_x3f_1307_);
lean_ctor_set(v_reuseFailAlloc_1328_, 4, v_setupFileName_x3f_1308_);
lean_ctor_set(v_reuseFailAlloc_1328_, 5, v_oleanFileName_x3f_1309_);
lean_ctor_set(v_reuseFailAlloc_1328_, 6, v_ileanFileName_x3f_1310_);
lean_ctor_set(v_reuseFailAlloc_1328_, 7, v_cFileName_x3f_1311_);
lean_ctor_set(v_reuseFailAlloc_1328_, 8, v_bcFileName_x3f_1312_);
lean_ctor_set(v_reuseFailAlloc_1328_, 9, v_errorOnKinds_1314_);
lean_ctor_set(v_reuseFailAlloc_1328_, 10, v_incrSaveFileName_x3f_1317_);
lean_ctor_set(v_reuseFailAlloc_1328_, 11, v___x_1322_);
lean_ctor_set(v_reuseFailAlloc_1328_, 12, v_incrHeaderSaveFileName_x3f_1318_);
lean_ctor_set_uint8(v_reuseFailAlloc_1328_, sizeof(void*)*13 + 8, v_component_1297_);
lean_ctor_set_uint8(v_reuseFailAlloc_1328_, sizeof(void*)*13 + 9, v_printPrefix_1298_);
lean_ctor_set_uint8(v_reuseFailAlloc_1328_, sizeof(void*)*13 + 10, v_printLibDir_1299_);
lean_ctor_set_uint8(v_reuseFailAlloc_1328_, sizeof(void*)*13 + 11, v_useStdin_1300_);
lean_ctor_set_uint8(v_reuseFailAlloc_1328_, sizeof(void*)*13 + 12, v_onlyDeps_1301_);
lean_ctor_set_uint8(v_reuseFailAlloc_1328_, sizeof(void*)*13 + 13, v_onlySrcDeps_1302_);
lean_ctor_set_uint8(v_reuseFailAlloc_1328_, sizeof(void*)*13 + 14, v_depsJson_1303_);
lean_ctor_set_uint32(v_reuseFailAlloc_1328_, sizeof(void*)*13, v_trustLevel_1305_);
lean_ctor_set_uint32(v_reuseFailAlloc_1328_, sizeof(void*)*13 + 4, v_numThreads_1306_);
lean_ctor_set_uint8(v_reuseFailAlloc_1328_, sizeof(void*)*13 + 15, v_jsonOutput_1313_);
lean_ctor_set_uint8(v_reuseFailAlloc_1328_, sizeof(void*)*13 + 16, v_printStats_1315_);
lean_ctor_set_uint8(v_reuseFailAlloc_1328_, sizeof(void*)*13 + 17, v_run_1316_);
v___x_1324_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
lean_object* v___x_1326_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v___x_1324_);
v___x_1326_ = v___x_1293_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_dec_ref(v_opts_942_);
v_a_1332_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1332_);
lean_dec_ref_known(v___x_1290_, 1);
v___x_1336_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1337_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1336_);
lean_dec_ref(v___x_1337_);
goto v___jp_1333_;
v___jp_1333_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = lean_io_error_to_string(v_a_1332_);
v___x_1335_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1334_);
lean_dec_ref(v___x_1335_);
goto v___jp_1082_;
}
}
}
}
else
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3));
v___x_1339_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1338_, v_optArg_x3f_944_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1380_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1342_ = v___x_1339_;
v_isShared_1343_ = v_isSharedCheck_1380_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1339_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1380_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v_leanOpts_1344_; lean_object* v_forwardedArgs_1345_; uint8_t v_component_1346_; uint8_t v_printPrefix_1347_; uint8_t v_printLibDir_1348_; uint8_t v_useStdin_1349_; uint8_t v_onlyDeps_1350_; uint8_t v_onlySrcDeps_1351_; uint8_t v_depsJson_1352_; lean_object* v_opts_1353_; uint32_t v_trustLevel_1354_; uint32_t v_numThreads_1355_; lean_object* v_rootDir_x3f_1356_; lean_object* v_setupFileName_x3f_1357_; lean_object* v_oleanFileName_x3f_1358_; lean_object* v_ileanFileName_x3f_1359_; lean_object* v_cFileName_x3f_1360_; lean_object* v_bcFileName_x3f_1361_; uint8_t v_jsonOutput_1362_; lean_object* v_errorOnKinds_1363_; uint8_t v_printStats_1364_; uint8_t v_run_1365_; lean_object* v_incrLoadFileName_x3f_1366_; lean_object* v_incrHeaderSaveFileName_x3f_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1378_; 
v_leanOpts_1344_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_1345_ = lean_ctor_get(v_opts_942_, 1);
v_component_1346_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_1347_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_1348_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_1349_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_1350_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1351_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_1352_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_1353_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_1354_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_1355_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1356_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_1357_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_1358_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_1359_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_1360_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_1361_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_1362_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_1363_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_1364_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_1365_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrLoadFileName_x3f_1366_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_1367_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_1378_ == 0)
{
lean_object* v_unused_1379_; 
v_unused_1379_ = lean_ctor_get(v_opts_942_, 10);
lean_dec(v_unused_1379_);
v___x_1369_ = v_opts_942_;
v_isShared_1370_ = v_isSharedCheck_1378_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1367_);
lean_inc(v_incrLoadFileName_x3f_1366_);
lean_inc(v_errorOnKinds_1363_);
lean_inc(v_bcFileName_x3f_1361_);
lean_inc(v_cFileName_x3f_1360_);
lean_inc(v_ileanFileName_x3f_1359_);
lean_inc(v_oleanFileName_x3f_1358_);
lean_inc(v_setupFileName_x3f_1357_);
lean_inc(v_rootDir_x3f_1356_);
lean_inc(v_opts_1353_);
lean_inc(v_forwardedArgs_1345_);
lean_inc(v_leanOpts_1344_);
lean_dec(v_opts_942_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1378_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1371_, 0, v_a_1340_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 10, v___x_1371_);
v___x_1373_ = v___x_1369_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_leanOpts_1344_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_forwardedArgs_1345_);
lean_ctor_set(v_reuseFailAlloc_1377_, 2, v_opts_1353_);
lean_ctor_set(v_reuseFailAlloc_1377_, 3, v_rootDir_x3f_1356_);
lean_ctor_set(v_reuseFailAlloc_1377_, 4, v_setupFileName_x3f_1357_);
lean_ctor_set(v_reuseFailAlloc_1377_, 5, v_oleanFileName_x3f_1358_);
lean_ctor_set(v_reuseFailAlloc_1377_, 6, v_ileanFileName_x3f_1359_);
lean_ctor_set(v_reuseFailAlloc_1377_, 7, v_cFileName_x3f_1360_);
lean_ctor_set(v_reuseFailAlloc_1377_, 8, v_bcFileName_x3f_1361_);
lean_ctor_set(v_reuseFailAlloc_1377_, 9, v_errorOnKinds_1363_);
lean_ctor_set(v_reuseFailAlloc_1377_, 10, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1377_, 11, v_incrLoadFileName_x3f_1366_);
lean_ctor_set(v_reuseFailAlloc_1377_, 12, v_incrHeaderSaveFileName_x3f_1367_);
lean_ctor_set_uint8(v_reuseFailAlloc_1377_, sizeof(void*)*13 + 8, v_component_1346_);
lean_ctor_set_uint8(v_reuseFailAlloc_1377_, sizeof(void*)*13 + 9, v_printPrefix_1347_);
lean_ctor_set_uint8(v_reuseFailAlloc_1377_, sizeof(void*)*13 + 10, v_printLibDir_1348_);
lean_ctor_set_uint8(v_reuseFailAlloc_1377_, sizeof(void*)*13 + 11, v_useStdin_1349_);
lean_ctor_set_uint8(v_reuseFailAlloc_1377_, sizeof(void*)*13 + 12, v_onlyDeps_1350_);
lean_ctor_set_uint8(v_reuseFailAlloc_1377_, sizeof(void*)*13 + 13, v_onlySrcDeps_1351_);
lean_ctor_set_uint8(v_reuseFailAlloc_1377_, sizeof(void*)*13 + 14, v_depsJson_1352_);
lean_ctor_set_uint32(v_reuseFailAlloc_1377_, sizeof(void*)*13, v_trustLevel_1354_);
lean_ctor_set_uint32(v_reuseFailAlloc_1377_, sizeof(void*)*13 + 4, v_numThreads_1355_);
lean_ctor_set_uint8(v_reuseFailAlloc_1377_, sizeof(void*)*13 + 15, v_jsonOutput_1362_);
lean_ctor_set_uint8(v_reuseFailAlloc_1377_, sizeof(void*)*13 + 16, v_printStats_1364_);
lean_ctor_set_uint8(v_reuseFailAlloc_1377_, sizeof(void*)*13 + 17, v_run_1365_);
v___x_1373_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1375_; 
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1373_);
v___x_1375_ = v___x_1342_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
lean_dec_ref(v_opts_942_);
v_a_1381_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1381_);
lean_dec_ref_known(v___x_1339_, 1);
v___x_1385_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1386_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1385_);
lean_dec_ref(v___x_1386_);
goto v___jp_1382_;
v___jp_1382_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = lean_io_error_to_string(v_a_1381_);
v___x_1384_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1383_);
lean_dec_ref(v___x_1384_);
goto v___jp_1042_;
}
}
}
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4));
v___x_1388_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1387_, v_optArg_x3f_944_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1430_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1391_ = v___x_1388_;
v_isShared_1392_ = v_isSharedCheck_1430_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1430_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v_leanOpts_1393_; lean_object* v_forwardedArgs_1394_; uint8_t v_component_1395_; uint8_t v_printPrefix_1396_; uint8_t v_printLibDir_1397_; uint8_t v_useStdin_1398_; uint8_t v_onlyDeps_1399_; uint8_t v_onlySrcDeps_1400_; uint8_t v_depsJson_1401_; lean_object* v_opts_1402_; uint32_t v_trustLevel_1403_; uint32_t v_numThreads_1404_; lean_object* v_rootDir_x3f_1405_; lean_object* v_setupFileName_x3f_1406_; lean_object* v_oleanFileName_x3f_1407_; lean_object* v_ileanFileName_x3f_1408_; lean_object* v_cFileName_x3f_1409_; lean_object* v_bcFileName_x3f_1410_; uint8_t v_jsonOutput_1411_; lean_object* v_errorOnKinds_1412_; uint8_t v_printStats_1413_; uint8_t v_run_1414_; lean_object* v_incrSaveFileName_x3f_1415_; lean_object* v_incrLoadFileName_x3f_1416_; lean_object* v_incrHeaderSaveFileName_x3f_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1429_; 
v_leanOpts_1393_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_1394_ = lean_ctor_get(v_opts_942_, 1);
v_component_1395_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_1396_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_1397_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_1398_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_1399_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1400_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_1401_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_1402_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_1403_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_1404_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1405_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_1406_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_1407_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_1408_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_1409_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_1410_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_1411_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_1412_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_1413_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_1414_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1415_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_1416_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_1417_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1419_ = v_opts_942_;
v_isShared_1420_ = v_isSharedCheck_1429_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1417_);
lean_inc(v_incrLoadFileName_x3f_1416_);
lean_inc(v_incrSaveFileName_x3f_1415_);
lean_inc(v_errorOnKinds_1412_);
lean_inc(v_bcFileName_x3f_1410_);
lean_inc(v_cFileName_x3f_1409_);
lean_inc(v_ileanFileName_x3f_1408_);
lean_inc(v_oleanFileName_x3f_1407_);
lean_inc(v_setupFileName_x3f_1406_);
lean_inc(v_rootDir_x3f_1405_);
lean_inc(v_opts_1402_);
lean_inc(v_forwardedArgs_1394_);
lean_inc(v_leanOpts_1393_);
lean_dec(v_opts_942_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1429_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1421_ = l_String_toName(v_a_1389_);
v___x_1422_ = lean_array_push(v_errorOnKinds_1412_, v___x_1421_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 9, v___x_1422_);
v___x_1424_ = v___x_1419_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_leanOpts_1393_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_forwardedArgs_1394_);
lean_ctor_set(v_reuseFailAlloc_1428_, 2, v_opts_1402_);
lean_ctor_set(v_reuseFailAlloc_1428_, 3, v_rootDir_x3f_1405_);
lean_ctor_set(v_reuseFailAlloc_1428_, 4, v_setupFileName_x3f_1406_);
lean_ctor_set(v_reuseFailAlloc_1428_, 5, v_oleanFileName_x3f_1407_);
lean_ctor_set(v_reuseFailAlloc_1428_, 6, v_ileanFileName_x3f_1408_);
lean_ctor_set(v_reuseFailAlloc_1428_, 7, v_cFileName_x3f_1409_);
lean_ctor_set(v_reuseFailAlloc_1428_, 8, v_bcFileName_x3f_1410_);
lean_ctor_set(v_reuseFailAlloc_1428_, 9, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1428_, 10, v_incrSaveFileName_x3f_1415_);
lean_ctor_set(v_reuseFailAlloc_1428_, 11, v_incrLoadFileName_x3f_1416_);
lean_ctor_set(v_reuseFailAlloc_1428_, 12, v_incrHeaderSaveFileName_x3f_1417_);
lean_ctor_set_uint8(v_reuseFailAlloc_1428_, sizeof(void*)*13 + 8, v_component_1395_);
lean_ctor_set_uint8(v_reuseFailAlloc_1428_, sizeof(void*)*13 + 9, v_printPrefix_1396_);
lean_ctor_set_uint8(v_reuseFailAlloc_1428_, sizeof(void*)*13 + 10, v_printLibDir_1397_);
lean_ctor_set_uint8(v_reuseFailAlloc_1428_, sizeof(void*)*13 + 11, v_useStdin_1398_);
lean_ctor_set_uint8(v_reuseFailAlloc_1428_, sizeof(void*)*13 + 12, v_onlyDeps_1399_);
lean_ctor_set_uint8(v_reuseFailAlloc_1428_, sizeof(void*)*13 + 13, v_onlySrcDeps_1400_);
lean_ctor_set_uint8(v_reuseFailAlloc_1428_, sizeof(void*)*13 + 14, v_depsJson_1401_);
lean_ctor_set_uint32(v_reuseFailAlloc_1428_, sizeof(void*)*13, v_trustLevel_1403_);
lean_ctor_set_uint32(v_reuseFailAlloc_1428_, sizeof(void*)*13 + 4, v_numThreads_1404_);
lean_ctor_set_uint8(v_reuseFailAlloc_1428_, sizeof(void*)*13 + 15, v_jsonOutput_1411_);
lean_ctor_set_uint8(v_reuseFailAlloc_1428_, sizeof(void*)*13 + 16, v_printStats_1413_);
lean_ctor_set_uint8(v_reuseFailAlloc_1428_, sizeof(void*)*13 + 17, v_run_1414_);
v___x_1424_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1426_; 
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v___x_1424_);
v___x_1426_ = v___x_1391_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1424_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
lean_dec_ref(v_opts_942_);
v_a_1431_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1388_, 1);
v___x_1435_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1436_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1435_);
lean_dec_ref(v___x_1436_);
goto v___jp_1432_;
v___jp_1432_:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = lean_io_error_to_string(v_a_1431_);
v___x_1434_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1433_);
lean_dec_ref(v___x_1434_);
goto v___jp_1088_;
}
}
}
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5));
v___x_1438_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1437_, v_optArg_x3f_944_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1479_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1441_ = v___x_1438_;
v_isShared_1442_ = v_isSharedCheck_1479_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1438_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1479_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v_leanOpts_1443_; lean_object* v_forwardedArgs_1444_; uint8_t v_component_1445_; uint8_t v_printPrefix_1446_; uint8_t v_printLibDir_1447_; uint8_t v_useStdin_1448_; uint8_t v_onlyDeps_1449_; uint8_t v_onlySrcDeps_1450_; uint8_t v_depsJson_1451_; lean_object* v_opts_1452_; uint32_t v_trustLevel_1453_; uint32_t v_numThreads_1454_; lean_object* v_rootDir_x3f_1455_; lean_object* v_oleanFileName_x3f_1456_; lean_object* v_ileanFileName_x3f_1457_; lean_object* v_cFileName_x3f_1458_; lean_object* v_bcFileName_x3f_1459_; uint8_t v_jsonOutput_1460_; lean_object* v_errorOnKinds_1461_; uint8_t v_printStats_1462_; uint8_t v_run_1463_; lean_object* v_incrSaveFileName_x3f_1464_; lean_object* v_incrLoadFileName_x3f_1465_; lean_object* v_incrHeaderSaveFileName_x3f_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1477_; 
v_leanOpts_1443_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_1444_ = lean_ctor_get(v_opts_942_, 1);
v_component_1445_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_1446_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_1447_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_1448_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_1449_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1450_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_1451_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_1452_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_1453_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_1454_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1455_ = lean_ctor_get(v_opts_942_, 3);
v_oleanFileName_x3f_1456_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_1457_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_1458_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_1459_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_1460_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_1461_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_1462_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_1463_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1464_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_1465_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_1466_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_1477_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_1477_ == 0)
{
lean_object* v_unused_1478_; 
v_unused_1478_ = lean_ctor_get(v_opts_942_, 4);
lean_dec(v_unused_1478_);
v___x_1468_ = v_opts_942_;
v_isShared_1469_ = v_isSharedCheck_1477_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1466_);
lean_inc(v_incrLoadFileName_x3f_1465_);
lean_inc(v_incrSaveFileName_x3f_1464_);
lean_inc(v_errorOnKinds_1461_);
lean_inc(v_bcFileName_x3f_1459_);
lean_inc(v_cFileName_x3f_1458_);
lean_inc(v_ileanFileName_x3f_1457_);
lean_inc(v_oleanFileName_x3f_1456_);
lean_inc(v_rootDir_x3f_1455_);
lean_inc(v_opts_1452_);
lean_inc(v_forwardedArgs_1444_);
lean_inc(v_leanOpts_1443_);
lean_dec(v_opts_942_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1477_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; lean_object* v___x_1472_; 
v___x_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1470_, 0, v_a_1439_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 4, v___x_1470_);
v___x_1472_ = v___x_1468_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_leanOpts_1443_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_forwardedArgs_1444_);
lean_ctor_set(v_reuseFailAlloc_1476_, 2, v_opts_1452_);
lean_ctor_set(v_reuseFailAlloc_1476_, 3, v_rootDir_x3f_1455_);
lean_ctor_set(v_reuseFailAlloc_1476_, 4, v___x_1470_);
lean_ctor_set(v_reuseFailAlloc_1476_, 5, v_oleanFileName_x3f_1456_);
lean_ctor_set(v_reuseFailAlloc_1476_, 6, v_ileanFileName_x3f_1457_);
lean_ctor_set(v_reuseFailAlloc_1476_, 7, v_cFileName_x3f_1458_);
lean_ctor_set(v_reuseFailAlloc_1476_, 8, v_bcFileName_x3f_1459_);
lean_ctor_set(v_reuseFailAlloc_1476_, 9, v_errorOnKinds_1461_);
lean_ctor_set(v_reuseFailAlloc_1476_, 10, v_incrSaveFileName_x3f_1464_);
lean_ctor_set(v_reuseFailAlloc_1476_, 11, v_incrLoadFileName_x3f_1465_);
lean_ctor_set(v_reuseFailAlloc_1476_, 12, v_incrHeaderSaveFileName_x3f_1466_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*13 + 8, v_component_1445_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*13 + 9, v_printPrefix_1446_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*13 + 10, v_printLibDir_1447_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*13 + 11, v_useStdin_1448_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*13 + 12, v_onlyDeps_1449_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*13 + 13, v_onlySrcDeps_1450_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*13 + 14, v_depsJson_1451_);
lean_ctor_set_uint32(v_reuseFailAlloc_1476_, sizeof(void*)*13, v_trustLevel_1453_);
lean_ctor_set_uint32(v_reuseFailAlloc_1476_, sizeof(void*)*13 + 4, v_numThreads_1454_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*13 + 15, v_jsonOutput_1460_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*13 + 16, v_printStats_1462_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*13 + 17, v_run_1463_);
v___x_1472_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
lean_object* v___x_1474_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1472_);
v___x_1474_ = v___x_1441_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_dec_ref(v_opts_942_);
v_a_1480_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1480_);
lean_dec_ref_known(v___x_1438_, 1);
v___x_1484_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1485_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1484_);
lean_dec_ref(v___x_1485_);
goto v___jp_1481_;
v___jp_1481_:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = lean_io_error_to_string(v_a_1480_);
v___x_1483_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1482_);
lean_dec_ref(v___x_1483_);
goto v___jp_1036_;
}
}
}
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6));
v___x_1487_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1486_, v_optArg_x3f_944_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v___x_1489_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc_n(v_a_1488_, 2);
lean_dec_ref_known(v___x_1487_, 1);
v___x_1489_ = lean_load_dynlib(v_a_1488_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1531_; 
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1531_ == 0)
{
lean_object* v_unused_1532_; 
v_unused_1532_ = lean_ctor_get(v___x_1489_, 0);
lean_dec(v_unused_1532_);
v___x_1491_ = v___x_1489_;
v_isShared_1492_ = v_isSharedCheck_1531_;
goto v_resetjp_1490_;
}
else
{
lean_dec(v___x_1489_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1531_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v_leanOpts_1493_; lean_object* v_forwardedArgs_1494_; uint8_t v_component_1495_; uint8_t v_printPrefix_1496_; uint8_t v_printLibDir_1497_; uint8_t v_useStdin_1498_; uint8_t v_onlyDeps_1499_; uint8_t v_onlySrcDeps_1500_; uint8_t v_depsJson_1501_; lean_object* v_opts_1502_; uint32_t v_trustLevel_1503_; uint32_t v_numThreads_1504_; lean_object* v_rootDir_x3f_1505_; lean_object* v_setupFileName_x3f_1506_; lean_object* v_oleanFileName_x3f_1507_; lean_object* v_ileanFileName_x3f_1508_; lean_object* v_cFileName_x3f_1509_; lean_object* v_bcFileName_x3f_1510_; uint8_t v_jsonOutput_1511_; lean_object* v_errorOnKinds_1512_; uint8_t v_printStats_1513_; uint8_t v_run_1514_; lean_object* v_incrSaveFileName_x3f_1515_; lean_object* v_incrLoadFileName_x3f_1516_; lean_object* v_incrHeaderSaveFileName_x3f_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1530_; 
v_leanOpts_1493_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_1494_ = lean_ctor_get(v_opts_942_, 1);
v_component_1495_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_1496_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_1497_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_1498_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_1499_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1500_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_1501_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_1502_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_1503_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_1504_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1505_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_1506_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_1507_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_1508_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_1509_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_1510_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_1511_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_1512_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_1513_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_1514_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1515_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_1516_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_1517_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1519_ = v_opts_942_;
v_isShared_1520_ = v_isSharedCheck_1530_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1517_);
lean_inc(v_incrLoadFileName_x3f_1516_);
lean_inc(v_incrSaveFileName_x3f_1515_);
lean_inc(v_errorOnKinds_1512_);
lean_inc(v_bcFileName_x3f_1510_);
lean_inc(v_cFileName_x3f_1509_);
lean_inc(v_ileanFileName_x3f_1508_);
lean_inc(v_oleanFileName_x3f_1507_);
lean_inc(v_setupFileName_x3f_1506_);
lean_inc(v_rootDir_x3f_1505_);
lean_inc(v_opts_1502_);
lean_inc(v_forwardedArgs_1494_);
lean_inc(v_leanOpts_1493_);
lean_dec(v_opts_942_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1530_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1521_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7));
v___x_1522_ = lean_string_append(v___x_1521_, v_a_1488_);
lean_dec(v_a_1488_);
v___x_1523_ = lean_array_push(v_forwardedArgs_1494_, v___x_1522_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 1, v___x_1523_);
v___x_1525_ = v___x_1519_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_leanOpts_1493_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1529_, 2, v_opts_1502_);
lean_ctor_set(v_reuseFailAlloc_1529_, 3, v_rootDir_x3f_1505_);
lean_ctor_set(v_reuseFailAlloc_1529_, 4, v_setupFileName_x3f_1506_);
lean_ctor_set(v_reuseFailAlloc_1529_, 5, v_oleanFileName_x3f_1507_);
lean_ctor_set(v_reuseFailAlloc_1529_, 6, v_ileanFileName_x3f_1508_);
lean_ctor_set(v_reuseFailAlloc_1529_, 7, v_cFileName_x3f_1509_);
lean_ctor_set(v_reuseFailAlloc_1529_, 8, v_bcFileName_x3f_1510_);
lean_ctor_set(v_reuseFailAlloc_1529_, 9, v_errorOnKinds_1512_);
lean_ctor_set(v_reuseFailAlloc_1529_, 10, v_incrSaveFileName_x3f_1515_);
lean_ctor_set(v_reuseFailAlloc_1529_, 11, v_incrLoadFileName_x3f_1516_);
lean_ctor_set(v_reuseFailAlloc_1529_, 12, v_incrHeaderSaveFileName_x3f_1517_);
lean_ctor_set_uint8(v_reuseFailAlloc_1529_, sizeof(void*)*13 + 8, v_component_1495_);
lean_ctor_set_uint8(v_reuseFailAlloc_1529_, sizeof(void*)*13 + 9, v_printPrefix_1496_);
lean_ctor_set_uint8(v_reuseFailAlloc_1529_, sizeof(void*)*13 + 10, v_printLibDir_1497_);
lean_ctor_set_uint8(v_reuseFailAlloc_1529_, sizeof(void*)*13 + 11, v_useStdin_1498_);
lean_ctor_set_uint8(v_reuseFailAlloc_1529_, sizeof(void*)*13 + 12, v_onlyDeps_1499_);
lean_ctor_set_uint8(v_reuseFailAlloc_1529_, sizeof(void*)*13 + 13, v_onlySrcDeps_1500_);
lean_ctor_set_uint8(v_reuseFailAlloc_1529_, sizeof(void*)*13 + 14, v_depsJson_1501_);
lean_ctor_set_uint32(v_reuseFailAlloc_1529_, sizeof(void*)*13, v_trustLevel_1503_);
lean_ctor_set_uint32(v_reuseFailAlloc_1529_, sizeof(void*)*13 + 4, v_numThreads_1504_);
lean_ctor_set_uint8(v_reuseFailAlloc_1529_, sizeof(void*)*13 + 15, v_jsonOutput_1511_);
lean_ctor_set_uint8(v_reuseFailAlloc_1529_, sizeof(void*)*13 + 16, v_printStats_1513_);
lean_ctor_set_uint8(v_reuseFailAlloc_1529_, sizeof(void*)*13 + 17, v_run_1514_);
v___x_1525_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1527_; 
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v___x_1525_);
v___x_1527_ = v___x_1491_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_dec(v_a_1488_);
lean_dec_ref(v_opts_942_);
v_a_1533_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1489_, 1);
v___x_1537_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1538_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1537_);
lean_dec_ref(v___x_1538_);
goto v___jp_1534_;
v___jp_1534_:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = lean_io_error_to_string(v_a_1533_);
v___x_1536_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1535_);
lean_dec_ref(v___x_1536_);
goto v___jp_1094_;
}
}
}
else
{
lean_object* v_a_1539_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
lean_dec_ref(v_opts_942_);
v_a_1539_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_a_1539_);
lean_dec_ref_known(v___x_1487_, 1);
v___x_1543_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1544_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1543_);
lean_dec_ref(v___x_1544_);
goto v___jp_1540_;
v___jp_1540_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = lean_io_error_to_string(v_a_1539_);
v___x_1542_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1541_);
lean_dec_ref(v___x_1542_);
goto v___jp_1030_;
}
}
}
}
else
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8));
v___x_1546_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1545_, v_optArg_x3f_944_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1619_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1549_ = v___x_1546_;
v_isShared_1550_ = v_isSharedCheck_1619_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1546_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1619_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v_fst_1552_; lean_object* v_snd_1553_; lean_object* v___y_1602_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1613_ = lean_unsigned_to_nat(0u);
v___x_1614_ = lean_string_utf8_byte_size(v_a_1547_);
lean_inc(v_a_1547_);
v___x_1615_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1615_, 0, v_a_1547_);
lean_ctor_set(v___x_1615_, 1, v___x_1613_);
lean_ctor_set(v___x_1615_, 2, v___x_1614_);
v___x_1616_ = lean_box(0);
v___x_1617_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_1615_, v_a_1547_, v___x_1613_, v___x_1616_);
lean_dec_ref_known(v___x_1615_, 3);
if (lean_obj_tag(v___x_1617_) == 0)
{
v___y_1602_ = v___x_1614_;
goto v___jp_1601_;
}
else
{
lean_object* v_val_1618_; 
v_val_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_val_1618_);
lean_dec_ref_known(v___x_1617_, 1);
v___y_1602_ = v_val_1618_;
goto v___jp_1601_;
}
v___jp_1551_:
{
lean_object* v___x_1554_; 
v___x_1554_ = lean_load_plugin(v_fst_1552_, v_snd_1553_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1596_; 
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1596_ == 0)
{
lean_object* v_unused_1597_; 
v_unused_1597_ = lean_ctor_get(v___x_1554_, 0);
lean_dec(v_unused_1597_);
v___x_1556_ = v___x_1554_;
v_isShared_1557_ = v_isSharedCheck_1596_;
goto v_resetjp_1555_;
}
else
{
lean_dec(v___x_1554_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1596_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v_leanOpts_1558_; lean_object* v_forwardedArgs_1559_; uint8_t v_component_1560_; uint8_t v_printPrefix_1561_; uint8_t v_printLibDir_1562_; uint8_t v_useStdin_1563_; uint8_t v_onlyDeps_1564_; uint8_t v_onlySrcDeps_1565_; uint8_t v_depsJson_1566_; lean_object* v_opts_1567_; uint32_t v_trustLevel_1568_; uint32_t v_numThreads_1569_; lean_object* v_rootDir_x3f_1570_; lean_object* v_setupFileName_x3f_1571_; lean_object* v_oleanFileName_x3f_1572_; lean_object* v_ileanFileName_x3f_1573_; lean_object* v_cFileName_x3f_1574_; lean_object* v_bcFileName_x3f_1575_; uint8_t v_jsonOutput_1576_; lean_object* v_errorOnKinds_1577_; uint8_t v_printStats_1578_; uint8_t v_run_1579_; lean_object* v_incrSaveFileName_x3f_1580_; lean_object* v_incrLoadFileName_x3f_1581_; lean_object* v_incrHeaderSaveFileName_x3f_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1595_; 
v_leanOpts_1558_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_1559_ = lean_ctor_get(v_opts_942_, 1);
v_component_1560_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_1561_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_1562_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_1563_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_1564_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1565_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_1566_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_1567_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_1568_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_1569_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1570_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_1571_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_1572_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_1573_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_1574_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_1575_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_1576_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_1577_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_1578_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_1579_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1580_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_1581_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_1582_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1584_ = v_opts_942_;
v_isShared_1585_ = v_isSharedCheck_1595_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1582_);
lean_inc(v_incrLoadFileName_x3f_1581_);
lean_inc(v_incrSaveFileName_x3f_1580_);
lean_inc(v_errorOnKinds_1577_);
lean_inc(v_bcFileName_x3f_1575_);
lean_inc(v_cFileName_x3f_1574_);
lean_inc(v_ileanFileName_x3f_1573_);
lean_inc(v_oleanFileName_x3f_1572_);
lean_inc(v_setupFileName_x3f_1571_);
lean_inc(v_rootDir_x3f_1570_);
lean_inc(v_opts_1567_);
lean_inc(v_forwardedArgs_1559_);
lean_inc(v_leanOpts_1558_);
lean_dec(v_opts_942_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1595_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1590_; 
v___x_1586_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9));
v___x_1587_ = lean_string_append(v___x_1586_, v_a_1547_);
lean_dec(v_a_1547_);
v___x_1588_ = lean_array_push(v_forwardedArgs_1559_, v___x_1587_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 1, v___x_1588_);
v___x_1590_ = v___x_1584_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_leanOpts_1558_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v___x_1588_);
lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_opts_1567_);
lean_ctor_set(v_reuseFailAlloc_1594_, 3, v_rootDir_x3f_1570_);
lean_ctor_set(v_reuseFailAlloc_1594_, 4, v_setupFileName_x3f_1571_);
lean_ctor_set(v_reuseFailAlloc_1594_, 5, v_oleanFileName_x3f_1572_);
lean_ctor_set(v_reuseFailAlloc_1594_, 6, v_ileanFileName_x3f_1573_);
lean_ctor_set(v_reuseFailAlloc_1594_, 7, v_cFileName_x3f_1574_);
lean_ctor_set(v_reuseFailAlloc_1594_, 8, v_bcFileName_x3f_1575_);
lean_ctor_set(v_reuseFailAlloc_1594_, 9, v_errorOnKinds_1577_);
lean_ctor_set(v_reuseFailAlloc_1594_, 10, v_incrSaveFileName_x3f_1580_);
lean_ctor_set(v_reuseFailAlloc_1594_, 11, v_incrLoadFileName_x3f_1581_);
lean_ctor_set(v_reuseFailAlloc_1594_, 12, v_incrHeaderSaveFileName_x3f_1582_);
lean_ctor_set_uint8(v_reuseFailAlloc_1594_, sizeof(void*)*13 + 8, v_component_1560_);
lean_ctor_set_uint8(v_reuseFailAlloc_1594_, sizeof(void*)*13 + 9, v_printPrefix_1561_);
lean_ctor_set_uint8(v_reuseFailAlloc_1594_, sizeof(void*)*13 + 10, v_printLibDir_1562_);
lean_ctor_set_uint8(v_reuseFailAlloc_1594_, sizeof(void*)*13 + 11, v_useStdin_1563_);
lean_ctor_set_uint8(v_reuseFailAlloc_1594_, sizeof(void*)*13 + 12, v_onlyDeps_1564_);
lean_ctor_set_uint8(v_reuseFailAlloc_1594_, sizeof(void*)*13 + 13, v_onlySrcDeps_1565_);
lean_ctor_set_uint8(v_reuseFailAlloc_1594_, sizeof(void*)*13 + 14, v_depsJson_1566_);
lean_ctor_set_uint32(v_reuseFailAlloc_1594_, sizeof(void*)*13, v_trustLevel_1568_);
lean_ctor_set_uint32(v_reuseFailAlloc_1594_, sizeof(void*)*13 + 4, v_numThreads_1569_);
lean_ctor_set_uint8(v_reuseFailAlloc_1594_, sizeof(void*)*13 + 15, v_jsonOutput_1576_);
lean_ctor_set_uint8(v_reuseFailAlloc_1594_, sizeof(void*)*13 + 16, v_printStats_1578_);
lean_ctor_set_uint8(v_reuseFailAlloc_1594_, sizeof(void*)*13 + 17, v_run_1579_);
v___x_1590_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
lean_object* v___x_1592_; 
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v___x_1590_);
v___x_1592_ = v___x_1556_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1590_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
lean_dec(v_a_1547_);
lean_dec_ref(v_opts_942_);
v_a_1598_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1598_);
lean_dec_ref_known(v___x_1554_, 1);
v___x_1599_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1600_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1599_);
lean_dec_ref(v___x_1600_);
v___y_1104_ = v_a_1598_;
goto v___jp_1103_;
}
}
v___jp_1601_:
{
lean_object* v___x_1603_; uint8_t v___x_1604_; 
v___x_1603_ = lean_string_utf8_byte_size(v_a_1547_);
v___x_1604_ = lean_nat_dec_eq(v___y_1602_, v___x_1603_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1610_; 
v___x_1605_ = lean_unsigned_to_nat(0u);
v___x_1606_ = lean_string_utf8_next_fast(v_a_1547_, v___y_1602_);
v___x_1607_ = lean_string_utf8_extract(v_a_1547_, v___x_1605_, v___y_1602_);
lean_dec(v___y_1602_);
v___x_1608_ = lean_string_utf8_extract(v_a_1547_, v___x_1606_, v___x_1603_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set_tag(v___x_1549_, 1);
lean_ctor_set(v___x_1549_, 0, v___x_1608_);
v___x_1610_ = v___x_1549_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1608_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
v_fst_1552_ = v___x_1607_;
v_snd_1553_ = v___x_1610_;
goto v___jp_1551_;
}
}
else
{
lean_object* v___x_1612_; 
lean_dec(v___y_1602_);
lean_del_object(v___x_1549_);
v___x_1612_ = lean_box(0);
lean_inc(v_a_1547_);
v_fst_1552_ = v_a_1547_;
v_snd_1553_ = v___x_1612_;
goto v___jp_1551_;
}
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
lean_dec_ref(v_opts_942_);
v_a_1620_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1546_, 1);
v___x_1624_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1625_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1624_);
lean_dec_ref(v___x_1625_);
goto v___jp_1621_;
v___jp_1621_:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = lean_io_error_to_string(v_a_1620_);
v___x_1623_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1622_);
lean_dec_ref(v___x_1623_);
goto v___jp_1024_;
}
}
}
}
else
{
uint8_t v___x_1626_; 
v___x_1626_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__16, &l___private_Lean_Shell_0__Lean_displayHelp___closed__16_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__16);
if (v___x_1626_ == 0)
{
lean_dec(v_optArg_x3f_944_);
lean_dec_ref(v_opts_942_);
goto v___jp_1076_;
}
else
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10));
v___x_1628_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1627_, v_optArg_x3f_944_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1637_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1637_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1637_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; lean_object* v___x_1635_; 
v___x_1633_ = lean_internal_enable_debug(v_a_1629_);
lean_dec(v_a_1629_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v_opts_942_);
v___x_1635_ = v___x_1631_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_opts_942_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
lean_dec_ref(v_opts_942_);
v_a_1638_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1638_);
lean_dec_ref_known(v___x_1628_, 1);
v___x_1642_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1643_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1642_);
lean_dec_ref(v___x_1643_);
goto v___jp_1639_;
v___jp_1639_:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = lean_io_error_to_string(v_a_1638_);
v___x_1641_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1640_);
lean_dec_ref(v___x_1641_);
goto v___jp_1110_;
}
}
}
}
}
else
{
lean_object* v_leanOpts_1644_; lean_object* v_forwardedArgs_1645_; uint8_t v_component_1646_; uint8_t v_printPrefix_1647_; uint8_t v_printLibDir_1648_; uint8_t v_useStdin_1649_; uint8_t v_onlyDeps_1650_; uint8_t v_onlySrcDeps_1651_; uint8_t v_depsJson_1652_; lean_object* v_opts_1653_; uint32_t v_trustLevel_1654_; uint32_t v_numThreads_1655_; lean_object* v_rootDir_x3f_1656_; lean_object* v_setupFileName_x3f_1657_; lean_object* v_oleanFileName_x3f_1658_; lean_object* v_ileanFileName_x3f_1659_; lean_object* v_cFileName_x3f_1660_; lean_object* v_bcFileName_x3f_1661_; uint8_t v_jsonOutput_1662_; lean_object* v_errorOnKinds_1663_; uint8_t v_printStats_1664_; uint8_t v_run_1665_; lean_object* v_incrSaveFileName_x3f_1666_; lean_object* v_incrLoadFileName_x3f_1667_; lean_object* v_incrHeaderSaveFileName_x3f_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1678_; 
lean_dec(v_optArg_x3f_944_);
v_leanOpts_1644_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_1645_ = lean_ctor_get(v_opts_942_, 1);
v_component_1646_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_1647_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_1648_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_1649_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_1650_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1651_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_1652_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_1653_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_1654_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_1655_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1656_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_1657_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_1658_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_1659_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_1660_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_1661_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_1662_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_1663_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_1664_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_1665_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1666_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_1667_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_1668_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_1678_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1670_ = v_opts_942_;
v_isShared_1671_ = v_isSharedCheck_1678_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1668_);
lean_inc(v_incrLoadFileName_x3f_1667_);
lean_inc(v_incrSaveFileName_x3f_1666_);
lean_inc(v_errorOnKinds_1663_);
lean_inc(v_bcFileName_x3f_1661_);
lean_inc(v_cFileName_x3f_1660_);
lean_inc(v_ileanFileName_x3f_1659_);
lean_inc(v_oleanFileName_x3f_1658_);
lean_inc(v_setupFileName_x3f_1657_);
lean_inc(v_rootDir_x3f_1656_);
lean_inc(v_opts_1653_);
lean_inc(v_forwardedArgs_1645_);
lean_inc(v_leanOpts_1644_);
lean_dec(v_opts_942_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1678_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1672_ = l_Lean_profiler;
v___x_1673_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_1644_, v___x_1672_, v___x_1223_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___x_1673_);
v___x_1675_ = v___x_1670_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v_forwardedArgs_1645_);
lean_ctor_set(v_reuseFailAlloc_1677_, 2, v_opts_1653_);
lean_ctor_set(v_reuseFailAlloc_1677_, 3, v_rootDir_x3f_1656_);
lean_ctor_set(v_reuseFailAlloc_1677_, 4, v_setupFileName_x3f_1657_);
lean_ctor_set(v_reuseFailAlloc_1677_, 5, v_oleanFileName_x3f_1658_);
lean_ctor_set(v_reuseFailAlloc_1677_, 6, v_ileanFileName_x3f_1659_);
lean_ctor_set(v_reuseFailAlloc_1677_, 7, v_cFileName_x3f_1660_);
lean_ctor_set(v_reuseFailAlloc_1677_, 8, v_bcFileName_x3f_1661_);
lean_ctor_set(v_reuseFailAlloc_1677_, 9, v_errorOnKinds_1663_);
lean_ctor_set(v_reuseFailAlloc_1677_, 10, v_incrSaveFileName_x3f_1666_);
lean_ctor_set(v_reuseFailAlloc_1677_, 11, v_incrLoadFileName_x3f_1667_);
lean_ctor_set(v_reuseFailAlloc_1677_, 12, v_incrHeaderSaveFileName_x3f_1668_);
lean_ctor_set_uint8(v_reuseFailAlloc_1677_, sizeof(void*)*13 + 8, v_component_1646_);
lean_ctor_set_uint8(v_reuseFailAlloc_1677_, sizeof(void*)*13 + 9, v_printPrefix_1647_);
lean_ctor_set_uint8(v_reuseFailAlloc_1677_, sizeof(void*)*13 + 10, v_printLibDir_1648_);
lean_ctor_set_uint8(v_reuseFailAlloc_1677_, sizeof(void*)*13 + 11, v_useStdin_1649_);
lean_ctor_set_uint8(v_reuseFailAlloc_1677_, sizeof(void*)*13 + 12, v_onlyDeps_1650_);
lean_ctor_set_uint8(v_reuseFailAlloc_1677_, sizeof(void*)*13 + 13, v_onlySrcDeps_1651_);
lean_ctor_set_uint8(v_reuseFailAlloc_1677_, sizeof(void*)*13 + 14, v_depsJson_1652_);
lean_ctor_set_uint32(v_reuseFailAlloc_1677_, sizeof(void*)*13, v_trustLevel_1654_);
lean_ctor_set_uint32(v_reuseFailAlloc_1677_, sizeof(void*)*13 + 4, v_numThreads_1655_);
lean_ctor_set_uint8(v_reuseFailAlloc_1677_, sizeof(void*)*13 + 15, v_jsonOutput_1662_);
lean_ctor_set_uint8(v_reuseFailAlloc_1677_, sizeof(void*)*13 + 16, v_printStats_1664_);
lean_ctor_set_uint8(v_reuseFailAlloc_1677_, sizeof(void*)*13 + 17, v_run_1665_);
v___x_1675_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v___x_1676_; 
v___x_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1675_);
return v___x_1676_;
}
}
}
}
else
{
lean_object* v_leanOpts_1679_; lean_object* v_forwardedArgs_1680_; uint8_t v_printPrefix_1681_; uint8_t v_printLibDir_1682_; uint8_t v_useStdin_1683_; uint8_t v_onlyDeps_1684_; uint8_t v_onlySrcDeps_1685_; uint8_t v_depsJson_1686_; lean_object* v_opts_1687_; uint32_t v_trustLevel_1688_; uint32_t v_numThreads_1689_; lean_object* v_rootDir_x3f_1690_; lean_object* v_setupFileName_x3f_1691_; lean_object* v_oleanFileName_x3f_1692_; lean_object* v_ileanFileName_x3f_1693_; lean_object* v_cFileName_x3f_1694_; lean_object* v_bcFileName_x3f_1695_; uint8_t v_jsonOutput_1696_; lean_object* v_errorOnKinds_1697_; uint8_t v_printStats_1698_; uint8_t v_run_1699_; lean_object* v_incrSaveFileName_x3f_1700_; lean_object* v_incrLoadFileName_x3f_1701_; lean_object* v_incrHeaderSaveFileName_x3f_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1711_; 
lean_dec(v_optArg_x3f_944_);
v_leanOpts_1679_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_1680_ = lean_ctor_get(v_opts_942_, 1);
v_printPrefix_1681_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_1682_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_1683_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_1684_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1685_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_1686_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_1687_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_1688_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_1689_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1690_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_1691_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_1692_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_1693_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_1694_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_1695_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_1696_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_1697_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_1698_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_1699_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1700_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_1701_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_1702_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1704_ = v_opts_942_;
v_isShared_1705_ = v_isSharedCheck_1711_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1702_);
lean_inc(v_incrLoadFileName_x3f_1701_);
lean_inc(v_incrSaveFileName_x3f_1700_);
lean_inc(v_errorOnKinds_1697_);
lean_inc(v_bcFileName_x3f_1695_);
lean_inc(v_cFileName_x3f_1694_);
lean_inc(v_ileanFileName_x3f_1693_);
lean_inc(v_oleanFileName_x3f_1692_);
lean_inc(v_setupFileName_x3f_1691_);
lean_inc(v_rootDir_x3f_1690_);
lean_inc(v_opts_1687_);
lean_inc(v_forwardedArgs_1680_);
lean_inc(v_leanOpts_1679_);
lean_dec(v_opts_942_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1711_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
uint8_t v___x_1706_; lean_object* v___x_1708_; 
v___x_1706_ = 2;
if (v_isShared_1705_ == 0)
{
v___x_1708_ = v___x_1704_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_leanOpts_1679_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_forwardedArgs_1680_);
lean_ctor_set(v_reuseFailAlloc_1710_, 2, v_opts_1687_);
lean_ctor_set(v_reuseFailAlloc_1710_, 3, v_rootDir_x3f_1690_);
lean_ctor_set(v_reuseFailAlloc_1710_, 4, v_setupFileName_x3f_1691_);
lean_ctor_set(v_reuseFailAlloc_1710_, 5, v_oleanFileName_x3f_1692_);
lean_ctor_set(v_reuseFailAlloc_1710_, 6, v_ileanFileName_x3f_1693_);
lean_ctor_set(v_reuseFailAlloc_1710_, 7, v_cFileName_x3f_1694_);
lean_ctor_set(v_reuseFailAlloc_1710_, 8, v_bcFileName_x3f_1695_);
lean_ctor_set(v_reuseFailAlloc_1710_, 9, v_errorOnKinds_1697_);
lean_ctor_set(v_reuseFailAlloc_1710_, 10, v_incrSaveFileName_x3f_1700_);
lean_ctor_set(v_reuseFailAlloc_1710_, 11, v_incrLoadFileName_x3f_1701_);
lean_ctor_set(v_reuseFailAlloc_1710_, 12, v_incrHeaderSaveFileName_x3f_1702_);
lean_ctor_set_uint8(v_reuseFailAlloc_1710_, sizeof(void*)*13 + 9, v_printPrefix_1681_);
lean_ctor_set_uint8(v_reuseFailAlloc_1710_, sizeof(void*)*13 + 10, v_printLibDir_1682_);
lean_ctor_set_uint8(v_reuseFailAlloc_1710_, sizeof(void*)*13 + 11, v_useStdin_1683_);
lean_ctor_set_uint8(v_reuseFailAlloc_1710_, sizeof(void*)*13 + 12, v_onlyDeps_1684_);
lean_ctor_set_uint8(v_reuseFailAlloc_1710_, sizeof(void*)*13 + 13, v_onlySrcDeps_1685_);
lean_ctor_set_uint8(v_reuseFailAlloc_1710_, sizeof(void*)*13 + 14, v_depsJson_1686_);
lean_ctor_set_uint32(v_reuseFailAlloc_1710_, sizeof(void*)*13, v_trustLevel_1688_);
lean_ctor_set_uint32(v_reuseFailAlloc_1710_, sizeof(void*)*13 + 4, v_numThreads_1689_);
lean_ctor_set_uint8(v_reuseFailAlloc_1710_, sizeof(void*)*13 + 15, v_jsonOutput_1696_);
lean_ctor_set_uint8(v_reuseFailAlloc_1710_, sizeof(void*)*13 + 16, v_printStats_1698_);
lean_ctor_set_uint8(v_reuseFailAlloc_1710_, sizeof(void*)*13 + 17, v_run_1699_);
v___x_1708_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
lean_object* v___x_1709_; 
lean_ctor_set_uint8(v___x_1708_, sizeof(void*)*13 + 8, v___x_1706_);
v___x_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1708_);
return v___x_1709_;
}
}
}
}
else
{
lean_object* v_leanOpts_1712_; lean_object* v_forwardedArgs_1713_; uint8_t v_printPrefix_1714_; uint8_t v_printLibDir_1715_; uint8_t v_useStdin_1716_; uint8_t v_onlyDeps_1717_; uint8_t v_onlySrcDeps_1718_; uint8_t v_depsJson_1719_; lean_object* v_opts_1720_; uint32_t v_trustLevel_1721_; uint32_t v_numThreads_1722_; lean_object* v_rootDir_x3f_1723_; lean_object* v_setupFileName_x3f_1724_; lean_object* v_oleanFileName_x3f_1725_; lean_object* v_ileanFileName_x3f_1726_; lean_object* v_cFileName_x3f_1727_; lean_object* v_bcFileName_x3f_1728_; uint8_t v_jsonOutput_1729_; lean_object* v_errorOnKinds_1730_; uint8_t v_printStats_1731_; uint8_t v_run_1732_; lean_object* v_incrSaveFileName_x3f_1733_; lean_object* v_incrLoadFileName_x3f_1734_; lean_object* v_incrHeaderSaveFileName_x3f_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1744_; 
lean_dec(v_optArg_x3f_944_);
v_leanOpts_1712_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_1713_ = lean_ctor_get(v_opts_942_, 1);
v_printPrefix_1714_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_1715_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_1716_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_1717_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1718_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_1719_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_1720_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_1721_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_1722_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1723_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_1724_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_1725_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_1726_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_1727_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_1728_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_1729_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_1730_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_1731_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_1732_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1733_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_1734_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_1735_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1737_ = v_opts_942_;
v_isShared_1738_ = v_isSharedCheck_1744_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1735_);
lean_inc(v_incrLoadFileName_x3f_1734_);
lean_inc(v_incrSaveFileName_x3f_1733_);
lean_inc(v_errorOnKinds_1730_);
lean_inc(v_bcFileName_x3f_1728_);
lean_inc(v_cFileName_x3f_1727_);
lean_inc(v_ileanFileName_x3f_1726_);
lean_inc(v_oleanFileName_x3f_1725_);
lean_inc(v_setupFileName_x3f_1724_);
lean_inc(v_rootDir_x3f_1723_);
lean_inc(v_opts_1720_);
lean_inc(v_forwardedArgs_1713_);
lean_inc(v_leanOpts_1712_);
lean_dec(v_opts_942_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1744_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
uint8_t v___x_1739_; lean_object* v___x_1741_; 
v___x_1739_ = 1;
if (v_isShared_1738_ == 0)
{
v___x_1741_ = v___x_1737_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_leanOpts_1712_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v_forwardedArgs_1713_);
lean_ctor_set(v_reuseFailAlloc_1743_, 2, v_opts_1720_);
lean_ctor_set(v_reuseFailAlloc_1743_, 3, v_rootDir_x3f_1723_);
lean_ctor_set(v_reuseFailAlloc_1743_, 4, v_setupFileName_x3f_1724_);
lean_ctor_set(v_reuseFailAlloc_1743_, 5, v_oleanFileName_x3f_1725_);
lean_ctor_set(v_reuseFailAlloc_1743_, 6, v_ileanFileName_x3f_1726_);
lean_ctor_set(v_reuseFailAlloc_1743_, 7, v_cFileName_x3f_1727_);
lean_ctor_set(v_reuseFailAlloc_1743_, 8, v_bcFileName_x3f_1728_);
lean_ctor_set(v_reuseFailAlloc_1743_, 9, v_errorOnKinds_1730_);
lean_ctor_set(v_reuseFailAlloc_1743_, 10, v_incrSaveFileName_x3f_1733_);
lean_ctor_set(v_reuseFailAlloc_1743_, 11, v_incrLoadFileName_x3f_1734_);
lean_ctor_set(v_reuseFailAlloc_1743_, 12, v_incrHeaderSaveFileName_x3f_1735_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*13 + 9, v_printPrefix_1714_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*13 + 10, v_printLibDir_1715_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*13 + 11, v_useStdin_1716_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*13 + 12, v_onlyDeps_1717_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*13 + 13, v_onlySrcDeps_1718_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*13 + 14, v_depsJson_1719_);
lean_ctor_set_uint32(v_reuseFailAlloc_1743_, sizeof(void*)*13, v_trustLevel_1721_);
lean_ctor_set_uint32(v_reuseFailAlloc_1743_, sizeof(void*)*13 + 4, v_numThreads_1722_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*13 + 15, v_jsonOutput_1729_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*13 + 16, v_printStats_1731_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*13 + 17, v_run_1732_);
v___x_1741_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1742_; 
lean_ctor_set_uint8(v___x_1741_, sizeof(void*)*13 + 8, v___x_1739_);
v___x_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
return v___x_1742_;
}
}
}
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11));
v___x_1746_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1745_, v_optArg_x3f_944_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v_leanOpts_1748_; lean_object* v_forwardedArgs_1749_; uint8_t v_component_1750_; uint8_t v_printPrefix_1751_; uint8_t v_printLibDir_1752_; uint8_t v_useStdin_1753_; uint8_t v_onlyDeps_1754_; uint8_t v_onlySrcDeps_1755_; uint8_t v_depsJson_1756_; lean_object* v_opts_1757_; uint32_t v_trustLevel_1758_; uint32_t v_numThreads_1759_; lean_object* v_rootDir_x3f_1760_; lean_object* v_setupFileName_x3f_1761_; lean_object* v_oleanFileName_x3f_1762_; lean_object* v_ileanFileName_x3f_1763_; lean_object* v_cFileName_x3f_1764_; lean_object* v_bcFileName_x3f_1765_; uint8_t v_jsonOutput_1766_; lean_object* v_errorOnKinds_1767_; uint8_t v_printStats_1768_; uint8_t v_run_1769_; lean_object* v_incrSaveFileName_x3f_1770_; lean_object* v_incrLoadFileName_x3f_1771_; lean_object* v_incrHeaderSaveFileName_x3f_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1797_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref_known(v___x_1746_, 1);
v_leanOpts_1748_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_1749_ = lean_ctor_get(v_opts_942_, 1);
v_component_1750_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_1751_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_1752_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_1753_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_1754_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1755_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_1756_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_1757_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_1758_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_1759_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1760_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_1761_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_1762_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_1763_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_1764_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_1765_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_1766_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_1767_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_1768_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_1769_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1770_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_1771_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_1772_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1774_ = v_opts_942_;
v_isShared_1775_ = v_isSharedCheck_1797_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1772_);
lean_inc(v_incrLoadFileName_x3f_1771_);
lean_inc(v_incrSaveFileName_x3f_1770_);
lean_inc(v_errorOnKinds_1767_);
lean_inc(v_bcFileName_x3f_1765_);
lean_inc(v_cFileName_x3f_1764_);
lean_inc(v_ileanFileName_x3f_1763_);
lean_inc(v_oleanFileName_x3f_1762_);
lean_inc(v_setupFileName_x3f_1761_);
lean_inc(v_rootDir_x3f_1760_);
lean_inc(v_opts_1757_);
lean_inc(v_forwardedArgs_1749_);
lean_inc(v_leanOpts_1748_);
lean_dec(v_opts_942_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1797_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1776_; 
lean_inc(v_a_1747_);
v___x_1776_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_leanOpts_1748_, v_a_1747_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1790_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1779_ = v___x_1776_;
v_isShared_1780_ = v_isSharedCheck_1790_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1776_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1790_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1785_; 
v___x_1781_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12));
v___x_1782_ = lean_string_append(v___x_1781_, v_a_1747_);
lean_dec(v_a_1747_);
v___x_1783_ = lean_array_push(v_forwardedArgs_1749_, v___x_1782_);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 1, v___x_1783_);
lean_ctor_set(v___x_1774_, 0, v_a_1777_);
v___x_1785_ = v___x_1774_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1777_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v___x_1783_);
lean_ctor_set(v_reuseFailAlloc_1789_, 2, v_opts_1757_);
lean_ctor_set(v_reuseFailAlloc_1789_, 3, v_rootDir_x3f_1760_);
lean_ctor_set(v_reuseFailAlloc_1789_, 4, v_setupFileName_x3f_1761_);
lean_ctor_set(v_reuseFailAlloc_1789_, 5, v_oleanFileName_x3f_1762_);
lean_ctor_set(v_reuseFailAlloc_1789_, 6, v_ileanFileName_x3f_1763_);
lean_ctor_set(v_reuseFailAlloc_1789_, 7, v_cFileName_x3f_1764_);
lean_ctor_set(v_reuseFailAlloc_1789_, 8, v_bcFileName_x3f_1765_);
lean_ctor_set(v_reuseFailAlloc_1789_, 9, v_errorOnKinds_1767_);
lean_ctor_set(v_reuseFailAlloc_1789_, 10, v_incrSaveFileName_x3f_1770_);
lean_ctor_set(v_reuseFailAlloc_1789_, 11, v_incrLoadFileName_x3f_1771_);
lean_ctor_set(v_reuseFailAlloc_1789_, 12, v_incrHeaderSaveFileName_x3f_1772_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*13 + 8, v_component_1750_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*13 + 9, v_printPrefix_1751_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*13 + 10, v_printLibDir_1752_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*13 + 11, v_useStdin_1753_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*13 + 12, v_onlyDeps_1754_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*13 + 13, v_onlySrcDeps_1755_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*13 + 14, v_depsJson_1756_);
lean_ctor_set_uint32(v_reuseFailAlloc_1789_, sizeof(void*)*13, v_trustLevel_1758_);
lean_ctor_set_uint32(v_reuseFailAlloc_1789_, sizeof(void*)*13 + 4, v_numThreads_1759_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*13 + 15, v_jsonOutput_1766_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*13 + 16, v_printStats_1768_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*13 + 17, v_run_1769_);
v___x_1785_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
lean_object* v___x_1787_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1785_);
v___x_1787_ = v___x_1779_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_del_object(v___x_1774_);
lean_dec(v_incrHeaderSaveFileName_x3f_1772_);
lean_dec(v_incrLoadFileName_x3f_1771_);
lean_dec(v_incrSaveFileName_x3f_1770_);
lean_dec_ref(v_errorOnKinds_1767_);
lean_dec(v_bcFileName_x3f_1765_);
lean_dec(v_cFileName_x3f_1764_);
lean_dec(v_ileanFileName_x3f_1763_);
lean_dec(v_oleanFileName_x3f_1762_);
lean_dec(v_setupFileName_x3f_1761_);
lean_dec(v_rootDir_x3f_1760_);
lean_dec_ref(v_opts_1757_);
lean_dec_ref(v_forwardedArgs_1749_);
lean_dec(v_a_1747_);
v_a_1791_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1776_, 1);
v___x_1795_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1796_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1795_);
lean_dec_ref(v___x_1796_);
goto v___jp_1792_;
v___jp_1792_:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = lean_io_error_to_string(v_a_1791_);
v___x_1794_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1793_);
lean_dec_ref(v___x_1794_);
goto v___jp_1018_;
}
}
}
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
lean_dec_ref(v_opts_942_);
v_a_1798_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1798_);
lean_dec_ref_known(v___x_1746_, 1);
v___x_1802_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1803_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1802_);
lean_dec_ref(v___x_1803_);
goto v___jp_1799_;
v___jp_1799_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = lean_io_error_to_string(v_a_1798_);
v___x_1801_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1800_);
lean_dec_ref(v___x_1801_);
goto v___jp_1116_;
}
}
}
}
else
{
lean_object* v_leanOpts_1804_; lean_object* v_forwardedArgs_1805_; uint8_t v_component_1806_; uint8_t v_printPrefix_1807_; uint8_t v_useStdin_1808_; uint8_t v_onlyDeps_1809_; uint8_t v_onlySrcDeps_1810_; uint8_t v_depsJson_1811_; lean_object* v_opts_1812_; uint32_t v_trustLevel_1813_; uint32_t v_numThreads_1814_; lean_object* v_rootDir_x3f_1815_; lean_object* v_setupFileName_x3f_1816_; lean_object* v_oleanFileName_x3f_1817_; lean_object* v_ileanFileName_x3f_1818_; lean_object* v_cFileName_x3f_1819_; lean_object* v_bcFileName_x3f_1820_; uint8_t v_jsonOutput_1821_; lean_object* v_errorOnKinds_1822_; uint8_t v_printStats_1823_; uint8_t v_run_1824_; lean_object* v_incrSaveFileName_x3f_1825_; lean_object* v_incrLoadFileName_x3f_1826_; lean_object* v_incrHeaderSaveFileName_x3f_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1835_; 
lean_dec(v_optArg_x3f_944_);
v_leanOpts_1804_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_1805_ = lean_ctor_get(v_opts_942_, 1);
v_component_1806_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_1807_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_useStdin_1808_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_1809_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1810_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_1811_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_1812_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_1813_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_1814_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1815_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_1816_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_1817_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_1818_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_1819_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_1820_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_1821_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_1822_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_1823_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_1824_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1825_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_1826_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_1827_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1829_ = v_opts_942_;
v_isShared_1830_ = v_isSharedCheck_1835_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1827_);
lean_inc(v_incrLoadFileName_x3f_1826_);
lean_inc(v_incrSaveFileName_x3f_1825_);
lean_inc(v_errorOnKinds_1822_);
lean_inc(v_bcFileName_x3f_1820_);
lean_inc(v_cFileName_x3f_1819_);
lean_inc(v_ileanFileName_x3f_1818_);
lean_inc(v_oleanFileName_x3f_1817_);
lean_inc(v_setupFileName_x3f_1816_);
lean_inc(v_rootDir_x3f_1815_);
lean_inc(v_opts_1812_);
lean_inc(v_forwardedArgs_1805_);
lean_inc(v_leanOpts_1804_);
lean_dec(v_opts_942_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1835_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_leanOpts_1804_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_forwardedArgs_1805_);
lean_ctor_set(v_reuseFailAlloc_1834_, 2, v_opts_1812_);
lean_ctor_set(v_reuseFailAlloc_1834_, 3, v_rootDir_x3f_1815_);
lean_ctor_set(v_reuseFailAlloc_1834_, 4, v_setupFileName_x3f_1816_);
lean_ctor_set(v_reuseFailAlloc_1834_, 5, v_oleanFileName_x3f_1817_);
lean_ctor_set(v_reuseFailAlloc_1834_, 6, v_ileanFileName_x3f_1818_);
lean_ctor_set(v_reuseFailAlloc_1834_, 7, v_cFileName_x3f_1819_);
lean_ctor_set(v_reuseFailAlloc_1834_, 8, v_bcFileName_x3f_1820_);
lean_ctor_set(v_reuseFailAlloc_1834_, 9, v_errorOnKinds_1822_);
lean_ctor_set(v_reuseFailAlloc_1834_, 10, v_incrSaveFileName_x3f_1825_);
lean_ctor_set(v_reuseFailAlloc_1834_, 11, v_incrLoadFileName_x3f_1826_);
lean_ctor_set(v_reuseFailAlloc_1834_, 12, v_incrHeaderSaveFileName_x3f_1827_);
lean_ctor_set_uint8(v_reuseFailAlloc_1834_, sizeof(void*)*13 + 8, v_component_1806_);
lean_ctor_set_uint8(v_reuseFailAlloc_1834_, sizeof(void*)*13 + 9, v_printPrefix_1807_);
lean_ctor_set_uint8(v_reuseFailAlloc_1834_, sizeof(void*)*13 + 11, v_useStdin_1808_);
lean_ctor_set_uint8(v_reuseFailAlloc_1834_, sizeof(void*)*13 + 12, v_onlyDeps_1809_);
lean_ctor_set_uint8(v_reuseFailAlloc_1834_, sizeof(void*)*13 + 13, v_onlySrcDeps_1810_);
lean_ctor_set_uint8(v_reuseFailAlloc_1834_, sizeof(void*)*13 + 14, v_depsJson_1811_);
lean_ctor_set_uint32(v_reuseFailAlloc_1834_, sizeof(void*)*13, v_trustLevel_1813_);
lean_ctor_set_uint32(v_reuseFailAlloc_1834_, sizeof(void*)*13 + 4, v_numThreads_1814_);
lean_ctor_set_uint8(v_reuseFailAlloc_1834_, sizeof(void*)*13 + 15, v_jsonOutput_1821_);
lean_ctor_set_uint8(v_reuseFailAlloc_1834_, sizeof(void*)*13 + 16, v_printStats_1823_);
lean_ctor_set_uint8(v_reuseFailAlloc_1834_, sizeof(void*)*13 + 17, v_run_1824_);
v___x_1832_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
lean_object* v___x_1833_; 
lean_ctor_set_uint8(v___x_1832_, sizeof(void*)*13 + 10, v___x_1215_);
v___x_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
return v___x_1833_;
}
}
}
}
else
{
lean_object* v_leanOpts_1836_; lean_object* v_forwardedArgs_1837_; uint8_t v_component_1838_; uint8_t v_printLibDir_1839_; uint8_t v_useStdin_1840_; uint8_t v_onlyDeps_1841_; uint8_t v_onlySrcDeps_1842_; uint8_t v_depsJson_1843_; lean_object* v_opts_1844_; uint32_t v_trustLevel_1845_; uint32_t v_numThreads_1846_; lean_object* v_rootDir_x3f_1847_; lean_object* v_setupFileName_x3f_1848_; lean_object* v_oleanFileName_x3f_1849_; lean_object* v_ileanFileName_x3f_1850_; lean_object* v_cFileName_x3f_1851_; lean_object* v_bcFileName_x3f_1852_; uint8_t v_jsonOutput_1853_; lean_object* v_errorOnKinds_1854_; uint8_t v_printStats_1855_; uint8_t v_run_1856_; lean_object* v_incrSaveFileName_x3f_1857_; lean_object* v_incrLoadFileName_x3f_1858_; lean_object* v_incrHeaderSaveFileName_x3f_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1867_; 
lean_dec(v_optArg_x3f_944_);
v_leanOpts_1836_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_1837_ = lean_ctor_get(v_opts_942_, 1);
v_component_1838_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printLibDir_1839_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_1840_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_1841_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1842_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_1843_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_1844_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_1845_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_1846_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1847_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_1848_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_1849_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_1850_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_1851_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_1852_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_1853_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_1854_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_1855_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_1856_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1857_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_1858_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_1859_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1861_ = v_opts_942_;
v_isShared_1862_ = v_isSharedCheck_1867_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1859_);
lean_inc(v_incrLoadFileName_x3f_1858_);
lean_inc(v_incrSaveFileName_x3f_1857_);
lean_inc(v_errorOnKinds_1854_);
lean_inc(v_bcFileName_x3f_1852_);
lean_inc(v_cFileName_x3f_1851_);
lean_inc(v_ileanFileName_x3f_1850_);
lean_inc(v_oleanFileName_x3f_1849_);
lean_inc(v_setupFileName_x3f_1848_);
lean_inc(v_rootDir_x3f_1847_);
lean_inc(v_opts_1844_);
lean_inc(v_forwardedArgs_1837_);
lean_inc(v_leanOpts_1836_);
lean_dec(v_opts_942_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1867_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_leanOpts_1836_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_forwardedArgs_1837_);
lean_ctor_set(v_reuseFailAlloc_1866_, 2, v_opts_1844_);
lean_ctor_set(v_reuseFailAlloc_1866_, 3, v_rootDir_x3f_1847_);
lean_ctor_set(v_reuseFailAlloc_1866_, 4, v_setupFileName_x3f_1848_);
lean_ctor_set(v_reuseFailAlloc_1866_, 5, v_oleanFileName_x3f_1849_);
lean_ctor_set(v_reuseFailAlloc_1866_, 6, v_ileanFileName_x3f_1850_);
lean_ctor_set(v_reuseFailAlloc_1866_, 7, v_cFileName_x3f_1851_);
lean_ctor_set(v_reuseFailAlloc_1866_, 8, v_bcFileName_x3f_1852_);
lean_ctor_set(v_reuseFailAlloc_1866_, 9, v_errorOnKinds_1854_);
lean_ctor_set(v_reuseFailAlloc_1866_, 10, v_incrSaveFileName_x3f_1857_);
lean_ctor_set(v_reuseFailAlloc_1866_, 11, v_incrLoadFileName_x3f_1858_);
lean_ctor_set(v_reuseFailAlloc_1866_, 12, v_incrHeaderSaveFileName_x3f_1859_);
lean_ctor_set_uint8(v_reuseFailAlloc_1866_, sizeof(void*)*13 + 8, v_component_1838_);
lean_ctor_set_uint8(v_reuseFailAlloc_1866_, sizeof(void*)*13 + 10, v_printLibDir_1839_);
lean_ctor_set_uint8(v_reuseFailAlloc_1866_, sizeof(void*)*13 + 11, v_useStdin_1840_);
lean_ctor_set_uint8(v_reuseFailAlloc_1866_, sizeof(void*)*13 + 12, v_onlyDeps_1841_);
lean_ctor_set_uint8(v_reuseFailAlloc_1866_, sizeof(void*)*13 + 13, v_onlySrcDeps_1842_);
lean_ctor_set_uint8(v_reuseFailAlloc_1866_, sizeof(void*)*13 + 14, v_depsJson_1843_);
lean_ctor_set_uint32(v_reuseFailAlloc_1866_, sizeof(void*)*13, v_trustLevel_1845_);
lean_ctor_set_uint32(v_reuseFailAlloc_1866_, sizeof(void*)*13 + 4, v_numThreads_1846_);
lean_ctor_set_uint8(v_reuseFailAlloc_1866_, sizeof(void*)*13 + 15, v_jsonOutput_1853_);
lean_ctor_set_uint8(v_reuseFailAlloc_1866_, sizeof(void*)*13 + 16, v_printStats_1855_);
lean_ctor_set_uint8(v_reuseFailAlloc_1866_, sizeof(void*)*13 + 17, v_run_1856_);
v___x_1864_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1865_; 
lean_ctor_set_uint8(v___x_1864_, sizeof(void*)*13 + 9, v___x_1213_);
v___x_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
return v___x_1865_;
}
}
}
}
else
{
lean_object* v_leanOpts_1868_; lean_object* v_forwardedArgs_1869_; uint8_t v_component_1870_; uint8_t v_printPrefix_1871_; uint8_t v_printLibDir_1872_; uint8_t v_useStdin_1873_; uint8_t v_onlyDeps_1874_; uint8_t v_onlySrcDeps_1875_; uint8_t v_depsJson_1876_; lean_object* v_opts_1877_; uint32_t v_trustLevel_1878_; uint32_t v_numThreads_1879_; lean_object* v_rootDir_x3f_1880_; lean_object* v_setupFileName_x3f_1881_; lean_object* v_oleanFileName_x3f_1882_; lean_object* v_ileanFileName_x3f_1883_; lean_object* v_cFileName_x3f_1884_; lean_object* v_bcFileName_x3f_1885_; uint8_t v_jsonOutput_1886_; lean_object* v_errorOnKinds_1887_; uint8_t v_run_1888_; lean_object* v_incrSaveFileName_x3f_1889_; lean_object* v_incrLoadFileName_x3f_1890_; lean_object* v_incrHeaderSaveFileName_x3f_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1899_; 
lean_dec(v_optArg_x3f_944_);
v_leanOpts_1868_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_1869_ = lean_ctor_get(v_opts_942_, 1);
v_component_1870_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_1871_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_1872_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_1873_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_1874_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1875_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_1876_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_1877_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_1878_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_1879_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1880_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_1881_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_1882_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_1883_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_1884_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_1885_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_1886_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_1887_ = lean_ctor_get(v_opts_942_, 9);
v_run_1888_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1889_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_1890_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_1891_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1893_ = v_opts_942_;
v_isShared_1894_ = v_isSharedCheck_1899_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1891_);
lean_inc(v_incrLoadFileName_x3f_1890_);
lean_inc(v_incrSaveFileName_x3f_1889_);
lean_inc(v_errorOnKinds_1887_);
lean_inc(v_bcFileName_x3f_1885_);
lean_inc(v_cFileName_x3f_1884_);
lean_inc(v_ileanFileName_x3f_1883_);
lean_inc(v_oleanFileName_x3f_1882_);
lean_inc(v_setupFileName_x3f_1881_);
lean_inc(v_rootDir_x3f_1880_);
lean_inc(v_opts_1877_);
lean_inc(v_forwardedArgs_1869_);
lean_inc(v_leanOpts_1868_);
lean_dec(v_opts_942_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1899_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_leanOpts_1868_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v_forwardedArgs_1869_);
lean_ctor_set(v_reuseFailAlloc_1898_, 2, v_opts_1877_);
lean_ctor_set(v_reuseFailAlloc_1898_, 3, v_rootDir_x3f_1880_);
lean_ctor_set(v_reuseFailAlloc_1898_, 4, v_setupFileName_x3f_1881_);
lean_ctor_set(v_reuseFailAlloc_1898_, 5, v_oleanFileName_x3f_1882_);
lean_ctor_set(v_reuseFailAlloc_1898_, 6, v_ileanFileName_x3f_1883_);
lean_ctor_set(v_reuseFailAlloc_1898_, 7, v_cFileName_x3f_1884_);
lean_ctor_set(v_reuseFailAlloc_1898_, 8, v_bcFileName_x3f_1885_);
lean_ctor_set(v_reuseFailAlloc_1898_, 9, v_errorOnKinds_1887_);
lean_ctor_set(v_reuseFailAlloc_1898_, 10, v_incrSaveFileName_x3f_1889_);
lean_ctor_set(v_reuseFailAlloc_1898_, 11, v_incrLoadFileName_x3f_1890_);
lean_ctor_set(v_reuseFailAlloc_1898_, 12, v_incrHeaderSaveFileName_x3f_1891_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, sizeof(void*)*13 + 8, v_component_1870_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, sizeof(void*)*13 + 9, v_printPrefix_1871_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, sizeof(void*)*13 + 10, v_printLibDir_1872_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, sizeof(void*)*13 + 11, v_useStdin_1873_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, sizeof(void*)*13 + 12, v_onlyDeps_1874_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, sizeof(void*)*13 + 13, v_onlySrcDeps_1875_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, sizeof(void*)*13 + 14, v_depsJson_1876_);
lean_ctor_set_uint32(v_reuseFailAlloc_1898_, sizeof(void*)*13, v_trustLevel_1878_);
lean_ctor_set_uint32(v_reuseFailAlloc_1898_, sizeof(void*)*13 + 4, v_numThreads_1879_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, sizeof(void*)*13 + 15, v_jsonOutput_1886_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, sizeof(void*)*13 + 17, v_run_1888_);
v___x_1896_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1897_; 
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*13 + 16, v___x_1211_);
v___x_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
return v___x_1897_;
}
}
}
}
else
{
lean_object* v_leanOpts_1900_; lean_object* v_forwardedArgs_1901_; uint8_t v_component_1902_; uint8_t v_printPrefix_1903_; uint8_t v_printLibDir_1904_; uint8_t v_useStdin_1905_; uint8_t v_onlyDeps_1906_; uint8_t v_onlySrcDeps_1907_; uint8_t v_depsJson_1908_; lean_object* v_opts_1909_; uint32_t v_trustLevel_1910_; uint32_t v_numThreads_1911_; lean_object* v_rootDir_x3f_1912_; lean_object* v_setupFileName_x3f_1913_; lean_object* v_oleanFileName_x3f_1914_; lean_object* v_ileanFileName_x3f_1915_; lean_object* v_cFileName_x3f_1916_; lean_object* v_bcFileName_x3f_1917_; lean_object* v_errorOnKinds_1918_; uint8_t v_printStats_1919_; uint8_t v_run_1920_; lean_object* v_incrSaveFileName_x3f_1921_; lean_object* v_incrLoadFileName_x3f_1922_; lean_object* v_incrHeaderSaveFileName_x3f_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1931_; 
lean_dec(v_optArg_x3f_944_);
v_leanOpts_1900_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_1901_ = lean_ctor_get(v_opts_942_, 1);
v_component_1902_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_1903_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_1904_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_1905_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_1906_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1907_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_1908_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_1909_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_1910_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_1911_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1912_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_1913_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_1914_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_1915_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_1916_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_1917_ = lean_ctor_get(v_opts_942_, 8);
v_errorOnKinds_1918_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_1919_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_1920_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1921_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_1922_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_1923_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_1931_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1925_ = v_opts_942_;
v_isShared_1926_ = v_isSharedCheck_1931_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1923_);
lean_inc(v_incrLoadFileName_x3f_1922_);
lean_inc(v_incrSaveFileName_x3f_1921_);
lean_inc(v_errorOnKinds_1918_);
lean_inc(v_bcFileName_x3f_1917_);
lean_inc(v_cFileName_x3f_1916_);
lean_inc(v_ileanFileName_x3f_1915_);
lean_inc(v_oleanFileName_x3f_1914_);
lean_inc(v_setupFileName_x3f_1913_);
lean_inc(v_rootDir_x3f_1912_);
lean_inc(v_opts_1909_);
lean_inc(v_forwardedArgs_1901_);
lean_inc(v_leanOpts_1900_);
lean_dec(v_opts_942_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1931_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_leanOpts_1900_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_forwardedArgs_1901_);
lean_ctor_set(v_reuseFailAlloc_1930_, 2, v_opts_1909_);
lean_ctor_set(v_reuseFailAlloc_1930_, 3, v_rootDir_x3f_1912_);
lean_ctor_set(v_reuseFailAlloc_1930_, 4, v_setupFileName_x3f_1913_);
lean_ctor_set(v_reuseFailAlloc_1930_, 5, v_oleanFileName_x3f_1914_);
lean_ctor_set(v_reuseFailAlloc_1930_, 6, v_ileanFileName_x3f_1915_);
lean_ctor_set(v_reuseFailAlloc_1930_, 7, v_cFileName_x3f_1916_);
lean_ctor_set(v_reuseFailAlloc_1930_, 8, v_bcFileName_x3f_1917_);
lean_ctor_set(v_reuseFailAlloc_1930_, 9, v_errorOnKinds_1918_);
lean_ctor_set(v_reuseFailAlloc_1930_, 10, v_incrSaveFileName_x3f_1921_);
lean_ctor_set(v_reuseFailAlloc_1930_, 11, v_incrLoadFileName_x3f_1922_);
lean_ctor_set(v_reuseFailAlloc_1930_, 12, v_incrHeaderSaveFileName_x3f_1923_);
lean_ctor_set_uint8(v_reuseFailAlloc_1930_, sizeof(void*)*13 + 8, v_component_1902_);
lean_ctor_set_uint8(v_reuseFailAlloc_1930_, sizeof(void*)*13 + 9, v_printPrefix_1903_);
lean_ctor_set_uint8(v_reuseFailAlloc_1930_, sizeof(void*)*13 + 10, v_printLibDir_1904_);
lean_ctor_set_uint8(v_reuseFailAlloc_1930_, sizeof(void*)*13 + 11, v_useStdin_1905_);
lean_ctor_set_uint8(v_reuseFailAlloc_1930_, sizeof(void*)*13 + 12, v_onlyDeps_1906_);
lean_ctor_set_uint8(v_reuseFailAlloc_1930_, sizeof(void*)*13 + 13, v_onlySrcDeps_1907_);
lean_ctor_set_uint8(v_reuseFailAlloc_1930_, sizeof(void*)*13 + 14, v_depsJson_1908_);
lean_ctor_set_uint32(v_reuseFailAlloc_1930_, sizeof(void*)*13, v_trustLevel_1910_);
lean_ctor_set_uint32(v_reuseFailAlloc_1930_, sizeof(void*)*13 + 4, v_numThreads_1911_);
lean_ctor_set_uint8(v_reuseFailAlloc_1930_, sizeof(void*)*13 + 16, v_printStats_1919_);
lean_ctor_set_uint8(v_reuseFailAlloc_1930_, sizeof(void*)*13 + 17, v_run_1920_);
v___x_1928_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
lean_object* v___x_1929_; 
lean_ctor_set_uint8(v___x_1928_, sizeof(void*)*13 + 15, v___x_1209_);
v___x_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
return v___x_1929_;
}
}
}
}
else
{
lean_object* v_leanOpts_1932_; lean_object* v_forwardedArgs_1933_; uint8_t v_component_1934_; uint8_t v_printPrefix_1935_; uint8_t v_printLibDir_1936_; uint8_t v_useStdin_1937_; uint8_t v_onlySrcDeps_1938_; lean_object* v_opts_1939_; uint32_t v_trustLevel_1940_; uint32_t v_numThreads_1941_; lean_object* v_rootDir_x3f_1942_; lean_object* v_setupFileName_x3f_1943_; lean_object* v_oleanFileName_x3f_1944_; lean_object* v_ileanFileName_x3f_1945_; lean_object* v_cFileName_x3f_1946_; lean_object* v_bcFileName_x3f_1947_; uint8_t v_jsonOutput_1948_; lean_object* v_errorOnKinds_1949_; uint8_t v_printStats_1950_; uint8_t v_run_1951_; lean_object* v_incrSaveFileName_x3f_1952_; lean_object* v_incrLoadFileName_x3f_1953_; lean_object* v_incrHeaderSaveFileName_x3f_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1962_; 
lean_dec(v_optArg_x3f_944_);
v_leanOpts_1932_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_1933_ = lean_ctor_get(v_opts_942_, 1);
v_component_1934_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_1935_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_1936_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_1937_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlySrcDeps_1938_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_opts_1939_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_1940_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_1941_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1942_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_1943_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_1944_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_1945_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_1946_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_1947_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_1948_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_1949_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_1950_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_1951_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1952_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_1953_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_1954_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1956_ = v_opts_942_;
v_isShared_1957_ = v_isSharedCheck_1962_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1954_);
lean_inc(v_incrLoadFileName_x3f_1953_);
lean_inc(v_incrSaveFileName_x3f_1952_);
lean_inc(v_errorOnKinds_1949_);
lean_inc(v_bcFileName_x3f_1947_);
lean_inc(v_cFileName_x3f_1946_);
lean_inc(v_ileanFileName_x3f_1945_);
lean_inc(v_oleanFileName_x3f_1944_);
lean_inc(v_setupFileName_x3f_1943_);
lean_inc(v_rootDir_x3f_1942_);
lean_inc(v_opts_1939_);
lean_inc(v_forwardedArgs_1933_);
lean_inc(v_leanOpts_1932_);
lean_dec(v_opts_942_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1962_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_leanOpts_1932_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_forwardedArgs_1933_);
lean_ctor_set(v_reuseFailAlloc_1961_, 2, v_opts_1939_);
lean_ctor_set(v_reuseFailAlloc_1961_, 3, v_rootDir_x3f_1942_);
lean_ctor_set(v_reuseFailAlloc_1961_, 4, v_setupFileName_x3f_1943_);
lean_ctor_set(v_reuseFailAlloc_1961_, 5, v_oleanFileName_x3f_1944_);
lean_ctor_set(v_reuseFailAlloc_1961_, 6, v_ileanFileName_x3f_1945_);
lean_ctor_set(v_reuseFailAlloc_1961_, 7, v_cFileName_x3f_1946_);
lean_ctor_set(v_reuseFailAlloc_1961_, 8, v_bcFileName_x3f_1947_);
lean_ctor_set(v_reuseFailAlloc_1961_, 9, v_errorOnKinds_1949_);
lean_ctor_set(v_reuseFailAlloc_1961_, 10, v_incrSaveFileName_x3f_1952_);
lean_ctor_set(v_reuseFailAlloc_1961_, 11, v_incrLoadFileName_x3f_1953_);
lean_ctor_set(v_reuseFailAlloc_1961_, 12, v_incrHeaderSaveFileName_x3f_1954_);
lean_ctor_set_uint8(v_reuseFailAlloc_1961_, sizeof(void*)*13 + 8, v_component_1934_);
lean_ctor_set_uint8(v_reuseFailAlloc_1961_, sizeof(void*)*13 + 9, v_printPrefix_1935_);
lean_ctor_set_uint8(v_reuseFailAlloc_1961_, sizeof(void*)*13 + 10, v_printLibDir_1936_);
lean_ctor_set_uint8(v_reuseFailAlloc_1961_, sizeof(void*)*13 + 11, v_useStdin_1937_);
lean_ctor_set_uint8(v_reuseFailAlloc_1961_, sizeof(void*)*13 + 13, v_onlySrcDeps_1938_);
lean_ctor_set_uint32(v_reuseFailAlloc_1961_, sizeof(void*)*13, v_trustLevel_1940_);
lean_ctor_set_uint32(v_reuseFailAlloc_1961_, sizeof(void*)*13 + 4, v_numThreads_1941_);
lean_ctor_set_uint8(v_reuseFailAlloc_1961_, sizeof(void*)*13 + 15, v_jsonOutput_1948_);
lean_ctor_set_uint8(v_reuseFailAlloc_1961_, sizeof(void*)*13 + 16, v_printStats_1950_);
lean_ctor_set_uint8(v_reuseFailAlloc_1961_, sizeof(void*)*13 + 17, v_run_1951_);
v___x_1959_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
lean_object* v___x_1960_; 
lean_ctor_set_uint8(v___x_1959_, sizeof(void*)*13 + 12, v___x_1207_);
lean_ctor_set_uint8(v___x_1959_, sizeof(void*)*13 + 14, v___x_1207_);
v___x_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1959_);
return v___x_1960_;
}
}
}
}
else
{
lean_object* v_leanOpts_1963_; lean_object* v_forwardedArgs_1964_; uint8_t v_component_1965_; uint8_t v_printPrefix_1966_; uint8_t v_printLibDir_1967_; uint8_t v_useStdin_1968_; uint8_t v_onlyDeps_1969_; uint8_t v_depsJson_1970_; lean_object* v_opts_1971_; uint32_t v_trustLevel_1972_; uint32_t v_numThreads_1973_; lean_object* v_rootDir_x3f_1974_; lean_object* v_setupFileName_x3f_1975_; lean_object* v_oleanFileName_x3f_1976_; lean_object* v_ileanFileName_x3f_1977_; lean_object* v_cFileName_x3f_1978_; lean_object* v_bcFileName_x3f_1979_; uint8_t v_jsonOutput_1980_; lean_object* v_errorOnKinds_1981_; uint8_t v_printStats_1982_; uint8_t v_run_1983_; lean_object* v_incrSaveFileName_x3f_1984_; lean_object* v_incrLoadFileName_x3f_1985_; lean_object* v_incrHeaderSaveFileName_x3f_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1994_; 
lean_dec(v_optArg_x3f_944_);
v_leanOpts_1963_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_1964_ = lean_ctor_get(v_opts_942_, 1);
v_component_1965_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_1966_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_1967_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_1968_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_1969_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_depsJson_1970_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_1971_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_1972_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_1973_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1974_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_1975_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_1976_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_1977_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_1978_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_1979_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_1980_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_1981_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_1982_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_1983_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1984_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_1985_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_1986_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1988_ = v_opts_942_;
v_isShared_1989_ = v_isSharedCheck_1994_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1986_);
lean_inc(v_incrLoadFileName_x3f_1985_);
lean_inc(v_incrSaveFileName_x3f_1984_);
lean_inc(v_errorOnKinds_1981_);
lean_inc(v_bcFileName_x3f_1979_);
lean_inc(v_cFileName_x3f_1978_);
lean_inc(v_ileanFileName_x3f_1977_);
lean_inc(v_oleanFileName_x3f_1976_);
lean_inc(v_setupFileName_x3f_1975_);
lean_inc(v_rootDir_x3f_1974_);
lean_inc(v_opts_1971_);
lean_inc(v_forwardedArgs_1964_);
lean_inc(v_leanOpts_1963_);
lean_dec(v_opts_942_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1994_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_leanOpts_1963_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_forwardedArgs_1964_);
lean_ctor_set(v_reuseFailAlloc_1993_, 2, v_opts_1971_);
lean_ctor_set(v_reuseFailAlloc_1993_, 3, v_rootDir_x3f_1974_);
lean_ctor_set(v_reuseFailAlloc_1993_, 4, v_setupFileName_x3f_1975_);
lean_ctor_set(v_reuseFailAlloc_1993_, 5, v_oleanFileName_x3f_1976_);
lean_ctor_set(v_reuseFailAlloc_1993_, 6, v_ileanFileName_x3f_1977_);
lean_ctor_set(v_reuseFailAlloc_1993_, 7, v_cFileName_x3f_1978_);
lean_ctor_set(v_reuseFailAlloc_1993_, 8, v_bcFileName_x3f_1979_);
lean_ctor_set(v_reuseFailAlloc_1993_, 9, v_errorOnKinds_1981_);
lean_ctor_set(v_reuseFailAlloc_1993_, 10, v_incrSaveFileName_x3f_1984_);
lean_ctor_set(v_reuseFailAlloc_1993_, 11, v_incrLoadFileName_x3f_1985_);
lean_ctor_set(v_reuseFailAlloc_1993_, 12, v_incrHeaderSaveFileName_x3f_1986_);
lean_ctor_set_uint8(v_reuseFailAlloc_1993_, sizeof(void*)*13 + 8, v_component_1965_);
lean_ctor_set_uint8(v_reuseFailAlloc_1993_, sizeof(void*)*13 + 9, v_printPrefix_1966_);
lean_ctor_set_uint8(v_reuseFailAlloc_1993_, sizeof(void*)*13 + 10, v_printLibDir_1967_);
lean_ctor_set_uint8(v_reuseFailAlloc_1993_, sizeof(void*)*13 + 11, v_useStdin_1968_);
lean_ctor_set_uint8(v_reuseFailAlloc_1993_, sizeof(void*)*13 + 12, v_onlyDeps_1969_);
lean_ctor_set_uint8(v_reuseFailAlloc_1993_, sizeof(void*)*13 + 14, v_depsJson_1970_);
lean_ctor_set_uint32(v_reuseFailAlloc_1993_, sizeof(void*)*13, v_trustLevel_1972_);
lean_ctor_set_uint32(v_reuseFailAlloc_1993_, sizeof(void*)*13 + 4, v_numThreads_1973_);
lean_ctor_set_uint8(v_reuseFailAlloc_1993_, sizeof(void*)*13 + 15, v_jsonOutput_1980_);
lean_ctor_set_uint8(v_reuseFailAlloc_1993_, sizeof(void*)*13 + 16, v_printStats_1982_);
lean_ctor_set_uint8(v_reuseFailAlloc_1993_, sizeof(void*)*13 + 17, v_run_1983_);
v___x_1991_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1992_; 
lean_ctor_set_uint8(v___x_1991_, sizeof(void*)*13 + 13, v___x_1205_);
v___x_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1991_);
return v___x_1992_;
}
}
}
}
else
{
lean_object* v_leanOpts_1995_; lean_object* v_forwardedArgs_1996_; uint8_t v_component_1997_; uint8_t v_printPrefix_1998_; uint8_t v_printLibDir_1999_; uint8_t v_useStdin_2000_; uint8_t v_onlySrcDeps_2001_; uint8_t v_depsJson_2002_; lean_object* v_opts_2003_; uint32_t v_trustLevel_2004_; uint32_t v_numThreads_2005_; lean_object* v_rootDir_x3f_2006_; lean_object* v_setupFileName_x3f_2007_; lean_object* v_oleanFileName_x3f_2008_; lean_object* v_ileanFileName_x3f_2009_; lean_object* v_cFileName_x3f_2010_; lean_object* v_bcFileName_x3f_2011_; uint8_t v_jsonOutput_2012_; lean_object* v_errorOnKinds_2013_; uint8_t v_printStats_2014_; uint8_t v_run_2015_; lean_object* v_incrSaveFileName_x3f_2016_; lean_object* v_incrLoadFileName_x3f_2017_; lean_object* v_incrHeaderSaveFileName_x3f_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2026_; 
lean_dec(v_optArg_x3f_944_);
v_leanOpts_1995_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_1996_ = lean_ctor_get(v_opts_942_, 1);
v_component_1997_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_1998_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_1999_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_2000_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlySrcDeps_2001_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_2002_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_2003_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_2004_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_2005_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2006_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_2007_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_2008_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_2009_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_2010_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_2011_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_2012_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_2013_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_2014_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_2015_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2016_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_2017_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_2018_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2020_ = v_opts_942_;
v_isShared_2021_ = v_isSharedCheck_2026_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2018_);
lean_inc(v_incrLoadFileName_x3f_2017_);
lean_inc(v_incrSaveFileName_x3f_2016_);
lean_inc(v_errorOnKinds_2013_);
lean_inc(v_bcFileName_x3f_2011_);
lean_inc(v_cFileName_x3f_2010_);
lean_inc(v_ileanFileName_x3f_2009_);
lean_inc(v_oleanFileName_x3f_2008_);
lean_inc(v_setupFileName_x3f_2007_);
lean_inc(v_rootDir_x3f_2006_);
lean_inc(v_opts_2003_);
lean_inc(v_forwardedArgs_1996_);
lean_inc(v_leanOpts_1995_);
lean_dec(v_opts_942_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2026_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_leanOpts_1995_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_forwardedArgs_1996_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_opts_2003_);
lean_ctor_set(v_reuseFailAlloc_2025_, 3, v_rootDir_x3f_2006_);
lean_ctor_set(v_reuseFailAlloc_2025_, 4, v_setupFileName_x3f_2007_);
lean_ctor_set(v_reuseFailAlloc_2025_, 5, v_oleanFileName_x3f_2008_);
lean_ctor_set(v_reuseFailAlloc_2025_, 6, v_ileanFileName_x3f_2009_);
lean_ctor_set(v_reuseFailAlloc_2025_, 7, v_cFileName_x3f_2010_);
lean_ctor_set(v_reuseFailAlloc_2025_, 8, v_bcFileName_x3f_2011_);
lean_ctor_set(v_reuseFailAlloc_2025_, 9, v_errorOnKinds_2013_);
lean_ctor_set(v_reuseFailAlloc_2025_, 10, v_incrSaveFileName_x3f_2016_);
lean_ctor_set(v_reuseFailAlloc_2025_, 11, v_incrLoadFileName_x3f_2017_);
lean_ctor_set(v_reuseFailAlloc_2025_, 12, v_incrHeaderSaveFileName_x3f_2018_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*13 + 8, v_component_1997_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*13 + 9, v_printPrefix_1998_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*13 + 10, v_printLibDir_1999_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*13 + 11, v_useStdin_2000_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*13 + 13, v_onlySrcDeps_2001_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*13 + 14, v_depsJson_2002_);
lean_ctor_set_uint32(v_reuseFailAlloc_2025_, sizeof(void*)*13, v_trustLevel_2004_);
lean_ctor_set_uint32(v_reuseFailAlloc_2025_, sizeof(void*)*13 + 4, v_numThreads_2005_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*13 + 15, v_jsonOutput_2012_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*13 + 16, v_printStats_2014_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*13 + 17, v_run_2015_);
v___x_2023_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2024_; 
lean_ctor_set_uint8(v___x_2023_, sizeof(void*)*13 + 12, v___x_1203_);
v___x_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2023_);
return v___x_2024_;
}
}
}
}
else
{
lean_object* v_leanOpts_2027_; lean_object* v_forwardedArgs_2028_; uint8_t v_component_2029_; uint8_t v_printPrefix_2030_; uint8_t v_printLibDir_2031_; uint8_t v_useStdin_2032_; uint8_t v_onlyDeps_2033_; uint8_t v_onlySrcDeps_2034_; uint8_t v_depsJson_2035_; lean_object* v_opts_2036_; uint32_t v_trustLevel_2037_; uint32_t v_numThreads_2038_; lean_object* v_rootDir_x3f_2039_; lean_object* v_setupFileName_x3f_2040_; lean_object* v_oleanFileName_x3f_2041_; lean_object* v_ileanFileName_x3f_2042_; lean_object* v_cFileName_x3f_2043_; lean_object* v_bcFileName_x3f_2044_; uint8_t v_jsonOutput_2045_; lean_object* v_errorOnKinds_2046_; uint8_t v_printStats_2047_; uint8_t v_run_2048_; lean_object* v_incrSaveFileName_x3f_2049_; lean_object* v_incrLoadFileName_x3f_2050_; lean_object* v_incrHeaderSaveFileName_x3f_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2061_; 
lean_dec(v_optArg_x3f_944_);
v_leanOpts_2027_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_2028_ = lean_ctor_get(v_opts_942_, 1);
v_component_2029_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_2030_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_2031_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_2032_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_2033_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2034_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_2035_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_2036_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_2037_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_2038_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2039_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_2040_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_2041_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_2042_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_2043_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_2044_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_2045_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_2046_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_2047_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_2048_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2049_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_2050_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_2051_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_2061_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2053_ = v_opts_942_;
v_isShared_2054_ = v_isSharedCheck_2061_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2051_);
lean_inc(v_incrLoadFileName_x3f_2050_);
lean_inc(v_incrSaveFileName_x3f_2049_);
lean_inc(v_errorOnKinds_2046_);
lean_inc(v_bcFileName_x3f_2044_);
lean_inc(v_cFileName_x3f_2043_);
lean_inc(v_ileanFileName_x3f_2042_);
lean_inc(v_oleanFileName_x3f_2041_);
lean_inc(v_setupFileName_x3f_2040_);
lean_inc(v_rootDir_x3f_2039_);
lean_inc(v_opts_2036_);
lean_inc(v_forwardedArgs_2028_);
lean_inc(v_leanOpts_2027_);
lean_dec(v_opts_942_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2061_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2055_ = l___private_Lean_Shell_0__Lean_verbose;
v___x_2056_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_2027_, v___x_2055_, v___x_1199_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v___x_2056_);
v___x_2058_ = v___x_2053_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2056_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v_forwardedArgs_2028_);
lean_ctor_set(v_reuseFailAlloc_2060_, 2, v_opts_2036_);
lean_ctor_set(v_reuseFailAlloc_2060_, 3, v_rootDir_x3f_2039_);
lean_ctor_set(v_reuseFailAlloc_2060_, 4, v_setupFileName_x3f_2040_);
lean_ctor_set(v_reuseFailAlloc_2060_, 5, v_oleanFileName_x3f_2041_);
lean_ctor_set(v_reuseFailAlloc_2060_, 6, v_ileanFileName_x3f_2042_);
lean_ctor_set(v_reuseFailAlloc_2060_, 7, v_cFileName_x3f_2043_);
lean_ctor_set(v_reuseFailAlloc_2060_, 8, v_bcFileName_x3f_2044_);
lean_ctor_set(v_reuseFailAlloc_2060_, 9, v_errorOnKinds_2046_);
lean_ctor_set(v_reuseFailAlloc_2060_, 10, v_incrSaveFileName_x3f_2049_);
lean_ctor_set(v_reuseFailAlloc_2060_, 11, v_incrLoadFileName_x3f_2050_);
lean_ctor_set(v_reuseFailAlloc_2060_, 12, v_incrHeaderSaveFileName_x3f_2051_);
lean_ctor_set_uint8(v_reuseFailAlloc_2060_, sizeof(void*)*13 + 8, v_component_2029_);
lean_ctor_set_uint8(v_reuseFailAlloc_2060_, sizeof(void*)*13 + 9, v_printPrefix_2030_);
lean_ctor_set_uint8(v_reuseFailAlloc_2060_, sizeof(void*)*13 + 10, v_printLibDir_2031_);
lean_ctor_set_uint8(v_reuseFailAlloc_2060_, sizeof(void*)*13 + 11, v_useStdin_2032_);
lean_ctor_set_uint8(v_reuseFailAlloc_2060_, sizeof(void*)*13 + 12, v_onlyDeps_2033_);
lean_ctor_set_uint8(v_reuseFailAlloc_2060_, sizeof(void*)*13 + 13, v_onlySrcDeps_2034_);
lean_ctor_set_uint8(v_reuseFailAlloc_2060_, sizeof(void*)*13 + 14, v_depsJson_2035_);
lean_ctor_set_uint32(v_reuseFailAlloc_2060_, sizeof(void*)*13, v_trustLevel_2037_);
lean_ctor_set_uint32(v_reuseFailAlloc_2060_, sizeof(void*)*13 + 4, v_numThreads_2038_);
lean_ctor_set_uint8(v_reuseFailAlloc_2060_, sizeof(void*)*13 + 15, v_jsonOutput_2045_);
lean_ctor_set_uint8(v_reuseFailAlloc_2060_, sizeof(void*)*13 + 16, v_printStats_2047_);
lean_ctor_set_uint8(v_reuseFailAlloc_2060_, sizeof(void*)*13 + 17, v_run_2048_);
v___x_2058_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2059_; 
v___x_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
return v___x_2059_;
}
}
}
}
else
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2062_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13));
v___x_2063_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2062_, v_optArg_x3f_944_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2117_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2066_ = v___x_2063_;
v_isShared_2067_ = v_isSharedCheck_2117_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2063_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2117_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2068_ = lean_unsigned_to_nat(0u);
v___x_2069_ = lean_string_utf8_byte_size(v_a_2064_);
lean_inc(v_a_2064_);
v___x_2070_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2070_, 0, v_a_2064_);
lean_ctor_set(v___x_2070_, 1, v___x_2068_);
lean_ctor_set(v___x_2070_, 2, v___x_2069_);
v___x_2071_ = l_String_Slice_toNat_x3f(v___x_2070_);
lean_dec_ref_known(v___x_2070_, 3);
if (lean_obj_tag(v___x_2071_) == 1)
{
lean_object* v_val_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; 
v_val_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_val_2072_);
lean_dec_ref_known(v___x_2071_, 1);
v___x_2073_ = lean_cstr_to_nat("4294967296");
v___x_2074_ = lean_nat_dec_lt(v_val_2072_, v___x_2073_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
lean_dec(v_val_2072_);
lean_del_object(v___x_2066_);
lean_dec(v_a_2064_);
lean_dec_ref(v_opts_942_);
v___x_2075_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14));
v___x_2076_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2075_);
lean_dec_ref(v___x_2076_);
goto v___jp_1012_;
}
else
{
lean_object* v_leanOpts_2077_; lean_object* v_forwardedArgs_2078_; uint8_t v_component_2079_; uint8_t v_printPrefix_2080_; uint8_t v_printLibDir_2081_; uint8_t v_useStdin_2082_; uint8_t v_onlyDeps_2083_; uint8_t v_onlySrcDeps_2084_; uint8_t v_depsJson_2085_; lean_object* v_opts_2086_; uint32_t v_numThreads_2087_; lean_object* v_rootDir_x3f_2088_; lean_object* v_setupFileName_x3f_2089_; lean_object* v_oleanFileName_x3f_2090_; lean_object* v_ileanFileName_x3f_2091_; lean_object* v_cFileName_x3f_2092_; lean_object* v_bcFileName_x3f_2093_; uint8_t v_jsonOutput_2094_; lean_object* v_errorOnKinds_2095_; uint8_t v_printStats_2096_; uint8_t v_run_2097_; lean_object* v_incrSaveFileName_x3f_2098_; lean_object* v_incrLoadFileName_x3f_2099_; lean_object* v_incrHeaderSaveFileName_x3f_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2114_; 
v_leanOpts_2077_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_2078_ = lean_ctor_get(v_opts_942_, 1);
v_component_2079_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_2080_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_2081_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_2082_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_2083_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2084_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_2085_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_2086_ = lean_ctor_get(v_opts_942_, 2);
v_numThreads_2087_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2088_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_2089_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_2090_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_2091_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_2092_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_2093_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_2094_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_2095_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_2096_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_2097_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2098_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_2099_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_2100_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_2114_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2102_ = v_opts_942_;
v_isShared_2103_ = v_isSharedCheck_2114_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2100_);
lean_inc(v_incrLoadFileName_x3f_2099_);
lean_inc(v_incrSaveFileName_x3f_2098_);
lean_inc(v_errorOnKinds_2095_);
lean_inc(v_bcFileName_x3f_2093_);
lean_inc(v_cFileName_x3f_2092_);
lean_inc(v_ileanFileName_x3f_2091_);
lean_inc(v_oleanFileName_x3f_2090_);
lean_inc(v_setupFileName_x3f_2089_);
lean_inc(v_rootDir_x3f_2088_);
lean_inc(v_opts_2086_);
lean_inc(v_forwardedArgs_2078_);
lean_inc(v_leanOpts_2077_);
lean_dec(v_opts_942_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2114_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
uint32_t v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2109_; 
v___x_2104_ = lean_uint32_of_nat(v_val_2072_);
lean_dec(v_val_2072_);
v___x_2105_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15));
v___x_2106_ = lean_string_append(v___x_2105_, v_a_2064_);
lean_dec(v_a_2064_);
v___x_2107_ = lean_array_push(v_forwardedArgs_2078_, v___x_2106_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 1, v___x_2107_);
v___x_2109_ = v___x_2102_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_leanOpts_2077_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v___x_2107_);
lean_ctor_set(v_reuseFailAlloc_2113_, 2, v_opts_2086_);
lean_ctor_set(v_reuseFailAlloc_2113_, 3, v_rootDir_x3f_2088_);
lean_ctor_set(v_reuseFailAlloc_2113_, 4, v_setupFileName_x3f_2089_);
lean_ctor_set(v_reuseFailAlloc_2113_, 5, v_oleanFileName_x3f_2090_);
lean_ctor_set(v_reuseFailAlloc_2113_, 6, v_ileanFileName_x3f_2091_);
lean_ctor_set(v_reuseFailAlloc_2113_, 7, v_cFileName_x3f_2092_);
lean_ctor_set(v_reuseFailAlloc_2113_, 8, v_bcFileName_x3f_2093_);
lean_ctor_set(v_reuseFailAlloc_2113_, 9, v_errorOnKinds_2095_);
lean_ctor_set(v_reuseFailAlloc_2113_, 10, v_incrSaveFileName_x3f_2098_);
lean_ctor_set(v_reuseFailAlloc_2113_, 11, v_incrLoadFileName_x3f_2099_);
lean_ctor_set(v_reuseFailAlloc_2113_, 12, v_incrHeaderSaveFileName_x3f_2100_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*13 + 8, v_component_2079_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*13 + 9, v_printPrefix_2080_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*13 + 10, v_printLibDir_2081_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*13 + 11, v_useStdin_2082_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*13 + 12, v_onlyDeps_2083_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*13 + 13, v_onlySrcDeps_2084_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*13 + 14, v_depsJson_2085_);
lean_ctor_set_uint32(v_reuseFailAlloc_2113_, sizeof(void*)*13 + 4, v_numThreads_2087_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*13 + 15, v_jsonOutput_2094_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*13 + 16, v_printStats_2096_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*13 + 17, v_run_2097_);
v___x_2109_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_2111_; 
lean_ctor_set_uint32(v___x_2109_, sizeof(void*)*13, v___x_2104_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 0, v___x_2109_);
v___x_2111_ = v___x_2066_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2109_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
}
else
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
lean_dec(v___x_2071_);
lean_del_object(v___x_2066_);
lean_dec(v_a_2064_);
lean_dec_ref(v_opts_942_);
v___x_2115_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16));
v___x_2116_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2115_);
lean_dec_ref(v___x_2116_);
goto v___jp_1009_;
}
}
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
lean_dec_ref(v_opts_942_);
v_a_2118_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2118_);
lean_dec_ref_known(v___x_2063_, 1);
v___x_2122_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2123_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2122_);
lean_dec_ref(v___x_2123_);
goto v___jp_2119_;
v___jp_2119_:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = lean_io_error_to_string(v_a_2118_);
v___x_2121_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2120_);
lean_dec_ref(v___x_2121_);
goto v___jp_1006_;
}
}
}
}
else
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17));
v___x_2125_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2124_, v_optArg_x3f_944_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2177_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2128_ = v___x_2125_;
v_isShared_2129_ = v_isSharedCheck_2177_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2125_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2177_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2130_ = lean_unsigned_to_nat(0u);
v___x_2131_ = lean_string_utf8_byte_size(v_a_2126_);
lean_inc(v_a_2126_);
v___x_2132_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2132_, 0, v_a_2126_);
lean_ctor_set(v___x_2132_, 1, v___x_2130_);
lean_ctor_set(v___x_2132_, 2, v___x_2131_);
v___x_2133_ = l_String_Slice_toNat_x3f(v___x_2132_);
lean_dec_ref_known(v___x_2132_, 3);
if (lean_obj_tag(v___x_2133_) == 1)
{
lean_object* v_val_2134_; lean_object* v_leanOpts_2135_; lean_object* v_forwardedArgs_2136_; uint8_t v_component_2137_; uint8_t v_printPrefix_2138_; uint8_t v_printLibDir_2139_; uint8_t v_useStdin_2140_; uint8_t v_onlyDeps_2141_; uint8_t v_onlySrcDeps_2142_; uint8_t v_depsJson_2143_; lean_object* v_opts_2144_; uint32_t v_trustLevel_2145_; uint32_t v_numThreads_2146_; lean_object* v_rootDir_x3f_2147_; lean_object* v_setupFileName_x3f_2148_; lean_object* v_oleanFileName_x3f_2149_; lean_object* v_ileanFileName_x3f_2150_; lean_object* v_cFileName_x3f_2151_; lean_object* v_bcFileName_x3f_2152_; uint8_t v_jsonOutput_2153_; lean_object* v_errorOnKinds_2154_; uint8_t v_printStats_2155_; uint8_t v_run_2156_; lean_object* v_incrSaveFileName_x3f_2157_; lean_object* v_incrLoadFileName_x3f_2158_; lean_object* v_incrHeaderSaveFileName_x3f_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2174_; 
v_val_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_val_2134_);
lean_dec_ref_known(v___x_2133_, 1);
v_leanOpts_2135_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_2136_ = lean_ctor_get(v_opts_942_, 1);
v_component_2137_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_2138_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_2139_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_2140_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_2141_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2142_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_2143_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_2144_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_2145_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_2146_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2147_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_2148_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_2149_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_2150_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_2151_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_2152_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_2153_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_2154_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_2155_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_2156_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2157_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_2158_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_2159_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_2174_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2161_ = v_opts_942_;
v_isShared_2162_ = v_isSharedCheck_2174_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2159_);
lean_inc(v_incrLoadFileName_x3f_2158_);
lean_inc(v_incrSaveFileName_x3f_2157_);
lean_inc(v_errorOnKinds_2154_);
lean_inc(v_bcFileName_x3f_2152_);
lean_inc(v_cFileName_x3f_2151_);
lean_inc(v_ileanFileName_x3f_2150_);
lean_inc(v_oleanFileName_x3f_2149_);
lean_inc(v_setupFileName_x3f_2148_);
lean_inc(v_rootDir_x3f_2147_);
lean_inc(v_opts_2144_);
lean_inc(v_forwardedArgs_2136_);
lean_inc(v_leanOpts_2135_);
lean_dec(v_opts_942_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2174_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2169_; 
v___x_2163_ = l___private_Lean_Shell_0__Lean_timeout;
v___x_2164_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_2135_, v___x_2163_, v_val_2134_);
v___x_2165_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18));
v___x_2166_ = lean_string_append(v___x_2165_, v_a_2126_);
lean_dec(v_a_2126_);
v___x_2167_ = lean_array_push(v_forwardedArgs_2136_, v___x_2166_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 1, v___x_2167_);
lean_ctor_set(v___x_2161_, 0, v___x_2164_);
v___x_2169_ = v___x_2161_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2164_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v___x_2167_);
lean_ctor_set(v_reuseFailAlloc_2173_, 2, v_opts_2144_);
lean_ctor_set(v_reuseFailAlloc_2173_, 3, v_rootDir_x3f_2147_);
lean_ctor_set(v_reuseFailAlloc_2173_, 4, v_setupFileName_x3f_2148_);
lean_ctor_set(v_reuseFailAlloc_2173_, 5, v_oleanFileName_x3f_2149_);
lean_ctor_set(v_reuseFailAlloc_2173_, 6, v_ileanFileName_x3f_2150_);
lean_ctor_set(v_reuseFailAlloc_2173_, 7, v_cFileName_x3f_2151_);
lean_ctor_set(v_reuseFailAlloc_2173_, 8, v_bcFileName_x3f_2152_);
lean_ctor_set(v_reuseFailAlloc_2173_, 9, v_errorOnKinds_2154_);
lean_ctor_set(v_reuseFailAlloc_2173_, 10, v_incrSaveFileName_x3f_2157_);
lean_ctor_set(v_reuseFailAlloc_2173_, 11, v_incrLoadFileName_x3f_2158_);
lean_ctor_set(v_reuseFailAlloc_2173_, 12, v_incrHeaderSaveFileName_x3f_2159_);
lean_ctor_set_uint8(v_reuseFailAlloc_2173_, sizeof(void*)*13 + 8, v_component_2137_);
lean_ctor_set_uint8(v_reuseFailAlloc_2173_, sizeof(void*)*13 + 9, v_printPrefix_2138_);
lean_ctor_set_uint8(v_reuseFailAlloc_2173_, sizeof(void*)*13 + 10, v_printLibDir_2139_);
lean_ctor_set_uint8(v_reuseFailAlloc_2173_, sizeof(void*)*13 + 11, v_useStdin_2140_);
lean_ctor_set_uint8(v_reuseFailAlloc_2173_, sizeof(void*)*13 + 12, v_onlyDeps_2141_);
lean_ctor_set_uint8(v_reuseFailAlloc_2173_, sizeof(void*)*13 + 13, v_onlySrcDeps_2142_);
lean_ctor_set_uint8(v_reuseFailAlloc_2173_, sizeof(void*)*13 + 14, v_depsJson_2143_);
lean_ctor_set_uint32(v_reuseFailAlloc_2173_, sizeof(void*)*13, v_trustLevel_2145_);
lean_ctor_set_uint32(v_reuseFailAlloc_2173_, sizeof(void*)*13 + 4, v_numThreads_2146_);
lean_ctor_set_uint8(v_reuseFailAlloc_2173_, sizeof(void*)*13 + 15, v_jsonOutput_2153_);
lean_ctor_set_uint8(v_reuseFailAlloc_2173_, sizeof(void*)*13 + 16, v_printStats_2155_);
lean_ctor_set_uint8(v_reuseFailAlloc_2173_, sizeof(void*)*13 + 17, v_run_2156_);
v___x_2169_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
lean_object* v___x_2171_; 
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v___x_2169_);
v___x_2171_ = v___x_2128_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
lean_dec(v___x_2133_);
lean_del_object(v___x_2128_);
lean_dec(v_a_2126_);
lean_dec_ref(v_opts_942_);
v___x_2175_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19));
v___x_2176_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2175_);
lean_dec_ref(v___x_2176_);
goto v___jp_1119_;
}
}
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
lean_dec_ref(v_opts_942_);
v_a_2178_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2125_, 1);
v___x_2182_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2183_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2182_);
lean_dec_ref(v___x_2183_);
goto v___jp_2179_;
v___jp_2179_:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = lean_io_error_to_string(v_a_2178_);
v___x_2181_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2180_);
lean_dec_ref(v___x_2181_);
goto v___jp_1125_;
}
}
}
}
else
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2184_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20));
v___x_2185_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2184_, v_optArg_x3f_944_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2237_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2188_ = v___x_2185_;
v_isShared_2189_ = v_isSharedCheck_2237_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2185_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2237_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2190_ = lean_unsigned_to_nat(0u);
v___x_2191_ = lean_string_utf8_byte_size(v_a_2186_);
lean_inc(v_a_2186_);
v___x_2192_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2192_, 0, v_a_2186_);
lean_ctor_set(v___x_2192_, 1, v___x_2190_);
lean_ctor_set(v___x_2192_, 2, v___x_2191_);
v___x_2193_ = l_String_Slice_toNat_x3f(v___x_2192_);
lean_dec_ref_known(v___x_2192_, 3);
if (lean_obj_tag(v___x_2193_) == 1)
{
lean_object* v_val_2194_; lean_object* v_leanOpts_2195_; lean_object* v_forwardedArgs_2196_; uint8_t v_component_2197_; uint8_t v_printPrefix_2198_; uint8_t v_printLibDir_2199_; uint8_t v_useStdin_2200_; uint8_t v_onlyDeps_2201_; uint8_t v_onlySrcDeps_2202_; uint8_t v_depsJson_2203_; lean_object* v_opts_2204_; uint32_t v_trustLevel_2205_; uint32_t v_numThreads_2206_; lean_object* v_rootDir_x3f_2207_; lean_object* v_setupFileName_x3f_2208_; lean_object* v_oleanFileName_x3f_2209_; lean_object* v_ileanFileName_x3f_2210_; lean_object* v_cFileName_x3f_2211_; lean_object* v_bcFileName_x3f_2212_; uint8_t v_jsonOutput_2213_; lean_object* v_errorOnKinds_2214_; uint8_t v_printStats_2215_; uint8_t v_run_2216_; lean_object* v_incrSaveFileName_x3f_2217_; lean_object* v_incrLoadFileName_x3f_2218_; lean_object* v_incrHeaderSaveFileName_x3f_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2234_; 
v_val_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_val_2194_);
lean_dec_ref_known(v___x_2193_, 1);
v_leanOpts_2195_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_2196_ = lean_ctor_get(v_opts_942_, 1);
v_component_2197_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_2198_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_2199_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_2200_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_2201_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2202_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_2203_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_2204_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_2205_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_2206_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2207_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_2208_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_2209_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_2210_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_2211_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_2212_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_2213_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_2214_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_2215_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_2216_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2217_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_2218_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_2219_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_2234_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2221_ = v_opts_942_;
v_isShared_2222_ = v_isSharedCheck_2234_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2219_);
lean_inc(v_incrLoadFileName_x3f_2218_);
lean_inc(v_incrSaveFileName_x3f_2217_);
lean_inc(v_errorOnKinds_2214_);
lean_inc(v_bcFileName_x3f_2212_);
lean_inc(v_cFileName_x3f_2211_);
lean_inc(v_ileanFileName_x3f_2210_);
lean_inc(v_oleanFileName_x3f_2209_);
lean_inc(v_setupFileName_x3f_2208_);
lean_inc(v_rootDir_x3f_2207_);
lean_inc(v_opts_2204_);
lean_inc(v_forwardedArgs_2196_);
lean_inc(v_leanOpts_2195_);
lean_dec(v_opts_942_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2234_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2229_; 
v___x_2223_ = l___private_Lean_Shell_0__Lean_maxMemory;
v___x_2224_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_2195_, v___x_2223_, v_val_2194_);
v___x_2225_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21));
v___x_2226_ = lean_string_append(v___x_2225_, v_a_2186_);
lean_dec(v_a_2186_);
v___x_2227_ = lean_array_push(v_forwardedArgs_2196_, v___x_2226_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 1, v___x_2227_);
lean_ctor_set(v___x_2221_, 0, v___x_2224_);
v___x_2229_ = v___x_2221_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2224_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v___x_2227_);
lean_ctor_set(v_reuseFailAlloc_2233_, 2, v_opts_2204_);
lean_ctor_set(v_reuseFailAlloc_2233_, 3, v_rootDir_x3f_2207_);
lean_ctor_set(v_reuseFailAlloc_2233_, 4, v_setupFileName_x3f_2208_);
lean_ctor_set(v_reuseFailAlloc_2233_, 5, v_oleanFileName_x3f_2209_);
lean_ctor_set(v_reuseFailAlloc_2233_, 6, v_ileanFileName_x3f_2210_);
lean_ctor_set(v_reuseFailAlloc_2233_, 7, v_cFileName_x3f_2211_);
lean_ctor_set(v_reuseFailAlloc_2233_, 8, v_bcFileName_x3f_2212_);
lean_ctor_set(v_reuseFailAlloc_2233_, 9, v_errorOnKinds_2214_);
lean_ctor_set(v_reuseFailAlloc_2233_, 10, v_incrSaveFileName_x3f_2217_);
lean_ctor_set(v_reuseFailAlloc_2233_, 11, v_incrLoadFileName_x3f_2218_);
lean_ctor_set(v_reuseFailAlloc_2233_, 12, v_incrHeaderSaveFileName_x3f_2219_);
lean_ctor_set_uint8(v_reuseFailAlloc_2233_, sizeof(void*)*13 + 8, v_component_2197_);
lean_ctor_set_uint8(v_reuseFailAlloc_2233_, sizeof(void*)*13 + 9, v_printPrefix_2198_);
lean_ctor_set_uint8(v_reuseFailAlloc_2233_, sizeof(void*)*13 + 10, v_printLibDir_2199_);
lean_ctor_set_uint8(v_reuseFailAlloc_2233_, sizeof(void*)*13 + 11, v_useStdin_2200_);
lean_ctor_set_uint8(v_reuseFailAlloc_2233_, sizeof(void*)*13 + 12, v_onlyDeps_2201_);
lean_ctor_set_uint8(v_reuseFailAlloc_2233_, sizeof(void*)*13 + 13, v_onlySrcDeps_2202_);
lean_ctor_set_uint8(v_reuseFailAlloc_2233_, sizeof(void*)*13 + 14, v_depsJson_2203_);
lean_ctor_set_uint32(v_reuseFailAlloc_2233_, sizeof(void*)*13, v_trustLevel_2205_);
lean_ctor_set_uint32(v_reuseFailAlloc_2233_, sizeof(void*)*13 + 4, v_numThreads_2206_);
lean_ctor_set_uint8(v_reuseFailAlloc_2233_, sizeof(void*)*13 + 15, v_jsonOutput_2213_);
lean_ctor_set_uint8(v_reuseFailAlloc_2233_, sizeof(void*)*13 + 16, v_printStats_2215_);
lean_ctor_set_uint8(v_reuseFailAlloc_2233_, sizeof(void*)*13 + 17, v_run_2216_);
v___x_2229_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
lean_object* v___x_2231_; 
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 0, v___x_2229_);
v___x_2231_ = v___x_2188_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2229_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
else
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
lean_dec(v___x_2193_);
lean_del_object(v___x_2188_);
lean_dec(v_a_2186_);
lean_dec_ref(v_opts_942_);
v___x_2235_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22));
v___x_2236_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2235_);
lean_dec_ref(v___x_2236_);
goto v___jp_1000_;
}
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
lean_dec_ref(v_opts_942_);
v_a_2238_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2238_);
lean_dec_ref_known(v___x_2185_, 1);
v___x_2242_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2243_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2242_);
lean_dec_ref(v___x_2243_);
goto v___jp_2239_;
v___jp_2239_:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = lean_io_error_to_string(v_a_2238_);
v___x_2241_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2240_);
lean_dec_ref(v___x_2241_);
goto v___jp_997_;
}
}
}
}
else
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23));
v___x_2245_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2244_, v_optArg_x3f_944_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2289_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2248_ = v___x_2245_;
v_isShared_2249_ = v_isSharedCheck_2289_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2245_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2289_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v_leanOpts_2250_; lean_object* v_forwardedArgs_2251_; uint8_t v_component_2252_; uint8_t v_printPrefix_2253_; uint8_t v_printLibDir_2254_; uint8_t v_useStdin_2255_; uint8_t v_onlyDeps_2256_; uint8_t v_onlySrcDeps_2257_; uint8_t v_depsJson_2258_; lean_object* v_opts_2259_; uint32_t v_trustLevel_2260_; uint32_t v_numThreads_2261_; lean_object* v_setupFileName_x3f_2262_; lean_object* v_oleanFileName_x3f_2263_; lean_object* v_ileanFileName_x3f_2264_; lean_object* v_cFileName_x3f_2265_; lean_object* v_bcFileName_x3f_2266_; uint8_t v_jsonOutput_2267_; lean_object* v_errorOnKinds_2268_; uint8_t v_printStats_2269_; uint8_t v_run_2270_; lean_object* v_incrSaveFileName_x3f_2271_; lean_object* v_incrLoadFileName_x3f_2272_; lean_object* v_incrHeaderSaveFileName_x3f_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2287_; 
v_leanOpts_2250_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_2251_ = lean_ctor_get(v_opts_942_, 1);
v_component_2252_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_2253_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_2254_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_2255_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_2256_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2257_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_2258_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_2259_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_2260_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_2261_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_setupFileName_x3f_2262_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_2263_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_2264_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_2265_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_2266_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_2267_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_2268_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_2269_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_2270_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2271_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_2272_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_2273_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_2287_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_2287_ == 0)
{
lean_object* v_unused_2288_; 
v_unused_2288_ = lean_ctor_get(v_opts_942_, 3);
lean_dec(v_unused_2288_);
v___x_2275_ = v_opts_942_;
v_isShared_2276_ = v_isSharedCheck_2287_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2273_);
lean_inc(v_incrLoadFileName_x3f_2272_);
lean_inc(v_incrSaveFileName_x3f_2271_);
lean_inc(v_errorOnKinds_2268_);
lean_inc(v_bcFileName_x3f_2266_);
lean_inc(v_cFileName_x3f_2265_);
lean_inc(v_ileanFileName_x3f_2264_);
lean_inc(v_oleanFileName_x3f_2263_);
lean_inc(v_setupFileName_x3f_2262_);
lean_inc(v_opts_2259_);
lean_inc(v_forwardedArgs_2251_);
lean_inc(v_leanOpts_2250_);
lean_dec(v_opts_942_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2287_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2282_; 
v___x_2277_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24));
v___x_2278_ = lean_string_append(v___x_2277_, v_a_2246_);
v___x_2279_ = lean_array_push(v_forwardedArgs_2251_, v___x_2278_);
v___x_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2280_, 0, v_a_2246_);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 3, v___x_2280_);
lean_ctor_set(v___x_2275_, 1, v___x_2279_);
v___x_2282_ = v___x_2275_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_leanOpts_2250_);
lean_ctor_set(v_reuseFailAlloc_2286_, 1, v___x_2279_);
lean_ctor_set(v_reuseFailAlloc_2286_, 2, v_opts_2259_);
lean_ctor_set(v_reuseFailAlloc_2286_, 3, v___x_2280_);
lean_ctor_set(v_reuseFailAlloc_2286_, 4, v_setupFileName_x3f_2262_);
lean_ctor_set(v_reuseFailAlloc_2286_, 5, v_oleanFileName_x3f_2263_);
lean_ctor_set(v_reuseFailAlloc_2286_, 6, v_ileanFileName_x3f_2264_);
lean_ctor_set(v_reuseFailAlloc_2286_, 7, v_cFileName_x3f_2265_);
lean_ctor_set(v_reuseFailAlloc_2286_, 8, v_bcFileName_x3f_2266_);
lean_ctor_set(v_reuseFailAlloc_2286_, 9, v_errorOnKinds_2268_);
lean_ctor_set(v_reuseFailAlloc_2286_, 10, v_incrSaveFileName_x3f_2271_);
lean_ctor_set(v_reuseFailAlloc_2286_, 11, v_incrLoadFileName_x3f_2272_);
lean_ctor_set(v_reuseFailAlloc_2286_, 12, v_incrHeaderSaveFileName_x3f_2273_);
lean_ctor_set_uint8(v_reuseFailAlloc_2286_, sizeof(void*)*13 + 8, v_component_2252_);
lean_ctor_set_uint8(v_reuseFailAlloc_2286_, sizeof(void*)*13 + 9, v_printPrefix_2253_);
lean_ctor_set_uint8(v_reuseFailAlloc_2286_, sizeof(void*)*13 + 10, v_printLibDir_2254_);
lean_ctor_set_uint8(v_reuseFailAlloc_2286_, sizeof(void*)*13 + 11, v_useStdin_2255_);
lean_ctor_set_uint8(v_reuseFailAlloc_2286_, sizeof(void*)*13 + 12, v_onlyDeps_2256_);
lean_ctor_set_uint8(v_reuseFailAlloc_2286_, sizeof(void*)*13 + 13, v_onlySrcDeps_2257_);
lean_ctor_set_uint8(v_reuseFailAlloc_2286_, sizeof(void*)*13 + 14, v_depsJson_2258_);
lean_ctor_set_uint32(v_reuseFailAlloc_2286_, sizeof(void*)*13, v_trustLevel_2260_);
lean_ctor_set_uint32(v_reuseFailAlloc_2286_, sizeof(void*)*13 + 4, v_numThreads_2261_);
lean_ctor_set_uint8(v_reuseFailAlloc_2286_, sizeof(void*)*13 + 15, v_jsonOutput_2267_);
lean_ctor_set_uint8(v_reuseFailAlloc_2286_, sizeof(void*)*13 + 16, v_printStats_2269_);
lean_ctor_set_uint8(v_reuseFailAlloc_2286_, sizeof(void*)*13 + 17, v_run_2270_);
v___x_2282_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
lean_object* v___x_2284_; 
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 0, v___x_2282_);
v___x_2284_ = v___x_2248_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2282_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
lean_dec_ref(v_opts_942_);
v_a_2290_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_a_2290_);
lean_dec_ref_known(v___x_2245_, 1);
v___x_2294_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2295_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2294_);
lean_dec_ref(v___x_2295_);
goto v___jp_2291_;
v___jp_2291_:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = lean_io_error_to_string(v_a_2290_);
v___x_2293_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2292_);
lean_dec_ref(v___x_2293_);
goto v___jp_1131_;
}
}
}
}
else
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2296_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25));
v___x_2297_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2296_, v_optArg_x3f_944_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2338_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2300_ = v___x_2297_;
v_isShared_2301_ = v_isSharedCheck_2338_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2297_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2338_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v_leanOpts_2302_; lean_object* v_forwardedArgs_2303_; uint8_t v_component_2304_; uint8_t v_printPrefix_2305_; uint8_t v_printLibDir_2306_; uint8_t v_useStdin_2307_; uint8_t v_onlyDeps_2308_; uint8_t v_onlySrcDeps_2309_; uint8_t v_depsJson_2310_; lean_object* v_opts_2311_; uint32_t v_trustLevel_2312_; uint32_t v_numThreads_2313_; lean_object* v_rootDir_x3f_2314_; lean_object* v_setupFileName_x3f_2315_; lean_object* v_oleanFileName_x3f_2316_; lean_object* v_cFileName_x3f_2317_; lean_object* v_bcFileName_x3f_2318_; uint8_t v_jsonOutput_2319_; lean_object* v_errorOnKinds_2320_; uint8_t v_printStats_2321_; uint8_t v_run_2322_; lean_object* v_incrSaveFileName_x3f_2323_; lean_object* v_incrLoadFileName_x3f_2324_; lean_object* v_incrHeaderSaveFileName_x3f_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2336_; 
v_leanOpts_2302_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_2303_ = lean_ctor_get(v_opts_942_, 1);
v_component_2304_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_2305_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_2306_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_2307_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_2308_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2309_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_2310_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_2311_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_2312_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_2313_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2314_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_2315_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_2316_ = lean_ctor_get(v_opts_942_, 5);
v_cFileName_x3f_2317_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_2318_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_2319_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_2320_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_2321_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_2322_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2323_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_2324_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_2325_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_2336_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_2336_ == 0)
{
lean_object* v_unused_2337_; 
v_unused_2337_ = lean_ctor_get(v_opts_942_, 6);
lean_dec(v_unused_2337_);
v___x_2327_ = v_opts_942_;
v_isShared_2328_ = v_isSharedCheck_2336_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2325_);
lean_inc(v_incrLoadFileName_x3f_2324_);
lean_inc(v_incrSaveFileName_x3f_2323_);
lean_inc(v_errorOnKinds_2320_);
lean_inc(v_bcFileName_x3f_2318_);
lean_inc(v_cFileName_x3f_2317_);
lean_inc(v_oleanFileName_x3f_2316_);
lean_inc(v_setupFileName_x3f_2315_);
lean_inc(v_rootDir_x3f_2314_);
lean_inc(v_opts_2311_);
lean_inc(v_forwardedArgs_2303_);
lean_inc(v_leanOpts_2302_);
lean_dec(v_opts_942_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2336_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2329_, 0, v_a_2298_);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 6, v___x_2329_);
v___x_2331_ = v___x_2327_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_leanOpts_2302_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_forwardedArgs_2303_);
lean_ctor_set(v_reuseFailAlloc_2335_, 2, v_opts_2311_);
lean_ctor_set(v_reuseFailAlloc_2335_, 3, v_rootDir_x3f_2314_);
lean_ctor_set(v_reuseFailAlloc_2335_, 4, v_setupFileName_x3f_2315_);
lean_ctor_set(v_reuseFailAlloc_2335_, 5, v_oleanFileName_x3f_2316_);
lean_ctor_set(v_reuseFailAlloc_2335_, 6, v___x_2329_);
lean_ctor_set(v_reuseFailAlloc_2335_, 7, v_cFileName_x3f_2317_);
lean_ctor_set(v_reuseFailAlloc_2335_, 8, v_bcFileName_x3f_2318_);
lean_ctor_set(v_reuseFailAlloc_2335_, 9, v_errorOnKinds_2320_);
lean_ctor_set(v_reuseFailAlloc_2335_, 10, v_incrSaveFileName_x3f_2323_);
lean_ctor_set(v_reuseFailAlloc_2335_, 11, v_incrLoadFileName_x3f_2324_);
lean_ctor_set(v_reuseFailAlloc_2335_, 12, v_incrHeaderSaveFileName_x3f_2325_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, sizeof(void*)*13 + 8, v_component_2304_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, sizeof(void*)*13 + 9, v_printPrefix_2305_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, sizeof(void*)*13 + 10, v_printLibDir_2306_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, sizeof(void*)*13 + 11, v_useStdin_2307_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, sizeof(void*)*13 + 12, v_onlyDeps_2308_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, sizeof(void*)*13 + 13, v_onlySrcDeps_2309_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, sizeof(void*)*13 + 14, v_depsJson_2310_);
lean_ctor_set_uint32(v_reuseFailAlloc_2335_, sizeof(void*)*13, v_trustLevel_2312_);
lean_ctor_set_uint32(v_reuseFailAlloc_2335_, sizeof(void*)*13 + 4, v_numThreads_2313_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, sizeof(void*)*13 + 15, v_jsonOutput_2319_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, sizeof(void*)*13 + 16, v_printStats_2321_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, sizeof(void*)*13 + 17, v_run_2322_);
v___x_2331_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2333_; 
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 0, v___x_2331_);
v___x_2333_ = v___x_2300_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
lean_dec_ref(v_opts_942_);
v_a_2339_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2297_, 1);
v___x_2343_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2344_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2343_);
lean_dec_ref(v___x_2344_);
goto v___jp_2340_;
v___jp_2340_:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2341_ = lean_io_error_to_string(v_a_2339_);
v___x_2342_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2341_);
lean_dec_ref(v___x_2342_);
goto v___jp_991_;
}
}
}
}
else
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26));
v___x_2346_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2345_, v_optArg_x3f_944_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2387_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2349_ = v___x_2346_;
v_isShared_2350_ = v_isSharedCheck_2387_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2346_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2387_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v_leanOpts_2351_; lean_object* v_forwardedArgs_2352_; uint8_t v_component_2353_; uint8_t v_printPrefix_2354_; uint8_t v_printLibDir_2355_; uint8_t v_useStdin_2356_; uint8_t v_onlyDeps_2357_; uint8_t v_onlySrcDeps_2358_; uint8_t v_depsJson_2359_; lean_object* v_opts_2360_; uint32_t v_trustLevel_2361_; uint32_t v_numThreads_2362_; lean_object* v_rootDir_x3f_2363_; lean_object* v_setupFileName_x3f_2364_; lean_object* v_ileanFileName_x3f_2365_; lean_object* v_cFileName_x3f_2366_; lean_object* v_bcFileName_x3f_2367_; uint8_t v_jsonOutput_2368_; lean_object* v_errorOnKinds_2369_; uint8_t v_printStats_2370_; uint8_t v_run_2371_; lean_object* v_incrSaveFileName_x3f_2372_; lean_object* v_incrLoadFileName_x3f_2373_; lean_object* v_incrHeaderSaveFileName_x3f_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2385_; 
v_leanOpts_2351_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_2352_ = lean_ctor_get(v_opts_942_, 1);
v_component_2353_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_2354_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_2355_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_2356_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_2357_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2358_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_2359_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_2360_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_2361_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_2362_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2363_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_2364_ = lean_ctor_get(v_opts_942_, 4);
v_ileanFileName_x3f_2365_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_2366_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_2367_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_2368_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_2369_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_2370_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_2371_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2372_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_2373_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_2374_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_2385_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_2385_ == 0)
{
lean_object* v_unused_2386_; 
v_unused_2386_ = lean_ctor_get(v_opts_942_, 5);
lean_dec(v_unused_2386_);
v___x_2376_ = v_opts_942_;
v_isShared_2377_ = v_isSharedCheck_2385_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2374_);
lean_inc(v_incrLoadFileName_x3f_2373_);
lean_inc(v_incrSaveFileName_x3f_2372_);
lean_inc(v_errorOnKinds_2369_);
lean_inc(v_bcFileName_x3f_2367_);
lean_inc(v_cFileName_x3f_2366_);
lean_inc(v_ileanFileName_x3f_2365_);
lean_inc(v_setupFileName_x3f_2364_);
lean_inc(v_rootDir_x3f_2363_);
lean_inc(v_opts_2360_);
lean_inc(v_forwardedArgs_2352_);
lean_inc(v_leanOpts_2351_);
lean_dec(v_opts_942_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2385_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2378_; lean_object* v___x_2380_; 
v___x_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2378_, 0, v_a_2347_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 5, v___x_2378_);
v___x_2380_ = v___x_2376_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_leanOpts_2351_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v_forwardedArgs_2352_);
lean_ctor_set(v_reuseFailAlloc_2384_, 2, v_opts_2360_);
lean_ctor_set(v_reuseFailAlloc_2384_, 3, v_rootDir_x3f_2363_);
lean_ctor_set(v_reuseFailAlloc_2384_, 4, v_setupFileName_x3f_2364_);
lean_ctor_set(v_reuseFailAlloc_2384_, 5, v___x_2378_);
lean_ctor_set(v_reuseFailAlloc_2384_, 6, v_ileanFileName_x3f_2365_);
lean_ctor_set(v_reuseFailAlloc_2384_, 7, v_cFileName_x3f_2366_);
lean_ctor_set(v_reuseFailAlloc_2384_, 8, v_bcFileName_x3f_2367_);
lean_ctor_set(v_reuseFailAlloc_2384_, 9, v_errorOnKinds_2369_);
lean_ctor_set(v_reuseFailAlloc_2384_, 10, v_incrSaveFileName_x3f_2372_);
lean_ctor_set(v_reuseFailAlloc_2384_, 11, v_incrLoadFileName_x3f_2373_);
lean_ctor_set(v_reuseFailAlloc_2384_, 12, v_incrHeaderSaveFileName_x3f_2374_);
lean_ctor_set_uint8(v_reuseFailAlloc_2384_, sizeof(void*)*13 + 8, v_component_2353_);
lean_ctor_set_uint8(v_reuseFailAlloc_2384_, sizeof(void*)*13 + 9, v_printPrefix_2354_);
lean_ctor_set_uint8(v_reuseFailAlloc_2384_, sizeof(void*)*13 + 10, v_printLibDir_2355_);
lean_ctor_set_uint8(v_reuseFailAlloc_2384_, sizeof(void*)*13 + 11, v_useStdin_2356_);
lean_ctor_set_uint8(v_reuseFailAlloc_2384_, sizeof(void*)*13 + 12, v_onlyDeps_2357_);
lean_ctor_set_uint8(v_reuseFailAlloc_2384_, sizeof(void*)*13 + 13, v_onlySrcDeps_2358_);
lean_ctor_set_uint8(v_reuseFailAlloc_2384_, sizeof(void*)*13 + 14, v_depsJson_2359_);
lean_ctor_set_uint32(v_reuseFailAlloc_2384_, sizeof(void*)*13, v_trustLevel_2361_);
lean_ctor_set_uint32(v_reuseFailAlloc_2384_, sizeof(void*)*13 + 4, v_numThreads_2362_);
lean_ctor_set_uint8(v_reuseFailAlloc_2384_, sizeof(void*)*13 + 15, v_jsonOutput_2368_);
lean_ctor_set_uint8(v_reuseFailAlloc_2384_, sizeof(void*)*13 + 16, v_printStats_2370_);
lean_ctor_set_uint8(v_reuseFailAlloc_2384_, sizeof(void*)*13 + 17, v_run_2371_);
v___x_2380_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
lean_object* v___x_2382_; 
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 0, v___x_2380_);
v___x_2382_ = v___x_2349_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v___x_2380_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
lean_dec_ref(v_opts_942_);
v_a_2388_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2346_, 1);
v___x_2392_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2393_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2392_);
lean_dec_ref(v___x_2393_);
goto v___jp_2389_;
v___jp_2389_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = lean_io_error_to_string(v_a_2388_);
v___x_2391_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2390_);
lean_dec_ref(v___x_2391_);
goto v___jp_1137_;
}
}
}
}
else
{
lean_object* v_leanOpts_2394_; lean_object* v_forwardedArgs_2395_; uint8_t v_component_2396_; uint8_t v_printPrefix_2397_; uint8_t v_printLibDir_2398_; uint8_t v_useStdin_2399_; uint8_t v_onlyDeps_2400_; uint8_t v_onlySrcDeps_2401_; uint8_t v_depsJson_2402_; lean_object* v_opts_2403_; uint32_t v_trustLevel_2404_; uint32_t v_numThreads_2405_; lean_object* v_rootDir_x3f_2406_; lean_object* v_setupFileName_x3f_2407_; lean_object* v_oleanFileName_x3f_2408_; lean_object* v_ileanFileName_x3f_2409_; lean_object* v_cFileName_x3f_2410_; lean_object* v_bcFileName_x3f_2411_; uint8_t v_jsonOutput_2412_; lean_object* v_errorOnKinds_2413_; uint8_t v_printStats_2414_; lean_object* v_incrSaveFileName_x3f_2415_; lean_object* v_incrLoadFileName_x3f_2416_; lean_object* v_incrHeaderSaveFileName_x3f_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2427_; 
lean_dec(v_optArg_x3f_944_);
v_leanOpts_2394_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_2395_ = lean_ctor_get(v_opts_942_, 1);
v_component_2396_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_2397_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_2398_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_2399_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_2400_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2401_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_2402_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_2403_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_2404_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_2405_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2406_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_2407_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_2408_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_2409_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_2410_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_2411_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_2412_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_2413_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_2414_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_incrSaveFileName_x3f_2415_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_2416_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_2417_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_2427_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2419_ = v_opts_942_;
v_isShared_2420_ = v_isSharedCheck_2427_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2417_);
lean_inc(v_incrLoadFileName_x3f_2416_);
lean_inc(v_incrSaveFileName_x3f_2415_);
lean_inc(v_errorOnKinds_2413_);
lean_inc(v_bcFileName_x3f_2411_);
lean_inc(v_cFileName_x3f_2410_);
lean_inc(v_ileanFileName_x3f_2409_);
lean_inc(v_oleanFileName_x3f_2408_);
lean_inc(v_setupFileName_x3f_2407_);
lean_inc(v_rootDir_x3f_2406_);
lean_inc(v_opts_2403_);
lean_inc(v_forwardedArgs_2395_);
lean_inc(v_leanOpts_2394_);
lean_dec(v_opts_942_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2427_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2424_; 
v___x_2421_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_2422_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_2394_, v___x_2421_, v___x_1185_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v___x_2422_);
v___x_2424_ = v___x_2419_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2422_);
lean_ctor_set(v_reuseFailAlloc_2426_, 1, v_forwardedArgs_2395_);
lean_ctor_set(v_reuseFailAlloc_2426_, 2, v_opts_2403_);
lean_ctor_set(v_reuseFailAlloc_2426_, 3, v_rootDir_x3f_2406_);
lean_ctor_set(v_reuseFailAlloc_2426_, 4, v_setupFileName_x3f_2407_);
lean_ctor_set(v_reuseFailAlloc_2426_, 5, v_oleanFileName_x3f_2408_);
lean_ctor_set(v_reuseFailAlloc_2426_, 6, v_ileanFileName_x3f_2409_);
lean_ctor_set(v_reuseFailAlloc_2426_, 7, v_cFileName_x3f_2410_);
lean_ctor_set(v_reuseFailAlloc_2426_, 8, v_bcFileName_x3f_2411_);
lean_ctor_set(v_reuseFailAlloc_2426_, 9, v_errorOnKinds_2413_);
lean_ctor_set(v_reuseFailAlloc_2426_, 10, v_incrSaveFileName_x3f_2415_);
lean_ctor_set(v_reuseFailAlloc_2426_, 11, v_incrLoadFileName_x3f_2416_);
lean_ctor_set(v_reuseFailAlloc_2426_, 12, v_incrHeaderSaveFileName_x3f_2417_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, sizeof(void*)*13 + 8, v_component_2396_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, sizeof(void*)*13 + 9, v_printPrefix_2397_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, sizeof(void*)*13 + 10, v_printLibDir_2398_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, sizeof(void*)*13 + 11, v_useStdin_2399_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, sizeof(void*)*13 + 12, v_onlyDeps_2400_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, sizeof(void*)*13 + 13, v_onlySrcDeps_2401_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, sizeof(void*)*13 + 14, v_depsJson_2402_);
lean_ctor_set_uint32(v_reuseFailAlloc_2426_, sizeof(void*)*13, v_trustLevel_2404_);
lean_ctor_set_uint32(v_reuseFailAlloc_2426_, sizeof(void*)*13 + 4, v_numThreads_2405_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, sizeof(void*)*13 + 15, v_jsonOutput_2412_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, sizeof(void*)*13 + 16, v_printStats_2414_);
v___x_2424_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2425_; 
lean_ctor_set_uint8(v___x_2424_, sizeof(void*)*13 + 17, v___x_1187_);
v___x_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
return v___x_2425_;
}
}
}
}
else
{
lean_object* v_leanOpts_2428_; lean_object* v_forwardedArgs_2429_; uint8_t v_component_2430_; uint8_t v_printPrefix_2431_; uint8_t v_printLibDir_2432_; uint8_t v_onlyDeps_2433_; uint8_t v_onlySrcDeps_2434_; uint8_t v_depsJson_2435_; lean_object* v_opts_2436_; uint32_t v_trustLevel_2437_; uint32_t v_numThreads_2438_; lean_object* v_rootDir_x3f_2439_; lean_object* v_setupFileName_x3f_2440_; lean_object* v_oleanFileName_x3f_2441_; lean_object* v_ileanFileName_x3f_2442_; lean_object* v_cFileName_x3f_2443_; lean_object* v_bcFileName_x3f_2444_; uint8_t v_jsonOutput_2445_; lean_object* v_errorOnKinds_2446_; uint8_t v_printStats_2447_; uint8_t v_run_2448_; lean_object* v_incrSaveFileName_x3f_2449_; lean_object* v_incrLoadFileName_x3f_2450_; lean_object* v_incrHeaderSaveFileName_x3f_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2459_; 
lean_dec(v_optArg_x3f_944_);
v_leanOpts_2428_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_2429_ = lean_ctor_get(v_opts_942_, 1);
v_component_2430_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_2431_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_2432_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_onlyDeps_2433_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2434_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_2435_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_2436_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_2437_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_2438_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2439_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_2440_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_2441_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_2442_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_2443_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_2444_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_2445_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_2446_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_2447_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_2448_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2449_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_2450_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_2451_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_2459_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2453_ = v_opts_942_;
v_isShared_2454_ = v_isSharedCheck_2459_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2451_);
lean_inc(v_incrLoadFileName_x3f_2450_);
lean_inc(v_incrSaveFileName_x3f_2449_);
lean_inc(v_errorOnKinds_2446_);
lean_inc(v_bcFileName_x3f_2444_);
lean_inc(v_cFileName_x3f_2443_);
lean_inc(v_ileanFileName_x3f_2442_);
lean_inc(v_oleanFileName_x3f_2441_);
lean_inc(v_setupFileName_x3f_2440_);
lean_inc(v_rootDir_x3f_2439_);
lean_inc(v_opts_2436_);
lean_inc(v_forwardedArgs_2429_);
lean_inc(v_leanOpts_2428_);
lean_dec(v_opts_942_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2459_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_leanOpts_2428_);
lean_ctor_set(v_reuseFailAlloc_2458_, 1, v_forwardedArgs_2429_);
lean_ctor_set(v_reuseFailAlloc_2458_, 2, v_opts_2436_);
lean_ctor_set(v_reuseFailAlloc_2458_, 3, v_rootDir_x3f_2439_);
lean_ctor_set(v_reuseFailAlloc_2458_, 4, v_setupFileName_x3f_2440_);
lean_ctor_set(v_reuseFailAlloc_2458_, 5, v_oleanFileName_x3f_2441_);
lean_ctor_set(v_reuseFailAlloc_2458_, 6, v_ileanFileName_x3f_2442_);
lean_ctor_set(v_reuseFailAlloc_2458_, 7, v_cFileName_x3f_2443_);
lean_ctor_set(v_reuseFailAlloc_2458_, 8, v_bcFileName_x3f_2444_);
lean_ctor_set(v_reuseFailAlloc_2458_, 9, v_errorOnKinds_2446_);
lean_ctor_set(v_reuseFailAlloc_2458_, 10, v_incrSaveFileName_x3f_2449_);
lean_ctor_set(v_reuseFailAlloc_2458_, 11, v_incrLoadFileName_x3f_2450_);
lean_ctor_set(v_reuseFailAlloc_2458_, 12, v_incrHeaderSaveFileName_x3f_2451_);
lean_ctor_set_uint8(v_reuseFailAlloc_2458_, sizeof(void*)*13 + 8, v_component_2430_);
lean_ctor_set_uint8(v_reuseFailAlloc_2458_, sizeof(void*)*13 + 9, v_printPrefix_2431_);
lean_ctor_set_uint8(v_reuseFailAlloc_2458_, sizeof(void*)*13 + 10, v_printLibDir_2432_);
lean_ctor_set_uint8(v_reuseFailAlloc_2458_, sizeof(void*)*13 + 12, v_onlyDeps_2433_);
lean_ctor_set_uint8(v_reuseFailAlloc_2458_, sizeof(void*)*13 + 13, v_onlySrcDeps_2434_);
lean_ctor_set_uint8(v_reuseFailAlloc_2458_, sizeof(void*)*13 + 14, v_depsJson_2435_);
lean_ctor_set_uint32(v_reuseFailAlloc_2458_, sizeof(void*)*13, v_trustLevel_2437_);
lean_ctor_set_uint32(v_reuseFailAlloc_2458_, sizeof(void*)*13 + 4, v_numThreads_2438_);
lean_ctor_set_uint8(v_reuseFailAlloc_2458_, sizeof(void*)*13 + 15, v_jsonOutput_2445_);
lean_ctor_set_uint8(v_reuseFailAlloc_2458_, sizeof(void*)*13 + 16, v_printStats_2447_);
lean_ctor_set_uint8(v_reuseFailAlloc_2458_, sizeof(void*)*13 + 17, v_run_2448_);
v___x_2456_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
lean_object* v___x_2457_; 
lean_ctor_set_uint8(v___x_2456_, sizeof(void*)*13 + 11, v___x_1185_);
v___x_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2456_);
return v___x_2457_;
}
}
}
}
else
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27));
v___x_2461_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2460_, v_optArg_x3f_944_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2523_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2464_ = v___x_2461_;
v_isShared_2465_ = v_isSharedCheck_2523_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2523_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2466_ = lean_unsigned_to_nat(0u);
v___x_2467_ = lean_string_utf8_byte_size(v_a_2462_);
lean_inc(v_a_2462_);
v___x_2468_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2468_, 0, v_a_2462_);
lean_ctor_set(v___x_2468_, 1, v___x_2466_);
lean_ctor_set(v___x_2468_, 2, v___x_2467_);
v___x_2469_ = l_String_Slice_toNat_x3f(v___x_2468_);
lean_dec_ref_known(v___x_2468_, 3);
if (lean_obj_tag(v___x_2469_) == 1)
{
lean_object* v_val_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; uint8_t v___x_2478_; 
v_val_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_val_2470_);
lean_dec_ref_known(v___x_2469_, 1);
v___x_2471_ = lean_unsigned_to_nat(4u);
v___x_2472_ = lean_unsigned_to_nat(2u);
v___x_2473_ = lean_nat_shiftr(v_val_2470_, v___x_2472_);
lean_dec(v_val_2470_);
v___x_2474_ = lean_nat_mul(v___x_2473_, v___x_2471_);
lean_dec(v___x_2473_);
v___x_2475_ = lean_unsigned_to_nat(1024u);
v___x_2476_ = lean_nat_mul(v___x_2474_, v___x_2475_);
lean_dec(v___x_2474_);
v___x_2477_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28, &l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28_once, _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28);
v___x_2478_ = lean_nat_dec_lt(v___x_2476_, v___x_2477_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
lean_dec(v___x_2476_);
lean_del_object(v___x_2464_);
lean_dec(v_a_2462_);
lean_dec_ref(v_opts_942_);
v___x_2479_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29));
v___x_2480_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2479_);
lean_dec_ref(v___x_2480_);
goto v___jp_985_;
}
else
{
size_t v___x_2481_; lean_object* v___x_2482_; lean_object* v_leanOpts_2483_; lean_object* v_forwardedArgs_2484_; uint8_t v_component_2485_; uint8_t v_printPrefix_2486_; uint8_t v_printLibDir_2487_; uint8_t v_useStdin_2488_; uint8_t v_onlyDeps_2489_; uint8_t v_onlySrcDeps_2490_; uint8_t v_depsJson_2491_; lean_object* v_opts_2492_; uint32_t v_trustLevel_2493_; uint32_t v_numThreads_2494_; lean_object* v_rootDir_x3f_2495_; lean_object* v_setupFileName_x3f_2496_; lean_object* v_oleanFileName_x3f_2497_; lean_object* v_ileanFileName_x3f_2498_; lean_object* v_cFileName_x3f_2499_; lean_object* v_bcFileName_x3f_2500_; uint8_t v_jsonOutput_2501_; lean_object* v_errorOnKinds_2502_; uint8_t v_printStats_2503_; uint8_t v_run_2504_; lean_object* v_incrSaveFileName_x3f_2505_; lean_object* v_incrLoadFileName_x3f_2506_; lean_object* v_incrHeaderSaveFileName_x3f_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2520_; 
v___x_2481_ = lean_usize_of_nat(v___x_2476_);
lean_dec(v___x_2476_);
v___x_2482_ = lean_internal_set_thread_stack_size(v___x_2481_);
v_leanOpts_2483_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_2484_ = lean_ctor_get(v_opts_942_, 1);
v_component_2485_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_2486_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_2487_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_2488_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_2489_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2490_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_2491_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_2492_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_2493_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_2494_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2495_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_2496_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_2497_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_2498_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_2499_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_2500_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_2501_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_2502_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_2503_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_2504_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2505_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_2506_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_2507_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_2520_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2509_ = v_opts_942_;
v_isShared_2510_ = v_isSharedCheck_2520_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2507_);
lean_inc(v_incrLoadFileName_x3f_2506_);
lean_inc(v_incrSaveFileName_x3f_2505_);
lean_inc(v_errorOnKinds_2502_);
lean_inc(v_bcFileName_x3f_2500_);
lean_inc(v_cFileName_x3f_2499_);
lean_inc(v_ileanFileName_x3f_2498_);
lean_inc(v_oleanFileName_x3f_2497_);
lean_inc(v_setupFileName_x3f_2496_);
lean_inc(v_rootDir_x3f_2495_);
lean_inc(v_opts_2492_);
lean_inc(v_forwardedArgs_2484_);
lean_inc(v_leanOpts_2483_);
lean_dec(v_opts_942_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2520_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2515_; 
v___x_2511_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30));
v___x_2512_ = lean_string_append(v___x_2511_, v_a_2462_);
lean_dec(v_a_2462_);
v___x_2513_ = lean_array_push(v_forwardedArgs_2484_, v___x_2512_);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 1, v___x_2513_);
v___x_2515_ = v___x_2509_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_leanOpts_2483_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v___x_2513_);
lean_ctor_set(v_reuseFailAlloc_2519_, 2, v_opts_2492_);
lean_ctor_set(v_reuseFailAlloc_2519_, 3, v_rootDir_x3f_2495_);
lean_ctor_set(v_reuseFailAlloc_2519_, 4, v_setupFileName_x3f_2496_);
lean_ctor_set(v_reuseFailAlloc_2519_, 5, v_oleanFileName_x3f_2497_);
lean_ctor_set(v_reuseFailAlloc_2519_, 6, v_ileanFileName_x3f_2498_);
lean_ctor_set(v_reuseFailAlloc_2519_, 7, v_cFileName_x3f_2499_);
lean_ctor_set(v_reuseFailAlloc_2519_, 8, v_bcFileName_x3f_2500_);
lean_ctor_set(v_reuseFailAlloc_2519_, 9, v_errorOnKinds_2502_);
lean_ctor_set(v_reuseFailAlloc_2519_, 10, v_incrSaveFileName_x3f_2505_);
lean_ctor_set(v_reuseFailAlloc_2519_, 11, v_incrLoadFileName_x3f_2506_);
lean_ctor_set(v_reuseFailAlloc_2519_, 12, v_incrHeaderSaveFileName_x3f_2507_);
lean_ctor_set_uint8(v_reuseFailAlloc_2519_, sizeof(void*)*13 + 8, v_component_2485_);
lean_ctor_set_uint8(v_reuseFailAlloc_2519_, sizeof(void*)*13 + 9, v_printPrefix_2486_);
lean_ctor_set_uint8(v_reuseFailAlloc_2519_, sizeof(void*)*13 + 10, v_printLibDir_2487_);
lean_ctor_set_uint8(v_reuseFailAlloc_2519_, sizeof(void*)*13 + 11, v_useStdin_2488_);
lean_ctor_set_uint8(v_reuseFailAlloc_2519_, sizeof(void*)*13 + 12, v_onlyDeps_2489_);
lean_ctor_set_uint8(v_reuseFailAlloc_2519_, sizeof(void*)*13 + 13, v_onlySrcDeps_2490_);
lean_ctor_set_uint8(v_reuseFailAlloc_2519_, sizeof(void*)*13 + 14, v_depsJson_2491_);
lean_ctor_set_uint32(v_reuseFailAlloc_2519_, sizeof(void*)*13, v_trustLevel_2493_);
lean_ctor_set_uint32(v_reuseFailAlloc_2519_, sizeof(void*)*13 + 4, v_numThreads_2494_);
lean_ctor_set_uint8(v_reuseFailAlloc_2519_, sizeof(void*)*13 + 15, v_jsonOutput_2501_);
lean_ctor_set_uint8(v_reuseFailAlloc_2519_, sizeof(void*)*13 + 16, v_printStats_2503_);
lean_ctor_set_uint8(v_reuseFailAlloc_2519_, sizeof(void*)*13 + 17, v_run_2504_);
v___x_2515_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
lean_object* v___x_2517_; 
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v___x_2515_);
v___x_2517_ = v___x_2464_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2515_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
}
else
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
lean_dec(v___x_2469_);
lean_del_object(v___x_2464_);
lean_dec(v_a_2462_);
lean_dec_ref(v_opts_942_);
v___x_2521_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31));
v___x_2522_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2521_);
lean_dec_ref(v___x_2522_);
goto v___jp_982_;
}
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
lean_dec_ref(v_opts_942_);
v_a_2524_ = lean_ctor_get(v___x_2461_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v___x_2461_, 1);
v___x_2528_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2529_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2528_);
lean_dec_ref(v___x_2529_);
goto v___jp_2525_;
v___jp_2525_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = lean_io_error_to_string(v_a_2524_);
v___x_2527_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2526_);
lean_dec_ref(v___x_2527_);
goto v___jp_979_;
}
}
}
}
else
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32));
v___x_2531_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2530_, v_optArg_x3f_944_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2572_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2534_ = v___x_2531_;
v_isShared_2535_ = v_isSharedCheck_2572_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2572_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v_leanOpts_2536_; lean_object* v_forwardedArgs_2537_; uint8_t v_component_2538_; uint8_t v_printPrefix_2539_; uint8_t v_printLibDir_2540_; uint8_t v_useStdin_2541_; uint8_t v_onlyDeps_2542_; uint8_t v_onlySrcDeps_2543_; uint8_t v_depsJson_2544_; lean_object* v_opts_2545_; uint32_t v_trustLevel_2546_; uint32_t v_numThreads_2547_; lean_object* v_rootDir_x3f_2548_; lean_object* v_setupFileName_x3f_2549_; lean_object* v_oleanFileName_x3f_2550_; lean_object* v_ileanFileName_x3f_2551_; lean_object* v_cFileName_x3f_2552_; uint8_t v_jsonOutput_2553_; lean_object* v_errorOnKinds_2554_; uint8_t v_printStats_2555_; uint8_t v_run_2556_; lean_object* v_incrSaveFileName_x3f_2557_; lean_object* v_incrLoadFileName_x3f_2558_; lean_object* v_incrHeaderSaveFileName_x3f_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2570_; 
v_leanOpts_2536_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_2537_ = lean_ctor_get(v_opts_942_, 1);
v_component_2538_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_2539_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_2540_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_2541_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_2542_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2543_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_2544_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_2545_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_2546_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_2547_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2548_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_2549_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_2550_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_2551_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_2552_ = lean_ctor_get(v_opts_942_, 7);
v_jsonOutput_2553_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_2554_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_2555_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_2556_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2557_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_2558_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_2559_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_2570_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_2570_ == 0)
{
lean_object* v_unused_2571_; 
v_unused_2571_ = lean_ctor_get(v_opts_942_, 8);
lean_dec(v_unused_2571_);
v___x_2561_ = v_opts_942_;
v_isShared_2562_ = v_isSharedCheck_2570_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2559_);
lean_inc(v_incrLoadFileName_x3f_2558_);
lean_inc(v_incrSaveFileName_x3f_2557_);
lean_inc(v_errorOnKinds_2554_);
lean_inc(v_cFileName_x3f_2552_);
lean_inc(v_ileanFileName_x3f_2551_);
lean_inc(v_oleanFileName_x3f_2550_);
lean_inc(v_setupFileName_x3f_2549_);
lean_inc(v_rootDir_x3f_2548_);
lean_inc(v_opts_2545_);
lean_inc(v_forwardedArgs_2537_);
lean_inc(v_leanOpts_2536_);
lean_dec(v_opts_942_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2570_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2563_; lean_object* v___x_2565_; 
v___x_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2563_, 0, v_a_2532_);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 8, v___x_2563_);
v___x_2565_ = v___x_2561_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_leanOpts_2536_);
lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_forwardedArgs_2537_);
lean_ctor_set(v_reuseFailAlloc_2569_, 2, v_opts_2545_);
lean_ctor_set(v_reuseFailAlloc_2569_, 3, v_rootDir_x3f_2548_);
lean_ctor_set(v_reuseFailAlloc_2569_, 4, v_setupFileName_x3f_2549_);
lean_ctor_set(v_reuseFailAlloc_2569_, 5, v_oleanFileName_x3f_2550_);
lean_ctor_set(v_reuseFailAlloc_2569_, 6, v_ileanFileName_x3f_2551_);
lean_ctor_set(v_reuseFailAlloc_2569_, 7, v_cFileName_x3f_2552_);
lean_ctor_set(v_reuseFailAlloc_2569_, 8, v___x_2563_);
lean_ctor_set(v_reuseFailAlloc_2569_, 9, v_errorOnKinds_2554_);
lean_ctor_set(v_reuseFailAlloc_2569_, 10, v_incrSaveFileName_x3f_2557_);
lean_ctor_set(v_reuseFailAlloc_2569_, 11, v_incrLoadFileName_x3f_2558_);
lean_ctor_set(v_reuseFailAlloc_2569_, 12, v_incrHeaderSaveFileName_x3f_2559_);
lean_ctor_set_uint8(v_reuseFailAlloc_2569_, sizeof(void*)*13 + 8, v_component_2538_);
lean_ctor_set_uint8(v_reuseFailAlloc_2569_, sizeof(void*)*13 + 9, v_printPrefix_2539_);
lean_ctor_set_uint8(v_reuseFailAlloc_2569_, sizeof(void*)*13 + 10, v_printLibDir_2540_);
lean_ctor_set_uint8(v_reuseFailAlloc_2569_, sizeof(void*)*13 + 11, v_useStdin_2541_);
lean_ctor_set_uint8(v_reuseFailAlloc_2569_, sizeof(void*)*13 + 12, v_onlyDeps_2542_);
lean_ctor_set_uint8(v_reuseFailAlloc_2569_, sizeof(void*)*13 + 13, v_onlySrcDeps_2543_);
lean_ctor_set_uint8(v_reuseFailAlloc_2569_, sizeof(void*)*13 + 14, v_depsJson_2544_);
lean_ctor_set_uint32(v_reuseFailAlloc_2569_, sizeof(void*)*13, v_trustLevel_2546_);
lean_ctor_set_uint32(v_reuseFailAlloc_2569_, sizeof(void*)*13 + 4, v_numThreads_2547_);
lean_ctor_set_uint8(v_reuseFailAlloc_2569_, sizeof(void*)*13 + 15, v_jsonOutput_2553_);
lean_ctor_set_uint8(v_reuseFailAlloc_2569_, sizeof(void*)*13 + 16, v_printStats_2555_);
lean_ctor_set_uint8(v_reuseFailAlloc_2569_, sizeof(void*)*13 + 17, v_run_2556_);
v___x_2565_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
lean_object* v___x_2567_; 
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 0, v___x_2565_);
v___x_2567_ = v___x_2534_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2565_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
lean_dec_ref(v_opts_942_);
v_a_2573_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_a_2573_);
lean_dec_ref_known(v___x_2531_, 1);
v___x_2577_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2578_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2577_);
lean_dec_ref(v___x_2578_);
goto v___jp_2574_;
v___jp_2574_:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2575_ = lean_io_error_to_string(v_a_2573_);
v___x_2576_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2575_);
lean_dec_ref(v___x_2576_);
goto v___jp_1143_;
}
}
}
}
else
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2579_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33));
v___x_2580_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2579_, v_optArg_x3f_944_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2621_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2583_ = v___x_2580_;
v_isShared_2584_ = v_isSharedCheck_2621_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2580_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2621_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v_leanOpts_2585_; lean_object* v_forwardedArgs_2586_; uint8_t v_component_2587_; uint8_t v_printPrefix_2588_; uint8_t v_printLibDir_2589_; uint8_t v_useStdin_2590_; uint8_t v_onlyDeps_2591_; uint8_t v_onlySrcDeps_2592_; uint8_t v_depsJson_2593_; lean_object* v_opts_2594_; uint32_t v_trustLevel_2595_; uint32_t v_numThreads_2596_; lean_object* v_rootDir_x3f_2597_; lean_object* v_setupFileName_x3f_2598_; lean_object* v_oleanFileName_x3f_2599_; lean_object* v_ileanFileName_x3f_2600_; lean_object* v_bcFileName_x3f_2601_; uint8_t v_jsonOutput_2602_; lean_object* v_errorOnKinds_2603_; uint8_t v_printStats_2604_; uint8_t v_run_2605_; lean_object* v_incrSaveFileName_x3f_2606_; lean_object* v_incrLoadFileName_x3f_2607_; lean_object* v_incrHeaderSaveFileName_x3f_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2619_; 
v_leanOpts_2585_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_2586_ = lean_ctor_get(v_opts_942_, 1);
v_component_2587_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_2588_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_2589_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_2590_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_2591_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2592_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_2593_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_2594_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_2595_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_numThreads_2596_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2597_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_2598_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_2599_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_2600_ = lean_ctor_get(v_opts_942_, 6);
v_bcFileName_x3f_2601_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_2602_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_2603_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_2604_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_2605_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2606_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_2607_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_2608_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_2619_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_2619_ == 0)
{
lean_object* v_unused_2620_; 
v_unused_2620_ = lean_ctor_get(v_opts_942_, 7);
lean_dec(v_unused_2620_);
v___x_2610_ = v_opts_942_;
v_isShared_2611_ = v_isSharedCheck_2619_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2608_);
lean_inc(v_incrLoadFileName_x3f_2607_);
lean_inc(v_incrSaveFileName_x3f_2606_);
lean_inc(v_errorOnKinds_2603_);
lean_inc(v_bcFileName_x3f_2601_);
lean_inc(v_ileanFileName_x3f_2600_);
lean_inc(v_oleanFileName_x3f_2599_);
lean_inc(v_setupFileName_x3f_2598_);
lean_inc(v_rootDir_x3f_2597_);
lean_inc(v_opts_2594_);
lean_inc(v_forwardedArgs_2586_);
lean_inc(v_leanOpts_2585_);
lean_dec(v_opts_942_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2619_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2612_; lean_object* v___x_2614_; 
v___x_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2612_, 0, v_a_2581_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 7, v___x_2612_);
v___x_2614_ = v___x_2610_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_leanOpts_2585_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v_forwardedArgs_2586_);
lean_ctor_set(v_reuseFailAlloc_2618_, 2, v_opts_2594_);
lean_ctor_set(v_reuseFailAlloc_2618_, 3, v_rootDir_x3f_2597_);
lean_ctor_set(v_reuseFailAlloc_2618_, 4, v_setupFileName_x3f_2598_);
lean_ctor_set(v_reuseFailAlloc_2618_, 5, v_oleanFileName_x3f_2599_);
lean_ctor_set(v_reuseFailAlloc_2618_, 6, v_ileanFileName_x3f_2600_);
lean_ctor_set(v_reuseFailAlloc_2618_, 7, v___x_2612_);
lean_ctor_set(v_reuseFailAlloc_2618_, 8, v_bcFileName_x3f_2601_);
lean_ctor_set(v_reuseFailAlloc_2618_, 9, v_errorOnKinds_2603_);
lean_ctor_set(v_reuseFailAlloc_2618_, 10, v_incrSaveFileName_x3f_2606_);
lean_ctor_set(v_reuseFailAlloc_2618_, 11, v_incrLoadFileName_x3f_2607_);
lean_ctor_set(v_reuseFailAlloc_2618_, 12, v_incrHeaderSaveFileName_x3f_2608_);
lean_ctor_set_uint8(v_reuseFailAlloc_2618_, sizeof(void*)*13 + 8, v_component_2587_);
lean_ctor_set_uint8(v_reuseFailAlloc_2618_, sizeof(void*)*13 + 9, v_printPrefix_2588_);
lean_ctor_set_uint8(v_reuseFailAlloc_2618_, sizeof(void*)*13 + 10, v_printLibDir_2589_);
lean_ctor_set_uint8(v_reuseFailAlloc_2618_, sizeof(void*)*13 + 11, v_useStdin_2590_);
lean_ctor_set_uint8(v_reuseFailAlloc_2618_, sizeof(void*)*13 + 12, v_onlyDeps_2591_);
lean_ctor_set_uint8(v_reuseFailAlloc_2618_, sizeof(void*)*13 + 13, v_onlySrcDeps_2592_);
lean_ctor_set_uint8(v_reuseFailAlloc_2618_, sizeof(void*)*13 + 14, v_depsJson_2593_);
lean_ctor_set_uint32(v_reuseFailAlloc_2618_, sizeof(void*)*13, v_trustLevel_2595_);
lean_ctor_set_uint32(v_reuseFailAlloc_2618_, sizeof(void*)*13 + 4, v_numThreads_2596_);
lean_ctor_set_uint8(v_reuseFailAlloc_2618_, sizeof(void*)*13 + 15, v_jsonOutput_2602_);
lean_ctor_set_uint8(v_reuseFailAlloc_2618_, sizeof(void*)*13 + 16, v_printStats_2604_);
lean_ctor_set_uint8(v_reuseFailAlloc_2618_, sizeof(void*)*13 + 17, v_run_2605_);
v___x_2614_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
lean_object* v___x_2616_; 
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v___x_2614_);
v___x_2616_ = v___x_2583_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2614_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
lean_dec_ref(v_opts_942_);
v_a_2622_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2622_);
lean_dec_ref_known(v___x_2580_, 1);
v___x_2626_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2627_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2626_);
lean_dec_ref(v___x_2627_);
goto v___jp_2623_;
v___jp_2623_:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = lean_io_error_to_string(v_a_2622_);
v___x_2625_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2624_);
lean_dec_ref(v___x_2625_);
goto v___jp_973_;
}
}
}
}
else
{
lean_object* v___x_2628_; lean_object* v___x_2629_; 
lean_dec(v_optArg_x3f_944_);
lean_dec_ref(v_opts_942_);
v___x_2628_ = l___private_Lean_Shell_0__Lean_featuresString;
v___x_2629_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2628_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2637_; 
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2637_ == 0)
{
lean_object* v_unused_2638_; 
v_unused_2638_ = lean_ctor_get(v___x_2629_, 0);
lean_dec(v_unused_2638_);
v___x_2631_ = v___x_2629_;
v_isShared_2632_ = v_isSharedCheck_2637_;
goto v_resetjp_2630_;
}
else
{
lean_dec(v___x_2629_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2637_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2633_; lean_object* v___x_2635_; 
v___x_2633_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2632_ == 0)
{
lean_ctor_set_tag(v___x_2631_, 1);
lean_ctor_set(v___x_2631_, 0, v___x_2633_);
v___x_2635_ = v___x_2631_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2633_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v_a_2639_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2639_);
lean_dec_ref_known(v___x_2629_, 1);
v___x_2643_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2644_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2643_);
lean_dec_ref(v___x_2644_);
goto v___jp_2640_;
v___jp_2640_:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2641_ = lean_io_error_to_string(v_a_2639_);
v___x_2642_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2641_);
lean_dec_ref(v___x_2642_);
goto v___jp_1149_;
}
}
}
}
else
{
lean_object* v___x_2645_; 
lean_dec(v_optArg_x3f_944_);
lean_dec_ref(v_opts_942_);
v___x_2645_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1173_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2653_; 
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2653_ == 0)
{
lean_object* v_unused_2654_; 
v_unused_2654_ = lean_ctor_get(v___x_2645_, 0);
lean_dec(v_unused_2654_);
v___x_2647_ = v___x_2645_;
v_isShared_2648_ = v_isSharedCheck_2653_;
goto v_resetjp_2646_;
}
else
{
lean_dec(v___x_2645_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2653_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2649_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2648_ == 0)
{
lean_ctor_set_tag(v___x_2647_, 1);
lean_ctor_set(v___x_2647_, 0, v___x_2649_);
v___x_2651_ = v___x_2647_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
else
{
lean_object* v_a_2655_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v_a_2655_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2655_);
lean_dec_ref_known(v___x_2645_, 1);
v___x_2659_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2660_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2659_);
lean_dec_ref(v___x_2660_);
goto v___jp_2656_;
v___jp_2656_:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = lean_io_error_to_string(v_a_2655_);
v___x_2658_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2657_);
lean_dec_ref(v___x_2658_);
goto v___jp_967_;
}
}
}
}
else
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
lean_dec(v_optArg_x3f_944_);
lean_dec_ref(v_opts_942_);
v___x_2661_ = l_Lean_githash;
v___x_2662_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2661_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2670_; 
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2670_ == 0)
{
lean_object* v_unused_2671_; 
v_unused_2671_ = lean_ctor_get(v___x_2662_, 0);
lean_dec(v_unused_2671_);
v___x_2664_ = v___x_2662_;
v_isShared_2665_ = v_isSharedCheck_2670_;
goto v_resetjp_2663_;
}
else
{
lean_dec(v___x_2662_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2670_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2666_; lean_object* v___x_2668_; 
v___x_2666_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2665_ == 0)
{
lean_ctor_set_tag(v___x_2664_, 1);
lean_ctor_set(v___x_2664_, 0, v___x_2666_);
v___x_2668_ = v___x_2664_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2666_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
else
{
lean_object* v_a_2672_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v_a_2672_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2672_);
lean_dec_ref_known(v___x_2662_, 1);
v___x_2676_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2677_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2676_);
lean_dec_ref(v___x_2677_);
goto v___jp_2673_;
v___jp_2673_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2674_ = lean_io_error_to_string(v_a_2672_);
v___x_2675_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2674_);
lean_dec_ref(v___x_2675_);
goto v___jp_1155_;
}
}
}
}
else
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
lean_dec(v_optArg_x3f_944_);
lean_dec_ref(v_opts_942_);
v___x_2678_ = l___private_Lean_Shell_0__Lean_shortVersionString;
v___x_2679_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2678_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2687_; 
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2687_ == 0)
{
lean_object* v_unused_2688_; 
v_unused_2688_ = lean_ctor_get(v___x_2679_, 0);
lean_dec(v_unused_2688_);
v___x_2681_ = v___x_2679_;
v_isShared_2682_ = v_isSharedCheck_2687_;
goto v_resetjp_2680_;
}
else
{
lean_dec(v___x_2679_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2687_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2683_; lean_object* v___x_2685_; 
v___x_2683_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2682_ == 0)
{
lean_ctor_set_tag(v___x_2681_, 1);
lean_ctor_set(v___x_2681_, 0, v___x_2683_);
v___x_2685_ = v___x_2681_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2683_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v_a_2689_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2689_);
lean_dec_ref_known(v___x_2679_, 1);
v___x_2693_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2694_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2693_);
lean_dec_ref(v___x_2694_);
goto v___jp_2690_;
v___jp_2690_:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2691_ = lean_io_error_to_string(v_a_2689_);
v___x_2692_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2691_);
lean_dec_ref(v___x_2692_);
goto v___jp_961_;
}
}
}
}
else
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
lean_dec(v_optArg_x3f_944_);
lean_dec_ref(v_opts_942_);
v___x_2695_ = l___private_Lean_Shell_0__Lean_versionHeader;
v___x_2696_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2695_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2704_; 
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2704_ == 0)
{
lean_object* v_unused_2705_; 
v_unused_2705_ = lean_ctor_get(v___x_2696_, 0);
lean_dec(v_unused_2705_);
v___x_2698_ = v___x_2696_;
v_isShared_2699_ = v_isSharedCheck_2704_;
goto v_resetjp_2697_;
}
else
{
lean_dec(v___x_2696_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2704_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2700_; lean_object* v___x_2702_; 
v___x_2700_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2699_ == 0)
{
lean_ctor_set_tag(v___x_2698_, 1);
lean_ctor_set(v___x_2698_, 0, v___x_2700_);
v___x_2702_ = v___x_2698_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2700_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v_a_2706_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2696_, 1);
v___x_2710_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2711_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2710_);
lean_dec_ref(v___x_2711_);
goto v___jp_2707_;
v___jp_2707_:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2708_ = lean_io_error_to_string(v_a_2706_);
v___x_2709_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2708_);
lean_dec_ref(v___x_2709_);
goto v___jp_1161_;
}
}
}
}
else
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2712_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34));
v___x_2713_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2712_, v_optArg_x3f_944_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2767_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2716_ = v___x_2713_;
v_isShared_2717_ = v_isSharedCheck_2767_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2713_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2767_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2718_ = lean_unsigned_to_nat(0u);
v___x_2719_ = lean_string_utf8_byte_size(v_a_2714_);
lean_inc(v_a_2714_);
v___x_2720_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2720_, 0, v_a_2714_);
lean_ctor_set(v___x_2720_, 1, v___x_2718_);
lean_ctor_set(v___x_2720_, 2, v___x_2719_);
v___x_2721_ = l_String_Slice_toNat_x3f(v___x_2720_);
lean_dec_ref_known(v___x_2720_, 3);
if (lean_obj_tag(v___x_2721_) == 1)
{
lean_object* v_val_2722_; lean_object* v___x_2723_; uint8_t v___x_2724_; 
v_val_2722_ = lean_ctor_get(v___x_2721_, 0);
lean_inc(v_val_2722_);
lean_dec_ref_known(v___x_2721_, 1);
v___x_2723_ = lean_cstr_to_nat("4294967296");
v___x_2724_ = lean_nat_dec_lt(v_val_2722_, v___x_2723_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2725_; lean_object* v___x_2726_; 
lean_dec(v_val_2722_);
lean_del_object(v___x_2716_);
lean_dec(v_a_2714_);
lean_dec_ref(v_opts_942_);
v___x_2725_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__35));
v___x_2726_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2725_);
lean_dec_ref(v___x_2726_);
goto v___jp_955_;
}
else
{
lean_object* v_leanOpts_2727_; lean_object* v_forwardedArgs_2728_; uint8_t v_component_2729_; uint8_t v_printPrefix_2730_; uint8_t v_printLibDir_2731_; uint8_t v_useStdin_2732_; uint8_t v_onlyDeps_2733_; uint8_t v_onlySrcDeps_2734_; uint8_t v_depsJson_2735_; lean_object* v_opts_2736_; uint32_t v_trustLevel_2737_; lean_object* v_rootDir_x3f_2738_; lean_object* v_setupFileName_x3f_2739_; lean_object* v_oleanFileName_x3f_2740_; lean_object* v_ileanFileName_x3f_2741_; lean_object* v_cFileName_x3f_2742_; lean_object* v_bcFileName_x3f_2743_; uint8_t v_jsonOutput_2744_; lean_object* v_errorOnKinds_2745_; uint8_t v_printStats_2746_; uint8_t v_run_2747_; lean_object* v_incrSaveFileName_x3f_2748_; lean_object* v_incrLoadFileName_x3f_2749_; lean_object* v_incrHeaderSaveFileName_x3f_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2764_; 
v_leanOpts_2727_ = lean_ctor_get(v_opts_942_, 0);
v_forwardedArgs_2728_ = lean_ctor_get(v_opts_942_, 1);
v_component_2729_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 8);
v_printPrefix_2730_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 9);
v_printLibDir_2731_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 10);
v_useStdin_2732_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 11);
v_onlyDeps_2733_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2734_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 13);
v_depsJson_2735_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 14);
v_opts_2736_ = lean_ctor_get(v_opts_942_, 2);
v_trustLevel_2737_ = lean_ctor_get_uint32(v_opts_942_, sizeof(void*)*13);
v_rootDir_x3f_2738_ = lean_ctor_get(v_opts_942_, 3);
v_setupFileName_x3f_2739_ = lean_ctor_get(v_opts_942_, 4);
v_oleanFileName_x3f_2740_ = lean_ctor_get(v_opts_942_, 5);
v_ileanFileName_x3f_2741_ = lean_ctor_get(v_opts_942_, 6);
v_cFileName_x3f_2742_ = lean_ctor_get(v_opts_942_, 7);
v_bcFileName_x3f_2743_ = lean_ctor_get(v_opts_942_, 8);
v_jsonOutput_2744_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 15);
v_errorOnKinds_2745_ = lean_ctor_get(v_opts_942_, 9);
v_printStats_2746_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 16);
v_run_2747_ = lean_ctor_get_uint8(v_opts_942_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2748_ = lean_ctor_get(v_opts_942_, 10);
v_incrLoadFileName_x3f_2749_ = lean_ctor_get(v_opts_942_, 11);
v_incrHeaderSaveFileName_x3f_2750_ = lean_ctor_get(v_opts_942_, 12);
v_isSharedCheck_2764_ = !lean_is_exclusive(v_opts_942_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2752_ = v_opts_942_;
v_isShared_2753_ = v_isSharedCheck_2764_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2750_);
lean_inc(v_incrLoadFileName_x3f_2749_);
lean_inc(v_incrSaveFileName_x3f_2748_);
lean_inc(v_errorOnKinds_2745_);
lean_inc(v_bcFileName_x3f_2743_);
lean_inc(v_cFileName_x3f_2742_);
lean_inc(v_ileanFileName_x3f_2741_);
lean_inc(v_oleanFileName_x3f_2740_);
lean_inc(v_setupFileName_x3f_2739_);
lean_inc(v_rootDir_x3f_2738_);
lean_inc(v_opts_2736_);
lean_inc(v_forwardedArgs_2728_);
lean_inc(v_leanOpts_2727_);
lean_dec(v_opts_942_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2764_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
uint32_t v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2759_; 
v___x_2754_ = lean_uint32_of_nat(v_val_2722_);
lean_dec(v_val_2722_);
v___x_2755_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__36));
v___x_2756_ = lean_string_append(v___x_2755_, v_a_2714_);
lean_dec(v_a_2714_);
v___x_2757_ = lean_array_push(v_forwardedArgs_2728_, v___x_2756_);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 1, v___x_2757_);
v___x_2759_ = v___x_2752_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_leanOpts_2727_);
lean_ctor_set(v_reuseFailAlloc_2763_, 1, v___x_2757_);
lean_ctor_set(v_reuseFailAlloc_2763_, 2, v_opts_2736_);
lean_ctor_set(v_reuseFailAlloc_2763_, 3, v_rootDir_x3f_2738_);
lean_ctor_set(v_reuseFailAlloc_2763_, 4, v_setupFileName_x3f_2739_);
lean_ctor_set(v_reuseFailAlloc_2763_, 5, v_oleanFileName_x3f_2740_);
lean_ctor_set(v_reuseFailAlloc_2763_, 6, v_ileanFileName_x3f_2741_);
lean_ctor_set(v_reuseFailAlloc_2763_, 7, v_cFileName_x3f_2742_);
lean_ctor_set(v_reuseFailAlloc_2763_, 8, v_bcFileName_x3f_2743_);
lean_ctor_set(v_reuseFailAlloc_2763_, 9, v_errorOnKinds_2745_);
lean_ctor_set(v_reuseFailAlloc_2763_, 10, v_incrSaveFileName_x3f_2748_);
lean_ctor_set(v_reuseFailAlloc_2763_, 11, v_incrLoadFileName_x3f_2749_);
lean_ctor_set(v_reuseFailAlloc_2763_, 12, v_incrHeaderSaveFileName_x3f_2750_);
lean_ctor_set_uint8(v_reuseFailAlloc_2763_, sizeof(void*)*13 + 8, v_component_2729_);
lean_ctor_set_uint8(v_reuseFailAlloc_2763_, sizeof(void*)*13 + 9, v_printPrefix_2730_);
lean_ctor_set_uint8(v_reuseFailAlloc_2763_, sizeof(void*)*13 + 10, v_printLibDir_2731_);
lean_ctor_set_uint8(v_reuseFailAlloc_2763_, sizeof(void*)*13 + 11, v_useStdin_2732_);
lean_ctor_set_uint8(v_reuseFailAlloc_2763_, sizeof(void*)*13 + 12, v_onlyDeps_2733_);
lean_ctor_set_uint8(v_reuseFailAlloc_2763_, sizeof(void*)*13 + 13, v_onlySrcDeps_2734_);
lean_ctor_set_uint8(v_reuseFailAlloc_2763_, sizeof(void*)*13 + 14, v_depsJson_2735_);
lean_ctor_set_uint32(v_reuseFailAlloc_2763_, sizeof(void*)*13, v_trustLevel_2737_);
lean_ctor_set_uint8(v_reuseFailAlloc_2763_, sizeof(void*)*13 + 15, v_jsonOutput_2744_);
lean_ctor_set_uint8(v_reuseFailAlloc_2763_, sizeof(void*)*13 + 16, v_printStats_2746_);
lean_ctor_set_uint8(v_reuseFailAlloc_2763_, sizeof(void*)*13 + 17, v_run_2747_);
v___x_2759_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
lean_object* v___x_2761_; 
lean_ctor_set_uint32(v___x_2759_, sizeof(void*)*13 + 4, v___x_2754_);
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 0, v___x_2759_);
v___x_2761_ = v___x_2716_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2759_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
}
else
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
lean_dec(v___x_2721_);
lean_del_object(v___x_2716_);
lean_dec(v_a_2714_);
lean_dec_ref(v_opts_942_);
v___x_2765_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__37));
v___x_2766_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2765_);
lean_dec_ref(v___x_2766_);
goto v___jp_952_;
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
lean_dec_ref(v_opts_942_);
v_a_2768_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_a_2768_);
lean_dec_ref_known(v___x_2713_, 1);
v___x_2772_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2773_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2772_);
lean_dec_ref(v___x_2773_);
goto v___jp_2769_;
v___jp_2769_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2770_ = lean_io_error_to_string(v_a_2768_);
v___x_2771_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2770_);
lean_dec_ref(v___x_2771_);
goto v___jp_949_;
}
}
}
}
else
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
lean_dec(v_optArg_x3f_944_);
v___x_2774_ = lean_internal_set_exit_on_panic(v___x_1165_);
v___x_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2775_, 0, v_opts_942_);
return v___x_2775_;
}
v___jp_946_:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
return v___x_948_;
}
v___jp_949_:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_951_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_950_);
lean_dec_ref(v___x_951_);
goto v___jp_946_;
}
v___jp_952_:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
return v___x_954_;
}
v___jp_955_:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
return v___x_957_;
}
v___jp_958_:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
return v___x_960_;
}
v___jp_961_:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_963_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_962_);
lean_dec_ref(v___x_963_);
goto v___jp_958_;
}
v___jp_964_:
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
return v___x_966_;
}
v___jp_967_:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_969_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_968_);
lean_dec_ref(v___x_969_);
goto v___jp_964_;
}
v___jp_970_:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
return v___x_972_;
}
v___jp_973_:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_975_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_974_);
lean_dec_ref(v___x_975_);
goto v___jp_970_;
}
v___jp_976_:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
return v___x_978_;
}
v___jp_979_:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_981_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_980_);
lean_dec_ref(v___x_981_);
goto v___jp_976_;
}
v___jp_982_:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
v___jp_985_:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
return v___x_987_;
}
v___jp_988_:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
return v___x_990_;
}
v___jp_991_:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_993_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_992_);
lean_dec_ref(v___x_993_);
goto v___jp_988_;
}
v___jp_994_:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
return v___x_996_;
}
v___jp_997_:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_999_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_998_);
lean_dec_ref(v___x_999_);
goto v___jp_994_;
}
v___jp_1000_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
return v___x_1002_;
}
v___jp_1003_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
return v___x_1005_;
}
v___jp_1006_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1008_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1007_);
lean_dec_ref(v___x_1008_);
goto v___jp_1003_;
}
v___jp_1009_:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
return v___x_1011_;
}
v___jp_1012_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
return v___x_1014_;
}
v___jp_1015_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
return v___x_1017_;
}
v___jp_1018_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1020_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1019_);
lean_dec_ref(v___x_1020_);
goto v___jp_1015_;
}
v___jp_1021_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
return v___x_1023_;
}
v___jp_1024_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1026_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1025_);
lean_dec_ref(v___x_1026_);
goto v___jp_1021_;
}
v___jp_1027_:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
return v___x_1029_;
}
v___jp_1030_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1032_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1031_);
lean_dec_ref(v___x_1032_);
goto v___jp_1027_;
}
v___jp_1033_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
return v___x_1035_;
}
v___jp_1036_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1038_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1037_);
lean_dec_ref(v___x_1038_);
goto v___jp_1033_;
}
v___jp_1039_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
return v___x_1041_;
}
v___jp_1042_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1044_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1043_);
lean_dec_ref(v___x_1044_);
goto v___jp_1039_;
}
v___jp_1045_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
return v___x_1047_;
}
v___jp_1048_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1050_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1049_);
lean_dec_ref(v___x_1050_);
goto v___jp_1045_;
}
v___jp_1051_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
return v___x_1053_;
}
v___jp_1054_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1056_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1055_);
lean_dec_ref(v___x_1056_);
goto v___jp_1051_;
}
v___jp_1057_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_io_error_to_string(v___y_1058_);
v___x_1060_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1059_);
lean_dec_ref(v___x_1060_);
goto v___jp_1054_;
}
v___jp_1061_:
{
uint8_t v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = 1;
v___x_1063_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1062_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1071_; 
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; 
v_unused_1072_ = lean_ctor_get(v___x_1063_, 0);
lean_dec(v_unused_1072_);
v___x_1065_ = v___x_1063_;
v_isShared_1066_ = v_isSharedCheck_1071_;
goto v_resetjp_1064_;
}
else
{
lean_dec(v___x_1063_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1071_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1067_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_1066_ == 0)
{
lean_ctor_set_tag(v___x_1065_, 1);
lean_ctor_set(v___x_1065_, 0, v___x_1067_);
v___x_1069_ = v___x_1065_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_a_1073_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v___x_1063_, 1);
v___x_1074_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1075_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1074_);
lean_dec_ref(v___x_1075_);
v___y_1058_ = v_a_1073_;
goto v___jp_1057_;
}
}
v___jp_1076_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__0));
v___x_1078_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1077_);
lean_dec_ref(v___x_1078_);
goto v___jp_1061_;
}
v___jp_1079_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
return v___x_1081_;
}
v___jp_1082_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1084_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1083_);
lean_dec_ref(v___x_1084_);
goto v___jp_1079_;
}
v___jp_1085_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
return v___x_1087_;
}
v___jp_1088_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1090_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1089_);
lean_dec_ref(v___x_1090_);
goto v___jp_1085_;
}
v___jp_1091_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
return v___x_1093_;
}
v___jp_1094_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1096_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1095_);
lean_dec_ref(v___x_1096_);
goto v___jp_1091_;
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
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = lean_io_error_to_string(v___y_1104_);
v___x_1106_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1105_);
lean_dec_ref(v___x_1106_);
goto v___jp_1100_;
}
v___jp_1107_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
return v___x_1109_;
}
v___jp_1110_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1112_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1111_);
lean_dec_ref(v___x_1112_);
goto v___jp_1107_;
}
v___jp_1113_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
return v___x_1115_;
}
v___jp_1116_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1118_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1117_);
lean_dec_ref(v___x_1118_);
goto v___jp_1113_;
}
v___jp_1119_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
return v___x_1121_;
}
v___jp_1122_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
return v___x_1124_;
}
v___jp_1125_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1127_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1126_);
lean_dec_ref(v___x_1127_);
goto v___jp_1122_;
}
v___jp_1128_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
return v___x_1130_;
}
v___jp_1131_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1133_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1132_);
lean_dec_ref(v___x_1133_);
goto v___jp_1128_;
}
v___jp_1134_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
return v___x_1136_;
}
v___jp_1137_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1139_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1138_);
lean_dec_ref(v___x_1139_);
goto v___jp_1134_;
}
v___jp_1140_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
return v___x_1142_;
}
v___jp_1143_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1145_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1144_);
lean_dec_ref(v___x_1145_);
goto v___jp_1140_;
}
v___jp_1146_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
return v___x_1148_;
}
v___jp_1149_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1151_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1150_);
lean_dec_ref(v___x_1151_);
goto v___jp_1146_;
}
v___jp_1152_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
return v___x_1154_;
}
v___jp_1155_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1157_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1156_);
lean_dec_ref(v___x_1157_);
goto v___jp_1152_;
}
v___jp_1158_:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
return v___x_1160_;
}
v___jp_1161_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1163_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1162_);
lean_dec_ref(v___x_1163_);
goto v___jp_1158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed(lean_object* v_opts_2776_, lean_object* v_opt_2777_, lean_object* v_optArg_x3f_2778_, lean_object* v_a_2779_){
_start:
{
uint32_t v_opt_boxed_2780_; lean_object* v_res_2781_; 
v_opt_boxed_2780_ = lean_unbox_uint32(v_opt_2777_);
lean_dec(v_opt_2777_);
v_res_2781_ = lean_shell_options_process(v_opts_2776_, v_opt_boxed_2780_, v_optArg_x3f_2778_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(lean_object* v_opts_2782_, lean_object* v_opt_2783_){
_start:
{
lean_object* v_name_2784_; lean_object* v_defValue_2785_; lean_object* v_map_2786_; lean_object* v___x_2787_; 
v_name_2784_ = lean_ctor_get(v_opt_2783_, 0);
v_defValue_2785_ = lean_ctor_get(v_opt_2783_, 1);
v_map_2786_ = lean_ctor_get(v_opts_2782_, 0);
v___x_2787_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2786_, v_name_2784_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_inc(v_defValue_2785_);
return v_defValue_2785_;
}
else
{
lean_object* v_val_2788_; 
v_val_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_val_2788_);
lean_dec_ref_known(v___x_2787_, 1);
if (lean_obj_tag(v_val_2788_) == 3)
{
lean_object* v_v_2789_; 
v_v_2789_ = lean_ctor_get(v_val_2788_, 0);
lean_inc(v_v_2789_);
lean_dec_ref_known(v_val_2788_, 1);
return v_v_2789_;
}
else
{
lean_dec(v_val_2788_);
lean_inc(v_defValue_2785_);
return v_defValue_2785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___boxed(lean_object* v_opts_2790_, lean_object* v_opt_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_opts_2790_, v_opt_2791_);
lean_dec_ref(v_opt_2791_);
lean_dec_ref(v_opts_2790_);
return v_res_2792_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2795_ = lean_string_utf8_byte_size(v___x_2794_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(lean_object* v_s_2796_){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; uint8_t v___x_2800_; 
v___x_2797_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2798_ = lean_string_utf8_byte_size(v_s_2796_);
v___x_2799_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1);
v___x_2800_ = lean_nat_dec_le(v___x_2799_, v___x_2798_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2801_; 
lean_dec_ref(v_s_2796_);
v___x_2801_ = lean_box(0);
return v___x_2801_;
}
else
{
lean_object* v___x_2802_; uint8_t v___x_2803_; 
v___x_2802_ = lean_unsigned_to_nat(0u);
v___x_2803_ = lean_string_memcmp(v_s_2796_, v___x_2797_, v___x_2802_, v___x_2802_, v___x_2799_);
if (v___x_2803_ == 0)
{
lean_object* v___x_2804_; 
lean_dec_ref(v_s_2796_);
v___x_2804_ = lean_box(0);
return v___x_2804_;
}
else
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
lean_inc_ref(v_s_2796_);
v___x_2805_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2805_, 0, v_s_2796_);
lean_ctor_set(v___x_2805_, 1, v___x_2802_);
lean_ctor_set(v___x_2805_, 2, v___x_2798_);
v___x_2806_ = l_String_Slice_pos_x21(v___x_2805_, v___x_2799_);
lean_dec_ref_known(v___x_2805_, 3);
v___x_2807_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2807_, 0, v_s_2796_);
lean_ctor_set(v___x_2807_, 1, v___x_2806_);
lean_ctor_set(v___x_2807_, 2, v___x_2798_);
v___x_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
return v___x_2808_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(lean_object* v_s_2809_, lean_object* v_pat_2810_){
_start:
{
lean_object* v___x_2811_; 
v___x_2811_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v_s_2809_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___boxed(lean_object* v_s_2812_, lean_object* v_pat_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(v_s_2812_, v_pat_2813_);
lean_dec_ref(v_pat_2813_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object* v___x_2818_, lean_object* v___x_2819_, lean_object* v_mainModuleName_2820_, lean_object* v_a_2821_, uint8_t v___x_2822_, lean_object* v___x_2823_, lean_object* v_fileName_2824_, lean_object* v___x_2825_, lean_object* v___x_2826_, lean_object* v___x_2827_, lean_object* v___x_2828_, lean_object* v___x_2829_, lean_object* v___x_2830_, lean_object* v___x_2831_, lean_object* v___x_2832_, uint8_t v_run_2833_){
_start:
{
lean_object* v_a_2836_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v_env_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; lean_object* v_fileName_2848_; lean_object* v_fileMap_2849_; lean_object* v_currRecDepth_2850_; lean_object* v_ref_2851_; lean_object* v_currNamespace_2852_; lean_object* v_openDecls_2853_; lean_object* v_initHeartbeats_2854_; lean_object* v_maxHeartbeats_2855_; lean_object* v_quotContext_2856_; lean_object* v_currMacroScope_2857_; lean_object* v_cancelTk_x3f_2858_; uint8_t v_suppressElabErrors_2859_; lean_object* v_inheritedTraceOptions_2860_; lean_object* v___y_2861_; uint8_t v___y_2893_; uint8_t v___x_2913_; 
v___x_2839_ = lean_io_get_num_heartbeats();
v___x_2840_ = lean_st_mk_ref(v___x_2818_);
v___x_2841_ = l_Lean_inheritedTraceOptions;
v___x_2842_ = lean_st_ref_get(v___x_2841_);
v___x_2843_ = lean_st_ref_get(v___x_2840_);
v_env_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc_ref(v_env_2844_);
lean_dec(v___x_2843_);
v___x_2845_ = l_Lean_diagnostics;
v___x_2846_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v___x_2819_, v___x_2845_);
v___x_2913_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2844_);
lean_dec_ref(v_env_2844_);
if (v___x_2913_ == 0)
{
if (v___x_2846_ == 0)
{
lean_dec_ref(v___x_2823_);
lean_inc(v___x_2840_);
lean_inc(v___x_2828_);
v_fileName_2848_ = v_fileName_2824_;
v_fileMap_2849_ = v___x_2825_;
v_currRecDepth_2850_ = v___x_2826_;
v_ref_2851_ = v___x_2827_;
v_currNamespace_2852_ = v___x_2828_;
v_openDecls_2853_ = v___x_2829_;
v_initHeartbeats_2854_ = v___x_2839_;
v_maxHeartbeats_2855_ = v___x_2830_;
v_quotContext_2856_ = v___x_2828_;
v_currMacroScope_2857_ = v___x_2831_;
v_cancelTk_x3f_2858_ = v___x_2832_;
v_suppressElabErrors_2859_ = v_run_2833_;
v_inheritedTraceOptions_2860_ = v___x_2842_;
v___y_2861_ = v___x_2840_;
goto v___jp_2847_;
}
else
{
v___y_2893_ = v___x_2913_;
goto v___jp_2892_;
}
}
else
{
v___y_2893_ = v___x_2846_;
goto v___jp_2892_;
}
v___jp_2835_:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = lean_mk_io_user_error(v_a_2836_);
v___x_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2837_);
return v___x_2838_;
}
v___jp_2847_:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2862_ = l_Lean_maxRecDepth;
v___x_2863_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_2819_, v___x_2862_);
v___x_2864_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2864_, 0, v_fileName_2848_);
lean_ctor_set(v___x_2864_, 1, v_fileMap_2849_);
lean_ctor_set(v___x_2864_, 2, v___x_2819_);
lean_ctor_set(v___x_2864_, 3, v_currRecDepth_2850_);
lean_ctor_set(v___x_2864_, 4, v___x_2863_);
lean_ctor_set(v___x_2864_, 5, v_ref_2851_);
lean_ctor_set(v___x_2864_, 6, v_currNamespace_2852_);
lean_ctor_set(v___x_2864_, 7, v_openDecls_2853_);
lean_ctor_set(v___x_2864_, 8, v_initHeartbeats_2854_);
lean_ctor_set(v___x_2864_, 9, v_maxHeartbeats_2855_);
lean_ctor_set(v___x_2864_, 10, v_quotContext_2856_);
lean_ctor_set(v___x_2864_, 11, v_currMacroScope_2857_);
lean_ctor_set(v___x_2864_, 12, v_cancelTk_x3f_2858_);
lean_ctor_set(v___x_2864_, 13, v_inheritedTraceOptions_2860_);
lean_ctor_set_uint8(v___x_2864_, sizeof(void*)*14, v___x_2846_);
lean_ctor_set_uint8(v___x_2864_, sizeof(void*)*14 + 1, v_suppressElabErrors_2859_);
v___x_2865_ = l_Lean_Compiler_LCNF_emitC(v_mainModuleName_2820_, v___x_2864_, v___y_2861_);
lean_dec(v___y_2861_);
lean_dec_ref_known(v___x_2864_, 14);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v___x_2865_, 1);
v___x_2867_ = lean_st_ref_get(v___x_2840_);
lean_dec(v___x_2840_);
lean_dec(v___x_2867_);
v___x_2868_ = lean_string_to_utf8(v_a_2866_);
lean_dec(v_a_2866_);
v___x_2869_ = lean_io_prim_handle_write(v_a_2821_, v___x_2868_);
lean_dec_ref(v___x_2868_);
return v___x_2869_;
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2891_; 
lean_dec(v___x_2840_);
v_a_2870_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2872_ = v___x_2865_;
v_isShared_2873_ = v_isSharedCheck_2891_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2865_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2891_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
if (lean_obj_tag(v_a_2870_) == 0)
{
lean_object* v_msg_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2878_; 
v_msg_2874_ = lean_ctor_get(v_a_2870_, 1);
lean_inc_ref(v_msg_2874_);
lean_dec_ref_known(v_a_2870_, 2);
v___x_2875_ = l_Lean_MessageData_toString(v_msg_2874_);
v___x_2876_ = lean_mk_io_user_error(v___x_2875_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 0, v___x_2876_);
v___x_2878_ = v___x_2872_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2876_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
else
{
lean_object* v_id_2880_; lean_object* v___x_2881_; 
lean_del_object(v___x_2872_);
v_id_2880_ = lean_ctor_get(v_a_2870_, 0);
lean_inc(v_id_2880_);
lean_dec_ref_known(v_a_2870_, 2);
v___x_2881_ = l_Lean_InternalExceptionId_getName(v_id_2880_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_a_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
lean_dec(v_id_2880_);
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_a_2882_);
lean_dec_ref_known(v___x_2881_, 1);
v___x_2883_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0));
v___x_2884_ = l_Lean_Name_toString(v_a_2882_, v___x_2822_);
v___x_2885_ = lean_string_append(v___x_2883_, v___x_2884_);
lean_dec_ref(v___x_2884_);
v_a_2836_ = v___x_2885_;
goto v___jp_2835_;
}
else
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
lean_dec_ref_known(v___x_2881_, 1);
v___x_2886_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__1));
v___x_2887_ = l_Nat_reprFast(v_id_2880_);
v___x_2888_ = lean_string_append(v___x_2886_, v___x_2887_);
lean_dec_ref(v___x_2887_);
v___x_2889_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__2));
v___x_2890_ = lean_string_append(v___x_2888_, v___x_2889_);
v_a_2836_ = v___x_2890_;
goto v___jp_2835_;
}
}
}
}
}
v___jp_2892_:
{
if (v___y_2893_ == 0)
{
lean_object* v___x_2894_; lean_object* v_env_2895_; lean_object* v_nextMacroScope_2896_; lean_object* v_ngen_2897_; lean_object* v_auxDeclNGen_2898_; lean_object* v_traceState_2899_; lean_object* v_messages_2900_; lean_object* v_infoState_2901_; lean_object* v_snapshotTasks_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2911_; 
v___x_2894_ = lean_st_ref_take(v___x_2840_);
v_env_2895_ = lean_ctor_get(v___x_2894_, 0);
v_nextMacroScope_2896_ = lean_ctor_get(v___x_2894_, 1);
v_ngen_2897_ = lean_ctor_get(v___x_2894_, 2);
v_auxDeclNGen_2898_ = lean_ctor_get(v___x_2894_, 3);
v_traceState_2899_ = lean_ctor_get(v___x_2894_, 4);
v_messages_2900_ = lean_ctor_get(v___x_2894_, 6);
v_infoState_2901_ = lean_ctor_get(v___x_2894_, 7);
v_snapshotTasks_2902_ = lean_ctor_get(v___x_2894_, 8);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2911_ == 0)
{
lean_object* v_unused_2912_; 
v_unused_2912_ = lean_ctor_get(v___x_2894_, 5);
lean_dec(v_unused_2912_);
v___x_2904_ = v___x_2894_;
v_isShared_2905_ = v_isSharedCheck_2911_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_snapshotTasks_2902_);
lean_inc(v_infoState_2901_);
lean_inc(v_messages_2900_);
lean_inc(v_traceState_2899_);
lean_inc(v_auxDeclNGen_2898_);
lean_inc(v_ngen_2897_);
lean_inc(v_nextMacroScope_2896_);
lean_inc(v_env_2895_);
lean_dec(v___x_2894_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2911_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2906_; lean_object* v___x_2908_; 
v___x_2906_ = l_Lean_Kernel_enableDiag(v_env_2895_, v___x_2846_);
if (v_isShared_2905_ == 0)
{
lean_ctor_set(v___x_2904_, 5, v___x_2823_);
lean_ctor_set(v___x_2904_, 0, v___x_2906_);
v___x_2908_ = v___x_2904_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2906_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v_nextMacroScope_2896_);
lean_ctor_set(v_reuseFailAlloc_2910_, 2, v_ngen_2897_);
lean_ctor_set(v_reuseFailAlloc_2910_, 3, v_auxDeclNGen_2898_);
lean_ctor_set(v_reuseFailAlloc_2910_, 4, v_traceState_2899_);
lean_ctor_set(v_reuseFailAlloc_2910_, 5, v___x_2823_);
lean_ctor_set(v_reuseFailAlloc_2910_, 6, v_messages_2900_);
lean_ctor_set(v_reuseFailAlloc_2910_, 7, v_infoState_2901_);
lean_ctor_set(v_reuseFailAlloc_2910_, 8, v_snapshotTasks_2902_);
v___x_2908_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
lean_object* v___x_2909_; 
v___x_2909_ = lean_st_ref_set(v___x_2840_, v___x_2908_);
lean_inc(v___x_2840_);
lean_inc(v___x_2828_);
v_fileName_2848_ = v_fileName_2824_;
v_fileMap_2849_ = v___x_2825_;
v_currRecDepth_2850_ = v___x_2826_;
v_ref_2851_ = v___x_2827_;
v_currNamespace_2852_ = v___x_2828_;
v_openDecls_2853_ = v___x_2829_;
v_initHeartbeats_2854_ = v___x_2839_;
v_maxHeartbeats_2855_ = v___x_2830_;
v_quotContext_2856_ = v___x_2828_;
v_currMacroScope_2857_ = v___x_2831_;
v_cancelTk_x3f_2858_ = v___x_2832_;
v_suppressElabErrors_2859_ = v_run_2833_;
v_inheritedTraceOptions_2860_ = v___x_2842_;
v___y_2861_ = v___x_2840_;
goto v___jp_2847_;
}
}
}
else
{
lean_dec_ref(v___x_2823_);
lean_inc(v___x_2840_);
lean_inc(v___x_2828_);
v_fileName_2848_ = v_fileName_2824_;
v_fileMap_2849_ = v___x_2825_;
v_currRecDepth_2850_ = v___x_2826_;
v_ref_2851_ = v___x_2827_;
v_currNamespace_2852_ = v___x_2828_;
v_openDecls_2853_ = v___x_2829_;
v_initHeartbeats_2854_ = v___x_2839_;
v_maxHeartbeats_2855_ = v___x_2830_;
v_quotContext_2856_ = v___x_2828_;
v_currMacroScope_2857_ = v___x_2831_;
v_cancelTk_x3f_2858_ = v___x_2832_;
v_suppressElabErrors_2859_ = v_run_2833_;
v_inheritedTraceOptions_2860_ = v___x_2842_;
v___y_2861_ = v___x_2840_;
goto v___jp_2847_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object** _args){
lean_object* v___x_2914_ = _args[0];
lean_object* v___x_2915_ = _args[1];
lean_object* v_mainModuleName_2916_ = _args[2];
lean_object* v_a_2917_ = _args[3];
lean_object* v___x_2918_ = _args[4];
lean_object* v___x_2919_ = _args[5];
lean_object* v_fileName_2920_ = _args[6];
lean_object* v___x_2921_ = _args[7];
lean_object* v___x_2922_ = _args[8];
lean_object* v___x_2923_ = _args[9];
lean_object* v___x_2924_ = _args[10];
lean_object* v___x_2925_ = _args[11];
lean_object* v___x_2926_ = _args[12];
lean_object* v___x_2927_ = _args[13];
lean_object* v___x_2928_ = _args[14];
lean_object* v_run_2929_ = _args[15];
lean_object* v___y_2930_ = _args[16];
_start:
{
uint8_t v___x_18813__boxed_2931_; uint8_t v_run_boxed_2932_; lean_object* v_res_2933_; 
v___x_18813__boxed_2931_ = lean_unbox(v___x_2918_);
v_run_boxed_2932_ = lean_unbox(v_run_2929_);
v_res_2933_ = l___private_Lean_Shell_0__Lean_shellMain___lam__0(v___x_2914_, v___x_2915_, v_mainModuleName_2916_, v_a_2917_, v___x_18813__boxed_2931_, v___x_2919_, v_fileName_2920_, v___x_2921_, v___x_2922_, v___x_2923_, v___x_2924_, v___x_2925_, v___x_2926_, v___x_2927_, v___x_2928_, v_run_boxed_2932_);
lean_dec(v_a_2917_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(lean_object* v_val_2934_, lean_object* v_a_2935_, lean_object* v_b_2936_){
_start:
{
lean_object* v_str_2937_; lean_object* v_startInclusive_2938_; lean_object* v_endExclusive_2939_; lean_object* v___x_2940_; uint8_t v___x_2941_; 
v_str_2937_ = lean_ctor_get(v_val_2934_, 0);
v_startInclusive_2938_ = lean_ctor_get(v_val_2934_, 1);
v_endExclusive_2939_ = lean_ctor_get(v_val_2934_, 2);
v___x_2940_ = lean_nat_sub(v_endExclusive_2939_, v_startInclusive_2938_);
v___x_2941_ = lean_nat_dec_eq(v_a_2935_, v___x_2940_);
lean_dec(v___x_2940_);
if (v___x_2941_ == 0)
{
lean_object* v___x_2942_; uint32_t v___x_2943_; uint32_t v___x_2944_; uint8_t v___x_2945_; 
v___x_2942_ = lean_nat_add(v_startInclusive_2938_, v_a_2935_);
v___x_2943_ = lean_string_utf8_get_fast(v_str_2937_, v___x_2942_);
v___x_2944_ = 10;
v___x_2945_ = lean_uint32_dec_eq(v___x_2943_, v___x_2944_);
if (v___x_2945_ == 0)
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
lean_dec(v_a_2935_);
v___x_2946_ = lean_box(0);
v___x_2947_ = lean_string_utf8_next_fast(v_str_2937_, v___x_2942_);
lean_dec(v___x_2942_);
v___x_2948_ = lean_nat_sub(v___x_2947_, v_startInclusive_2938_);
v_a_2935_ = v___x_2948_;
v_b_2936_ = v___x_2946_;
goto _start;
}
else
{
lean_object* v___x_2950_; 
lean_dec(v___x_2942_);
v___x_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2950_, 0, v_a_2935_);
return v___x_2950_;
}
}
else
{
lean_dec(v_a_2935_);
lean_inc(v_b_2936_);
return v_b_2936_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg___boxed(lean_object* v_val_2951_, lean_object* v_a_2952_, lean_object* v_b_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_2951_, v_a_2952_, v_b_2953_);
lean_dec(v_b_2953_);
lean_dec_ref(v_val_2951_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(lean_object* v_s_2955_){
_start:
{
uint32_t v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2957_ = 10;
v___x_2958_ = lean_string_push(v_s_2955_, v___x_2957_);
v___x_2959_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4___boxed(lean_object* v_s_2960_, lean_object* v_a_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_s_2960_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object* v_s_2963_){
_start:
{
uint32_t v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2965_ = 10;
v___x_2966_ = lean_string_push(v_s_2963_, v___x_2965_);
v___x_2967_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___boxed(lean_object* v_s_2968_, lean_object* v_a_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v_s_2968_);
return v_res_2970_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shellMain___closed__0(void){
_start:
{
lean_object* v___x_2971_; uint8_t v___x_2972_; 
v___x_2971_ = lean_box(0);
v___x_2972_ = lean_internal_has_address_sanitizer(v___x_2971_);
return v___x_2972_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__4(void){
_start:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2977_ = l_Lean_Options_empty;
v___x_2978_ = l_Lean_Core_getMaxHeartbeats(v___x_2977_);
return v___x_2978_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__5(void){
_start:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2979_ = lean_unsigned_to_nat(1u);
v___x_2980_ = l_Lean_firstFrontendMacroScope;
v___x_2981_ = lean_nat_add(v___x_2980_, v___x_2979_);
return v___x_2981_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10(void){
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
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11(void){
_start:
{
size_t v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2995_ = ((size_t)5ULL);
v___x_2996_ = lean_unsigned_to_nat(0u);
v___x_2997_ = lean_unsigned_to_nat(32u);
v___x_2998_ = lean_mk_empty_array_with_capacity(v___x_2997_);
v___x_2999_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__10, &l___private_Lean_Shell_0__Lean_shellMain___closed__10_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10);
v___x_3000_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3000_, 0, v___x_2999_);
lean_ctor_set(v___x_3000_, 1, v___x_2998_);
lean_ctor_set(v___x_3000_, 2, v___x_2996_);
lean_ctor_set(v___x_3000_, 3, v___x_2996_);
lean_ctor_set_usize(v___x_3000_, 4, v___x_2995_);
return v___x_3000_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__12(void){
_start:
{
lean_object* v___x_3001_; uint64_t v___x_3002_; lean_object* v___x_3003_; 
v___x_3001_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__11, &l___private_Lean_Shell_0__Lean_shellMain___closed__11_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11);
v___x_3002_ = 0ULL;
v___x_3003_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3003_, 0, v___x_3001_);
lean_ctor_set_uint64(v___x_3003_, sizeof(void*)*1, v___x_3002_);
return v___x_3003_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13(void){
_start:
{
lean_object* v___x_3004_; 
v___x_3004_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3004_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14(void){
_start:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3005_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__13, &l___private_Lean_Shell_0__Lean_shellMain___closed__13_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13);
v___x_3006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3005_);
return v___x_3006_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__15(void){
_start:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3007_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__14, &l___private_Lean_Shell_0__Lean_shellMain___closed__14_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14);
v___x_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
return v___x_3008_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16(void){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3009_ = l_Lean_NameSet_empty;
v___x_3010_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__11, &l___private_Lean_Shell_0__Lean_shellMain___closed__11_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11);
v___x_3011_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
lean_ctor_set(v___x_3011_, 1, v___x_3010_);
lean_ctor_set(v___x_3011_, 2, v___x_3009_);
return v___x_3011_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__17(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; lean_object* v___x_3015_; 
v___x_3012_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__11, &l___private_Lean_Shell_0__Lean_shellMain___closed__11_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11);
v___x_3013_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__14, &l___private_Lean_Shell_0__Lean_shellMain___closed__14_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14);
v___x_3014_ = 1;
v___x_3015_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3015_, 0, v___x_3013_);
lean_ctor_set(v___x_3015_, 1, v___x_3013_);
lean_ctor_set(v___x_3015_, 2, v___x_3012_);
lean_ctor_set_uint8(v___x_3015_, sizeof(void*)*3, v___x_3014_);
return v___x_3015_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__22(void){
_start:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3021_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__21));
v___x_3022_ = lean_string_utf8_byte_size(v___x_3021_);
return v___x_3022_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__23(void){
_start:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3023_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__22, &l___private_Lean_Shell_0__Lean_shellMain___closed__22_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__22);
v___x_3024_ = lean_unsigned_to_nat(0u);
v___x_3025_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__21));
v___x_3026_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3025_);
lean_ctor_set(v___x_3026_, 1, v___x_3024_);
lean_ctor_set(v___x_3026_, 2, v___x_3023_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* lean_shell_main(lean_object* v_args_3030_, lean_object* v_opts_3031_){
_start:
{
lean_object* v___y_3040_; lean_object* v_fns_3055_; lean_object* v_leanOpts_3074_; lean_object* v_forwardedArgs_3075_; uint8_t v_component_3076_; uint8_t v_printPrefix_3077_; uint8_t v_printLibDir_3078_; uint8_t v_useStdin_3079_; uint8_t v_onlyDeps_3080_; uint8_t v_onlySrcDeps_3081_; uint8_t v_depsJson_3082_; uint32_t v_trustLevel_3083_; lean_object* v_rootDir_x3f_3084_; lean_object* v_setupFileName_x3f_3085_; lean_object* v_oleanFileName_x3f_3086_; lean_object* v_ileanFileName_x3f_3087_; lean_object* v_cFileName_x3f_3088_; lean_object* v_bcFileName_x3f_3089_; uint8_t v_jsonOutput_3090_; lean_object* v_errorOnKinds_3091_; uint8_t v_printStats_3092_; uint8_t v_run_3093_; lean_object* v_incrSaveFileName_x3f_3094_; lean_object* v_incrLoadFileName_x3f_3095_; lean_object* v_incrHeaderSaveFileName_x3f_3096_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; 
v_leanOpts_3074_ = lean_ctor_get(v_opts_3031_, 0);
lean_inc_ref(v_leanOpts_3074_);
v_forwardedArgs_3075_ = lean_ctor_get(v_opts_3031_, 1);
lean_inc_ref(v_forwardedArgs_3075_);
v_component_3076_ = lean_ctor_get_uint8(v_opts_3031_, sizeof(void*)*13 + 8);
v_printPrefix_3077_ = lean_ctor_get_uint8(v_opts_3031_, sizeof(void*)*13 + 9);
v_printLibDir_3078_ = lean_ctor_get_uint8(v_opts_3031_, sizeof(void*)*13 + 10);
v_useStdin_3079_ = lean_ctor_get_uint8(v_opts_3031_, sizeof(void*)*13 + 11);
v_onlyDeps_3080_ = lean_ctor_get_uint8(v_opts_3031_, sizeof(void*)*13 + 12);
v_onlySrcDeps_3081_ = lean_ctor_get_uint8(v_opts_3031_, sizeof(void*)*13 + 13);
v_depsJson_3082_ = lean_ctor_get_uint8(v_opts_3031_, sizeof(void*)*13 + 14);
v_trustLevel_3083_ = lean_ctor_get_uint32(v_opts_3031_, sizeof(void*)*13);
v_rootDir_x3f_3084_ = lean_ctor_get(v_opts_3031_, 3);
lean_inc(v_rootDir_x3f_3084_);
v_setupFileName_x3f_3085_ = lean_ctor_get(v_opts_3031_, 4);
lean_inc(v_setupFileName_x3f_3085_);
v_oleanFileName_x3f_3086_ = lean_ctor_get(v_opts_3031_, 5);
lean_inc(v_oleanFileName_x3f_3086_);
v_ileanFileName_x3f_3087_ = lean_ctor_get(v_opts_3031_, 6);
lean_inc(v_ileanFileName_x3f_3087_);
v_cFileName_x3f_3088_ = lean_ctor_get(v_opts_3031_, 7);
lean_inc(v_cFileName_x3f_3088_);
v_bcFileName_x3f_3089_ = lean_ctor_get(v_opts_3031_, 8);
lean_inc(v_bcFileName_x3f_3089_);
v_jsonOutput_3090_ = lean_ctor_get_uint8(v_opts_3031_, sizeof(void*)*13 + 15);
v_errorOnKinds_3091_ = lean_ctor_get(v_opts_3031_, 9);
lean_inc_ref(v_errorOnKinds_3091_);
v_printStats_3092_ = lean_ctor_get_uint8(v_opts_3031_, sizeof(void*)*13 + 16);
v_run_3093_ = lean_ctor_get_uint8(v_opts_3031_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_3094_ = lean_ctor_get(v_opts_3031_, 10);
lean_inc(v_incrSaveFileName_x3f_3094_);
v_incrLoadFileName_x3f_3095_ = lean_ctor_get(v_opts_3031_, 11);
lean_inc(v_incrLoadFileName_x3f_3095_);
v_incrHeaderSaveFileName_x3f_3096_ = lean_ctor_get(v_opts_3031_, 12);
lean_inc(v_incrHeaderSaveFileName_x3f_3096_);
lean_dec_ref(v_opts_3031_);
if (v_printPrefix_3077_ == 0)
{
if (v_printLibDir_3078_ == 0)
{
uint8_t v___x_3123_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v_mainModuleName_3130_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v_contents_3231_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v_str_3260_; lean_object* v_startInclusive_3261_; lean_object* v_endExclusive_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v_fileName_3363_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3401_; lean_object* v___y_3402_; uint8_t v___y_3433_; lean_object* v_fst_3434_; lean_object* v_snd_3435_; uint8_t v___y_3437_; lean_object* v___x_3467_; lean_object* v_maxMemory_3468_; lean_object* v___x_3469_; uint8_t v___x_3470_; 
v___x_3123_ = 1;
v___x_3467_ = l___private_Lean_Shell_0__Lean_maxMemory;
v_maxMemory_3468_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_leanOpts_3074_, v___x_3467_);
v___x_3469_ = lean_unsigned_to_nat(0u);
v___x_3470_ = lean_nat_dec_eq(v_maxMemory_3468_, v___x_3469_);
if (v___x_3470_ == 0)
{
size_t v___x_3471_; size_t v___x_3472_; size_t v___x_3473_; size_t v___x_3474_; lean_object* v___x_3475_; 
v___x_3471_ = lean_usize_of_nat(v_maxMemory_3468_);
lean_dec(v_maxMemory_3468_);
v___x_3472_ = ((size_t)10ULL);
v___x_3473_ = lean_usize_shift_left(v___x_3471_, v___x_3472_);
v___x_3474_ = lean_usize_shift_left(v___x_3473_, v___x_3472_);
v___x_3475_ = lean_internal_set_max_memory(v___x_3474_);
goto v___jp_3458_;
}
else
{
lean_dec(v_maxMemory_3468_);
goto v___jp_3458_;
}
v___jp_3124_:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3131_ = lean_unsigned_to_nat(0u);
v___x_3132_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__2));
lean_inc(v_mainModuleName_3130_);
lean_inc_ref(v_leanOpts_3074_);
v___x_3133_ = l_Lean_Elab_runFrontend(v___y_3129_, v_leanOpts_3074_, v___y_3128_, v_mainModuleName_3130_, v_trustLevel_3083_, v_oleanFileName_x3f_3086_, v_ileanFileName_x3f_3087_, v_jsonOutput_3090_, v_errorOnKinds_3091_, v___x_3132_, v_printStats_3092_, v___y_3126_, v_incrSaveFileName_x3f_3094_, v_incrLoadFileName_x3f_3095_, v_incrHeaderSaveFileName_x3f_3096_);
lean_dec_ref(v_errorOnKinds_3091_);
lean_dec(v_ileanFileName_x3f_3087_);
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3201_; 
v_a_3134_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3136_ = v___x_3133_;
v_isShared_3137_ = v_isSharedCheck_3201_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3133_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3201_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
if (lean_obj_tag(v_a_3134_) == 1)
{
if (v_run_3093_ == 0)
{
lean_del_object(v___x_3136_);
lean_dec(v___y_3127_);
if (lean_obj_tag(v_cFileName_x3f_3088_) == 1)
{
lean_object* v_val_3138_; lean_object* v_val_3139_; uint8_t v___x_3140_; lean_object* v___x_3141_; 
v_val_3138_ = lean_ctor_get(v_a_3134_, 0);
lean_inc(v_val_3138_);
v_val_3139_ = lean_ctor_get(v_cFileName_x3f_3088_, 0);
lean_inc(v_val_3139_);
lean_dec_ref_known(v_cFileName_x3f_3088_, 1);
v___x_3140_ = 1;
v___x_3141_ = lean_io_prim_handle_mk(v_val_3139_, v___x_3140_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___f_3162_; lean_object* v___x_3163_; 
lean_dec(v_val_3139_);
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_a_3142_);
lean_dec_ref_known(v___x_3141_, 1);
v___x_3143_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__3));
v___x_3144_ = l_Lean_instInhabitedFileMap_default;
v___x_3145_ = l_Lean_Options_empty;
v___x_3146_ = lean_box(0);
v___x_3147_ = lean_box(0);
v___x_3148_ = lean_box(0);
v___x_3149_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__4, &l___private_Lean_Shell_0__Lean_shellMain___closed__4_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__4);
v___x_3150_ = l_Lean_firstFrontendMacroScope;
v___x_3151_ = lean_box(0);
v___x_3152_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__5, &l___private_Lean_Shell_0__Lean_shellMain___closed__5_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__5);
v___x_3153_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__8));
v___x_3154_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__9));
v___x_3155_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__12, &l___private_Lean_Shell_0__Lean_shellMain___closed__12_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__12);
v___x_3156_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__15, &l___private_Lean_Shell_0__Lean_shellMain___closed__15_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__15);
v___x_3157_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__16, &l___private_Lean_Shell_0__Lean_shellMain___closed__16_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16);
v___x_3158_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__17, &l___private_Lean_Shell_0__Lean_shellMain___closed__17_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__17);
lean_inc(v_val_3138_);
v___x_3159_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3159_, 0, v_val_3138_);
lean_ctor_set(v___x_3159_, 1, v___x_3152_);
lean_ctor_set(v___x_3159_, 2, v___x_3153_);
lean_ctor_set(v___x_3159_, 3, v___x_3154_);
lean_ctor_set(v___x_3159_, 4, v___x_3155_);
lean_ctor_set(v___x_3159_, 5, v___x_3156_);
lean_ctor_set(v___x_3159_, 6, v___x_3157_);
lean_ctor_set(v___x_3159_, 7, v___x_3158_);
lean_ctor_set(v___x_3159_, 8, v___x_3132_);
v___x_3160_ = lean_box(v___x_3123_);
v___x_3161_ = lean_box(v_run_3093_);
lean_inc(v_mainModuleName_3130_);
v___f_3162_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed), 17, 16);
lean_closure_set(v___f_3162_, 0, v___x_3159_);
lean_closure_set(v___f_3162_, 1, v___x_3145_);
lean_closure_set(v___f_3162_, 2, v_mainModuleName_3130_);
lean_closure_set(v___f_3162_, 3, v_a_3142_);
lean_closure_set(v___f_3162_, 4, v___x_3160_);
lean_closure_set(v___f_3162_, 5, v___x_3156_);
lean_closure_set(v___f_3162_, 6, v___y_3125_);
lean_closure_set(v___f_3162_, 7, v___x_3144_);
lean_closure_set(v___f_3162_, 8, v___x_3131_);
lean_closure_set(v___f_3162_, 9, v___x_3146_);
lean_closure_set(v___f_3162_, 10, v___x_3147_);
lean_closure_set(v___f_3162_, 11, v___x_3148_);
lean_closure_set(v___f_3162_, 12, v___x_3149_);
lean_closure_set(v___f_3162_, 13, v___x_3150_);
lean_closure_set(v___f_3162_, 14, v___x_3151_);
lean_closure_set(v___f_3162_, 15, v___x_3161_);
v___x_3163_ = l_Lean_profileitIOUnsafe___redArg(v___x_3143_, v_leanOpts_3074_, v___f_3162_, v___x_3147_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_dec_ref_known(v___x_3163_, 1);
v___y_3098_ = v_mainModuleName_3130_;
v___y_3099_ = v_val_3138_;
v___y_3100_ = v_a_3134_;
goto v___jp_3097_;
}
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
lean_dec(v_val_3138_);
lean_dec_ref_known(v_a_3134_, 1);
lean_dec(v_mainModuleName_3130_);
lean_dec(v_bcFileName_x3f_3089_);
lean_dec_ref(v_leanOpts_3074_);
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3163_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3163_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
else
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
lean_dec_ref_known(v___x_3141_, 1);
lean_dec(v_val_3138_);
lean_dec_ref_known(v_a_3134_, 1);
lean_dec(v_mainModuleName_3130_);
lean_dec_ref(v___y_3125_);
lean_dec(v_bcFileName_x3f_3089_);
lean_dec_ref(v_leanOpts_3074_);
v___x_3172_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__18));
v___x_3173_ = lean_string_append(v___x_3172_, v_val_3139_);
lean_dec(v_val_3139_);
v___x_3174_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__1));
v___x_3175_ = lean_string_append(v___x_3173_, v___x_3174_);
v___x_3176_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3175_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3184_; 
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3184_ == 0)
{
lean_object* v_unused_3185_; 
v_unused_3185_ = lean_ctor_get(v___x_3176_, 0);
lean_dec(v_unused_3185_);
v___x_3178_ = v___x_3176_;
v_isShared_3179_ = v_isSharedCheck_3184_;
goto v_resetjp_3177_;
}
else
{
lean_dec(v___x_3176_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3184_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3180_; lean_object* v___x_3182_; 
v___x_3180_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 0, v___x_3180_);
v___x_3182_ = v___x_3178_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3180_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
else
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3193_; 
v_a_3186_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3188_ = v___x_3176_;
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3176_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3191_; 
if (v_isShared_3189_ == 0)
{
v___x_3191_ = v___x_3188_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3186_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
}
else
{
lean_object* v_val_3194_; 
lean_dec_ref(v___y_3125_);
lean_dec(v_cFileName_x3f_3088_);
v_val_3194_ = lean_ctor_get(v_a_3134_, 0);
lean_inc(v_val_3194_);
v___y_3098_ = v_mainModuleName_3130_;
v___y_3099_ = v_val_3194_;
v___y_3100_ = v_a_3134_;
goto v___jp_3097_;
}
}
else
{
lean_object* v_val_3195_; uint32_t v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3199_; 
lean_dec(v_mainModuleName_3130_);
lean_dec_ref(v___y_3125_);
lean_dec(v_bcFileName_x3f_3089_);
lean_dec(v_cFileName_x3f_3088_);
v_val_3195_ = lean_ctor_get(v_a_3134_, 0);
lean_inc(v_val_3195_);
lean_dec_ref_known(v_a_3134_, 1);
v___x_3196_ = lean_eval_main(v_val_3195_, v_leanOpts_3074_, v___y_3127_);
lean_dec(v___y_3127_);
lean_dec_ref(v_leanOpts_3074_);
lean_dec(v_val_3195_);
v___x_3197_ = lean_box_uint32(v___x_3196_);
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 0, v___x_3197_);
v___x_3199_ = v___x_3136_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3197_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
else
{
lean_del_object(v___x_3136_);
lean_dec(v_mainModuleName_3130_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3125_);
lean_dec(v_bcFileName_x3f_3089_);
lean_dec(v_cFileName_x3f_3088_);
lean_dec_ref(v_leanOpts_3074_);
v___y_3040_ = v_a_3134_;
goto v___jp_3039_;
}
}
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec(v_mainModuleName_3130_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3125_);
lean_dec(v_bcFileName_x3f_3089_);
lean_dec(v_cFileName_x3f_3088_);
lean_dec_ref(v_leanOpts_3074_);
v_a_3202_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3133_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3133_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
v___jp_3210_:
{
if (lean_obj_tag(v___y_3216_) == 0)
{
lean_object* v_a_3217_; 
v_a_3217_ = lean_ctor_get(v___y_3216_, 0);
lean_inc(v_a_3217_);
lean_dec_ref_known(v___y_3216_, 1);
v___y_3125_ = v___y_3211_;
v___y_3126_ = v___y_3212_;
v___y_3127_ = v___y_3213_;
v___y_3128_ = v___y_3214_;
v___y_3129_ = v___y_3215_;
v_mainModuleName_3130_ = v_a_3217_;
goto v___jp_3124_;
}
else
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
lean_dec_ref(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v_incrHeaderSaveFileName_x3f_3096_);
lean_dec(v_incrLoadFileName_x3f_3095_);
lean_dec(v_incrSaveFileName_x3f_3094_);
lean_dec_ref(v_errorOnKinds_3091_);
lean_dec(v_bcFileName_x3f_3089_);
lean_dec(v_cFileName_x3f_3088_);
lean_dec(v_ileanFileName_x3f_3087_);
lean_dec(v_oleanFileName_x3f_3086_);
lean_dec_ref(v_leanOpts_3074_);
v_a_3218_ = lean_ctor_get(v___y_3216_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___y_3216_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___y_3216_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___y_3216_);
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
v___jp_3226_:
{
if (lean_obj_tag(v_setupFileName_x3f_3085_) == 0)
{
lean_object* v___x_3232_; 
v___x_3232_ = lean_box(0);
if (lean_obj_tag(v___y_3229_) == 1)
{
lean_object* v_val_3233_; lean_object* v___x_3234_; 
v_val_3233_ = lean_ctor_get(v___y_3229_, 0);
lean_inc(v_val_3233_);
lean_dec_ref_known(v___y_3229_, 1);
v___x_3234_ = l_Lean_moduleNameOfFileName(v_val_3233_, v_rootDir_x3f_3084_);
if (lean_obj_tag(v___x_3234_) == 0)
{
v___y_3211_ = v___y_3227_;
v___y_3212_ = v___x_3232_;
v___y_3213_ = v___y_3228_;
v___y_3214_ = v___y_3230_;
v___y_3215_ = v_contents_3231_;
v___y_3216_ = v___x_3234_;
goto v___jp_3210_;
}
else
{
if (lean_obj_tag(v_oleanFileName_x3f_3086_) == 0)
{
if (lean_obj_tag(v_cFileName_x3f_3088_) == 0)
{
lean_object* v___x_3235_; 
lean_dec_ref_known(v___x_3234_, 1);
v___x_3235_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__20));
v___y_3125_ = v___y_3227_;
v___y_3126_ = v___x_3232_;
v___y_3127_ = v___y_3228_;
v___y_3128_ = v___y_3230_;
v___y_3129_ = v_contents_3231_;
v_mainModuleName_3130_ = v___x_3235_;
goto v___jp_3124_;
}
else
{
v___y_3211_ = v___y_3227_;
v___y_3212_ = v___x_3232_;
v___y_3213_ = v___y_3228_;
v___y_3214_ = v___y_3230_;
v___y_3215_ = v_contents_3231_;
v___y_3216_ = v___x_3234_;
goto v___jp_3210_;
}
}
else
{
v___y_3211_ = v___y_3227_;
v___y_3212_ = v___x_3232_;
v___y_3213_ = v___y_3228_;
v___y_3214_ = v___y_3230_;
v___y_3215_ = v_contents_3231_;
v___y_3216_ = v___x_3234_;
goto v___jp_3210_;
}
}
}
else
{
lean_object* v___x_3236_; 
lean_dec(v___y_3229_);
lean_dec(v_rootDir_x3f_3084_);
v___x_3236_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__20));
v___y_3125_ = v___y_3227_;
v___y_3126_ = v___x_3232_;
v___y_3127_ = v___y_3228_;
v___y_3128_ = v___y_3230_;
v___y_3129_ = v_contents_3231_;
v_mainModuleName_3130_ = v___x_3236_;
goto v___jp_3124_;
}
}
else
{
lean_object* v_val_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3255_; 
lean_dec(v___y_3229_);
lean_dec(v_rootDir_x3f_3084_);
v_val_3237_ = lean_ctor_get(v_setupFileName_x3f_3085_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v_setupFileName_x3f_3085_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3239_ = v_setupFileName_x3f_3085_;
v_isShared_3240_ = v_isSharedCheck_3255_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_val_3237_);
lean_dec(v_setupFileName_x3f_3085_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3255_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3241_; 
v___x_3241_ = l_Lean_ModuleSetup_load(v_val_3237_);
lean_dec(v_val_3237_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; lean_object* v_name_3243_; lean_object* v___x_3245_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_a_3242_);
lean_dec_ref_known(v___x_3241_, 1);
v_name_3243_ = lean_ctor_get(v_a_3242_, 0);
lean_inc(v_name_3243_);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 0, v_a_3242_);
v___x_3245_ = v___x_3239_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3242_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
v___y_3125_ = v___y_3227_;
v___y_3126_ = v___x_3245_;
v___y_3127_ = v___y_3228_;
v___y_3128_ = v___y_3230_;
v___y_3129_ = v_contents_3231_;
v_mainModuleName_3130_ = v_name_3243_;
goto v___jp_3124_;
}
}
else
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3254_; 
lean_del_object(v___x_3239_);
lean_dec_ref(v_contents_3231_);
lean_dec_ref(v___y_3230_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec(v_incrHeaderSaveFileName_x3f_3096_);
lean_dec(v_incrLoadFileName_x3f_3095_);
lean_dec(v_incrSaveFileName_x3f_3094_);
lean_dec_ref(v_errorOnKinds_3091_);
lean_dec(v_bcFileName_x3f_3089_);
lean_dec(v_cFileName_x3f_3088_);
lean_dec(v_ileanFileName_x3f_3087_);
lean_dec(v_oleanFileName_x3f_3086_);
lean_dec_ref(v_leanOpts_3074_);
v_a_3247_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3249_ = v___x_3241_;
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3241_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3252_; 
if (v_isShared_3250_ == 0)
{
v___x_3252_ = v___x_3249_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3247_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
}
}
}
v___jp_3256_:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; uint8_t v___x_3269_; 
v___x_3265_ = lean_nat_add(v_startInclusive_3261_, v___y_3264_);
lean_dec(v___y_3264_);
lean_inc(v___x_3265_);
lean_inc_ref(v_str_3260_);
v___x_3266_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3266_, 0, v_str_3260_);
lean_ctor_set(v___x_3266_, 1, v_startInclusive_3261_);
lean_ctor_set(v___x_3266_, 2, v___x_3265_);
v___x_3267_ = l_String_Slice_trimAscii(v___x_3266_);
v___x_3268_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__23, &l___private_Lean_Shell_0__Lean_shellMain___closed__23_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__23);
v___x_3269_ = l_String_Slice_beq(v___x_3267_, v___x_3268_);
if (v___x_3269_ == 0)
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
lean_dec(v___x_3265_);
lean_dec_ref(v___y_3263_);
lean_dec(v_endExclusive_3262_);
lean_dec_ref(v_str_3260_);
lean_dec(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec(v_incrHeaderSaveFileName_x3f_3096_);
lean_dec(v_incrLoadFileName_x3f_3095_);
lean_dec(v_incrSaveFileName_x3f_3094_);
lean_dec_ref(v_errorOnKinds_3091_);
lean_dec(v_bcFileName_x3f_3089_);
lean_dec(v_cFileName_x3f_3088_);
lean_dec(v_ileanFileName_x3f_3087_);
lean_dec(v_oleanFileName_x3f_3086_);
lean_dec(v_setupFileName_x3f_3085_);
lean_dec(v_rootDir_x3f_3084_);
lean_dec_ref(v_leanOpts_3074_);
v___x_3270_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__24));
v___x_3271_ = l_String_Slice_toString(v___x_3267_);
lean_dec_ref(v___x_3267_);
v___x_3272_ = lean_string_append(v___x_3270_, v___x_3271_);
lean_dec_ref(v___x_3271_);
v___x_3273_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
v___x_3274_ = lean_string_append(v___x_3272_, v___x_3273_);
v___x_3275_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3274_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3283_; 
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3283_ == 0)
{
lean_object* v_unused_3284_; 
v_unused_3284_ = lean_ctor_get(v___x_3275_, 0);
lean_dec(v_unused_3284_);
v___x_3277_ = v___x_3275_;
v_isShared_3278_ = v_isSharedCheck_3283_;
goto v_resetjp_3276_;
}
else
{
lean_dec(v___x_3275_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3283_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3279_; lean_object* v___x_3281_; 
v___x_3279_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 0, v___x_3279_);
v___x_3281_ = v___x_3277_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v___x_3279_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
v_a_3285_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3275_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3275_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
else
{
lean_object* v___x_3293_; 
lean_dec_ref(v___x_3267_);
v___x_3293_ = lean_string_utf8_extract(v_str_3260_, v___x_3265_, v_endExclusive_3262_);
lean_dec(v_endExclusive_3262_);
lean_dec(v___x_3265_);
lean_dec_ref(v_str_3260_);
v___y_3227_ = v___y_3257_;
v___y_3228_ = v___y_3258_;
v___y_3229_ = v___y_3259_;
v___y_3230_ = v___y_3263_;
v_contents_3231_ = v___x_3293_;
goto v___jp_3226_;
}
}
v___jp_3294_:
{
if (lean_obj_tag(v___y_3298_) == 0)
{
lean_object* v_a_3299_; lean_object* v___x_3300_; 
v_a_3299_ = lean_ctor_get(v___y_3298_, 0);
lean_inc(v_a_3299_);
lean_dec_ref_known(v___y_3298_, 1);
v___x_3300_ = lean_decode_lossy_utf8(v_a_3299_);
lean_dec(v_a_3299_);
if (v_onlyDeps_3080_ == 0)
{
if (v_onlySrcDeps_3081_ == 0)
{
lean_object* v___x_3301_; 
lean_inc_ref(v___x_3300_);
v___x_3301_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v___x_3300_);
if (lean_obj_tag(v___x_3301_) == 1)
{
lean_object* v_val_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
lean_dec_ref(v___x_3300_);
v_val_3302_ = lean_ctor_get(v___x_3301_, 0);
lean_inc(v_val_3302_);
lean_dec_ref_known(v___x_3301_, 1);
v___x_3303_ = lean_unsigned_to_nat(0u);
v___x_3304_ = lean_box(0);
v___x_3305_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3302_, v___x_3303_, v___x_3304_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_str_3306_; lean_object* v_startInclusive_3307_; lean_object* v_endExclusive_3308_; lean_object* v___x_3309_; 
v_str_3306_ = lean_ctor_get(v_val_3302_, 0);
lean_inc_ref(v_str_3306_);
v_startInclusive_3307_ = lean_ctor_get(v_val_3302_, 1);
lean_inc(v_startInclusive_3307_);
v_endExclusive_3308_ = lean_ctor_get(v_val_3302_, 2);
lean_inc(v_endExclusive_3308_);
lean_dec(v_val_3302_);
v___x_3309_ = lean_nat_sub(v_endExclusive_3308_, v_startInclusive_3307_);
lean_inc_ref(v___y_3297_);
v___y_3257_ = v___y_3297_;
v___y_3258_ = v___y_3295_;
v___y_3259_ = v___y_3296_;
v_str_3260_ = v_str_3306_;
v_startInclusive_3261_ = v_startInclusive_3307_;
v_endExclusive_3262_ = v_endExclusive_3308_;
v___y_3263_ = v___y_3297_;
v___y_3264_ = v___x_3309_;
goto v___jp_3256_;
}
else
{
lean_object* v_val_3310_; lean_object* v_str_3311_; lean_object* v_startInclusive_3312_; lean_object* v_endExclusive_3313_; 
v_val_3310_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_val_3310_);
lean_dec_ref_known(v___x_3305_, 1);
v_str_3311_ = lean_ctor_get(v_val_3302_, 0);
lean_inc_ref(v_str_3311_);
v_startInclusive_3312_ = lean_ctor_get(v_val_3302_, 1);
lean_inc(v_startInclusive_3312_);
v_endExclusive_3313_ = lean_ctor_get(v_val_3302_, 2);
lean_inc(v_endExclusive_3313_);
lean_dec(v_val_3302_);
lean_inc_ref(v___y_3297_);
v___y_3257_ = v___y_3297_;
v___y_3258_ = v___y_3295_;
v___y_3259_ = v___y_3296_;
v_str_3260_ = v_str_3311_;
v_startInclusive_3261_ = v_startInclusive_3312_;
v_endExclusive_3262_ = v_endExclusive_3313_;
v___y_3263_ = v___y_3297_;
v___y_3264_ = v_val_3310_;
goto v___jp_3256_;
}
}
else
{
lean_dec(v___x_3301_);
lean_inc_ref(v___y_3297_);
v___y_3227_ = v___y_3297_;
v___y_3228_ = v___y_3295_;
v___y_3229_ = v___y_3296_;
v___y_3230_ = v___y_3297_;
v_contents_3231_ = v___x_3300_;
goto v___jp_3226_;
}
}
else
{
lean_object* v___x_3314_; lean_object* v___x_3315_; 
lean_dec(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec(v_incrHeaderSaveFileName_x3f_3096_);
lean_dec(v_incrLoadFileName_x3f_3095_);
lean_dec(v_incrSaveFileName_x3f_3094_);
lean_dec_ref(v_errorOnKinds_3091_);
lean_dec(v_bcFileName_x3f_3089_);
lean_dec(v_cFileName_x3f_3088_);
lean_dec(v_ileanFileName_x3f_3087_);
lean_dec(v_oleanFileName_x3f_3086_);
lean_dec(v_setupFileName_x3f_3085_);
lean_dec(v_rootDir_x3f_3084_);
lean_dec_ref(v_leanOpts_3074_);
v___x_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3314_, 0, v___y_3297_);
v___x_3315_ = l_Lean_Elab_printImportSrcs(v___x_3300_, v___x_3314_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3323_; 
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3323_ == 0)
{
lean_object* v_unused_3324_; 
v_unused_3324_ = lean_ctor_get(v___x_3315_, 0);
lean_dec(v_unused_3324_);
v___x_3317_ = v___x_3315_;
v_isShared_3318_ = v_isSharedCheck_3323_;
goto v_resetjp_3316_;
}
else
{
lean_dec(v___x_3315_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3323_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
lean_object* v___x_3319_; lean_object* v___x_3321_; 
v___x_3319_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 0, v___x_3319_);
v___x_3321_ = v___x_3317_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3319_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
else
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3332_; 
v_a_3325_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3327_ = v___x_3315_;
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3315_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3325_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
}
}
}
else
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
lean_dec(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec(v_incrHeaderSaveFileName_x3f_3096_);
lean_dec(v_incrLoadFileName_x3f_3095_);
lean_dec(v_incrSaveFileName_x3f_3094_);
lean_dec_ref(v_errorOnKinds_3091_);
lean_dec(v_bcFileName_x3f_3089_);
lean_dec(v_cFileName_x3f_3088_);
lean_dec(v_ileanFileName_x3f_3087_);
lean_dec(v_oleanFileName_x3f_3086_);
lean_dec(v_setupFileName_x3f_3085_);
lean_dec(v_rootDir_x3f_3084_);
lean_dec_ref(v_leanOpts_3074_);
v___x_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3333_, 0, v___y_3297_);
v___x_3334_ = l_Lean_Elab_printImports(v___x_3300_, v___x_3333_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3342_; 
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3342_ == 0)
{
lean_object* v_unused_3343_; 
v_unused_3343_ = lean_ctor_get(v___x_3334_, 0);
lean_dec(v_unused_3343_);
v___x_3336_ = v___x_3334_;
v_isShared_3337_ = v_isSharedCheck_3342_;
goto v_resetjp_3335_;
}
else
{
lean_dec(v___x_3334_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3342_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3338_; lean_object* v___x_3340_; 
v___x_3338_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v___x_3338_);
v___x_3340_ = v___x_3336_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3338_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
else
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3351_; 
v_a_3344_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3346_ = v___x_3334_;
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3334_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3349_; 
if (v_isShared_3347_ == 0)
{
v___x_3349_ = v___x_3346_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3344_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
}
}
else
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3359_; 
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec(v_incrHeaderSaveFileName_x3f_3096_);
lean_dec(v_incrLoadFileName_x3f_3095_);
lean_dec(v_incrSaveFileName_x3f_3094_);
lean_dec_ref(v_errorOnKinds_3091_);
lean_dec(v_bcFileName_x3f_3089_);
lean_dec(v_cFileName_x3f_3088_);
lean_dec(v_ileanFileName_x3f_3087_);
lean_dec(v_oleanFileName_x3f_3086_);
lean_dec(v_setupFileName_x3f_3085_);
lean_dec(v_rootDir_x3f_3084_);
lean_dec_ref(v_leanOpts_3074_);
v_a_3352_ = lean_ctor_get(v___y_3298_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___y_3298_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3354_ = v___y_3298_;
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___y_3298_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3357_; 
if (v_isShared_3355_ == 0)
{
v___x_3357_ = v___x_3354_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_a_3352_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
}
v___jp_3360_:
{
if (v_useStdin_3079_ == 0)
{
lean_object* v___x_3364_; 
v___x_3364_ = l_IO_FS_readBinFile(v_fileName_3363_);
v___y_3295_ = v___y_3361_;
v___y_3296_ = v___y_3362_;
v___y_3297_ = v_fileName_3363_;
v___y_3298_ = v___x_3364_;
goto v___jp_3294_;
}
else
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3365_ = lean_get_stdin();
v___x_3366_ = l_IO_FS_Stream_readBinToEnd(v___x_3365_);
v___y_3295_ = v___y_3361_;
v___y_3296_ = v___y_3362_;
v___y_3297_ = v_fileName_3363_;
v___y_3298_ = v___x_3366_;
goto v___jp_3294_;
}
}
v___jp_3367_:
{
if (lean_obj_tag(v___y_3369_) == 1)
{
lean_object* v_val_3370_; 
v_val_3370_ = lean_ctor_get(v___y_3369_, 0);
lean_inc(v_val_3370_);
v___y_3361_ = v___y_3368_;
v___y_3362_ = v___y_3369_;
v_fileName_3363_ = v_val_3370_;
goto v___jp_3360_;
}
else
{
if (v_useStdin_3079_ == 0)
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
lean_dec(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec(v_incrHeaderSaveFileName_x3f_3096_);
lean_dec(v_incrLoadFileName_x3f_3095_);
lean_dec(v_incrSaveFileName_x3f_3094_);
lean_dec_ref(v_errorOnKinds_3091_);
lean_dec(v_bcFileName_x3f_3089_);
lean_dec(v_cFileName_x3f_3088_);
lean_dec(v_ileanFileName_x3f_3087_);
lean_dec(v_oleanFileName_x3f_3086_);
lean_dec(v_setupFileName_x3f_3085_);
lean_dec(v_rootDir_x3f_3084_);
lean_dec_ref(v_leanOpts_3074_);
v___x_3371_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__25));
v___x_3372_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3371_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v___x_3373_; 
lean_dec_ref_known(v___x_3372_, 1);
v___x_3373_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_3123_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3381_; 
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3381_ == 0)
{
lean_object* v_unused_3382_; 
v_unused_3382_ = lean_ctor_get(v___x_3373_, 0);
lean_dec(v_unused_3382_);
v___x_3375_ = v___x_3373_;
v_isShared_3376_ = v_isSharedCheck_3381_;
goto v_resetjp_3374_;
}
else
{
lean_dec(v___x_3373_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3381_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3377_; lean_object* v___x_3379_; 
v___x_3377_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 0, v___x_3377_);
v___x_3379_ = v___x_3375_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3377_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
else
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3390_; 
v_a_3383_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3385_ = v___x_3373_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3373_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3388_; 
if (v_isShared_3386_ == 0)
{
v___x_3388_ = v___x_3385_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3383_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
else
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
v_a_3391_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3372_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3372_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
else
{
lean_object* v___x_3399_; 
v___x_3399_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__26));
v___y_3361_ = v___y_3368_;
v___y_3362_ = v___y_3369_;
v_fileName_3363_ = v___x_3399_;
goto v___jp_3360_;
}
}
}
v___jp_3400_:
{
uint8_t v___x_3403_; 
v___x_3403_ = l_List_isEmpty___redArg(v___y_3401_);
if (v___x_3403_ == 0)
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
lean_dec(v___y_3402_);
lean_dec(v___y_3401_);
lean_dec(v_incrHeaderSaveFileName_x3f_3096_);
lean_dec(v_incrLoadFileName_x3f_3095_);
lean_dec(v_incrSaveFileName_x3f_3094_);
lean_dec_ref(v_errorOnKinds_3091_);
lean_dec(v_bcFileName_x3f_3089_);
lean_dec(v_cFileName_x3f_3088_);
lean_dec(v_ileanFileName_x3f_3087_);
lean_dec(v_oleanFileName_x3f_3086_);
lean_dec(v_setupFileName_x3f_3085_);
lean_dec(v_rootDir_x3f_3084_);
lean_dec_ref(v_leanOpts_3074_);
v___x_3404_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__25));
v___x_3405_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3404_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v___x_3406_; 
lean_dec_ref_known(v___x_3405_, 1);
v___x_3406_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_3123_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3414_; 
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3414_ == 0)
{
lean_object* v_unused_3415_; 
v_unused_3415_ = lean_ctor_get(v___x_3406_, 0);
lean_dec(v_unused_3415_);
v___x_3408_ = v___x_3406_;
v_isShared_3409_ = v_isSharedCheck_3414_;
goto v_resetjp_3407_;
}
else
{
lean_dec(v___x_3406_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3414_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3410_; lean_object* v___x_3412_; 
v___x_3410_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 0, v___x_3410_);
v___x_3412_ = v___x_3408_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v___x_3410_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
else
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
v_a_3416_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3418_ = v___x_3406_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3406_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3416_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
v_a_3424_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3426_ = v___x_3405_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3405_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3429_; 
if (v_isShared_3427_ == 0)
{
v___x_3429_ = v___x_3426_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3424_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
else
{
v___y_3368_ = v___y_3401_;
v___y_3369_ = v___y_3402_;
goto v___jp_3367_;
}
}
v___jp_3432_:
{
if (v_run_3093_ == 0)
{
v___y_3401_ = v_snd_3435_;
v___y_3402_ = v_fst_3434_;
goto v___jp_3400_;
}
else
{
if (v___y_3433_ == 0)
{
v___y_3368_ = v_snd_3435_;
v___y_3369_ = v_fst_3434_;
goto v___jp_3367_;
}
else
{
v___y_3401_ = v_snd_3435_;
v___y_3402_ = v_fst_3434_;
goto v___jp_3400_;
}
}
}
v___jp_3436_:
{
if (lean_obj_tag(v_args_3030_) == 0)
{
lean_object* v___x_3438_; 
v___x_3438_ = lean_box(0);
v___y_3433_ = v___y_3437_;
v_fst_3434_ = v___x_3438_;
v_snd_3435_ = v_args_3030_;
goto v___jp_3432_;
}
else
{
lean_object* v_head_3439_; lean_object* v_tail_3440_; lean_object* v___x_3441_; 
v_head_3439_ = lean_ctor_get(v_args_3030_, 0);
lean_inc(v_head_3439_);
v_tail_3440_ = lean_ctor_get(v_args_3030_, 1);
lean_inc(v_tail_3440_);
lean_dec_ref_known(v_args_3030_, 2);
v___x_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3441_, 0, v_head_3439_);
v___y_3433_ = v___y_3437_;
v_fst_3434_ = v___x_3441_;
v_snd_3435_ = v_tail_3440_;
goto v___jp_3432_;
}
}
v___jp_3442_:
{
switch(v_component_3076_)
{
case 0:
{
lean_dec_ref(v_forwardedArgs_3075_);
if (v_onlyDeps_3080_ == 0)
{
v___y_3437_ = v_onlyDeps_3080_;
goto v___jp_3436_;
}
else
{
if (v_depsJson_3082_ == 0)
{
v___y_3437_ = v_depsJson_3082_;
goto v___jp_3436_;
}
else
{
lean_dec(v_incrHeaderSaveFileName_x3f_3096_);
lean_dec(v_incrLoadFileName_x3f_3095_);
lean_dec(v_incrSaveFileName_x3f_3094_);
lean_dec_ref(v_errorOnKinds_3091_);
lean_dec(v_bcFileName_x3f_3089_);
lean_dec(v_cFileName_x3f_3088_);
lean_dec(v_ileanFileName_x3f_3087_);
lean_dec(v_oleanFileName_x3f_3086_);
lean_dec(v_setupFileName_x3f_3085_);
lean_dec(v_rootDir_x3f_3084_);
lean_dec_ref(v_leanOpts_3074_);
if (v_useStdin_3079_ == 0)
{
lean_object* v___x_3443_; 
v___x_3443_ = lean_array_mk(v_args_3030_);
v_fns_3055_ = v___x_3443_;
goto v___jp_3054_;
}
else
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
lean_dec(v_args_3030_);
v___x_3444_ = lean_get_stdin();
v___x_3445_ = l_IO_FS_Stream_lines(v___x_3444_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_a_3446_);
lean_dec_ref_known(v___x_3445_, 1);
v_fns_3055_ = v_a_3446_;
goto v___jp_3054_;
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
v_a_3447_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3445_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3445_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
lean_dec(v_incrHeaderSaveFileName_x3f_3096_);
lean_dec(v_incrLoadFileName_x3f_3095_);
lean_dec(v_incrSaveFileName_x3f_3094_);
lean_dec_ref(v_errorOnKinds_3091_);
lean_dec(v_bcFileName_x3f_3089_);
lean_dec(v_cFileName_x3f_3088_);
lean_dec(v_ileanFileName_x3f_3087_);
lean_dec(v_oleanFileName_x3f_3086_);
lean_dec(v_setupFileName_x3f_3085_);
lean_dec(v_rootDir_x3f_3084_);
lean_dec_ref(v_leanOpts_3074_);
lean_dec(v_args_3030_);
v___x_3455_ = lean_array_to_list(v_forwardedArgs_3075_);
v___x_3456_ = l_Lean_Server_Watchdog_watchdogMain(v___x_3455_);
return v___x_3456_;
}
default: 
{
lean_object* v___x_3457_; 
lean_dec(v_incrHeaderSaveFileName_x3f_3096_);
lean_dec(v_incrLoadFileName_x3f_3095_);
lean_dec(v_incrSaveFileName_x3f_3094_);
lean_dec_ref(v_errorOnKinds_3091_);
lean_dec(v_bcFileName_x3f_3089_);
lean_dec(v_cFileName_x3f_3088_);
lean_dec(v_ileanFileName_x3f_3087_);
lean_dec(v_oleanFileName_x3f_3086_);
lean_dec(v_setupFileName_x3f_3085_);
lean_dec(v_rootDir_x3f_3084_);
lean_dec_ref(v_forwardedArgs_3075_);
lean_dec(v_args_3030_);
v___x_3457_ = l_Lean_Server_FileWorker_workerMain(v_leanOpts_3074_);
return v___x_3457_;
}
}
}
v___jp_3458_:
{
lean_object* v___x_3459_; lean_object* v_timeout_3460_; lean_object* v___x_3461_; uint8_t v___x_3462_; 
v___x_3459_ = l___private_Lean_Shell_0__Lean_timeout;
v_timeout_3460_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_leanOpts_3074_, v___x_3459_);
v___x_3461_ = lean_unsigned_to_nat(0u);
v___x_3462_ = lean_nat_dec_eq(v_timeout_3460_, v___x_3461_);
if (v___x_3462_ == 0)
{
size_t v___x_3463_; size_t v___x_3464_; size_t v___x_3465_; lean_object* v___x_3466_; 
v___x_3463_ = lean_usize_of_nat(v_timeout_3460_);
lean_dec(v_timeout_3460_);
v___x_3464_ = ((size_t)1000ULL);
v___x_3465_ = lean_usize_mul(v___x_3463_, v___x_3464_);
v___x_3466_ = lean_internal_set_max_heartbeat(v___x_3465_);
goto v___jp_3442_;
}
else
{
lean_dec(v_timeout_3460_);
goto v___jp_3442_;
}
}
}
else
{
lean_object* v___x_3476_; 
lean_dec(v_incrHeaderSaveFileName_x3f_3096_);
lean_dec(v_incrLoadFileName_x3f_3095_);
lean_dec(v_incrSaveFileName_x3f_3094_);
lean_dec_ref(v_errorOnKinds_3091_);
lean_dec(v_bcFileName_x3f_3089_);
lean_dec(v_cFileName_x3f_3088_);
lean_dec(v_ileanFileName_x3f_3087_);
lean_dec(v_oleanFileName_x3f_3086_);
lean_dec(v_setupFileName_x3f_3085_);
lean_dec(v_rootDir_x3f_3084_);
lean_dec_ref(v_forwardedArgs_3075_);
lean_dec_ref(v_leanOpts_3074_);
lean_dec(v_args_3030_);
v___x_3476_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v_a_3477_; lean_object* v___x_3478_; 
v_a_3477_ = lean_ctor_get(v___x_3476_, 0);
lean_inc(v_a_3477_);
lean_dec_ref_known(v___x_3476_, 1);
v___x_3478_ = l_Lean_getLibDir(v_a_3477_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v_a_3479_; lean_object* v___x_3480_; 
v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
lean_inc(v_a_3479_);
lean_dec_ref_known(v___x_3478_, 1);
v___x_3480_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3479_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3488_; 
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3488_ == 0)
{
lean_object* v_unused_3489_; 
v_unused_3489_ = lean_ctor_get(v___x_3480_, 0);
lean_dec(v_unused_3489_);
v___x_3482_ = v___x_3480_;
v_isShared_3483_ = v_isSharedCheck_3488_;
goto v_resetjp_3481_;
}
else
{
lean_dec(v___x_3480_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3488_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3484_; lean_object* v___x_3486_; 
v___x_3484_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 0, v___x_3484_);
v___x_3486_ = v___x_3482_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3484_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
else
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3497_; 
v_a_3490_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3492_ = v___x_3480_;
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3480_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3495_; 
if (v_isShared_3493_ == 0)
{
v___x_3495_ = v___x_3492_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3490_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
v_a_3498_ = lean_ctor_get(v___x_3478_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3478_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3478_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
else
{
lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3513_; 
v_a_3506_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3508_ = v___x_3476_;
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3476_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3511_; 
if (v_isShared_3509_ == 0)
{
v___x_3511_ = v___x_3508_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_a_3506_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
}
}
}
else
{
lean_object* v___x_3514_; 
lean_dec(v_incrHeaderSaveFileName_x3f_3096_);
lean_dec(v_incrLoadFileName_x3f_3095_);
lean_dec(v_incrSaveFileName_x3f_3094_);
lean_dec_ref(v_errorOnKinds_3091_);
lean_dec(v_bcFileName_x3f_3089_);
lean_dec(v_cFileName_x3f_3088_);
lean_dec(v_ileanFileName_x3f_3087_);
lean_dec(v_oleanFileName_x3f_3086_);
lean_dec(v_setupFileName_x3f_3085_);
lean_dec(v_rootDir_x3f_3084_);
lean_dec_ref(v_forwardedArgs_3075_);
lean_dec_ref(v_leanOpts_3074_);
lean_dec(v_args_3030_);
v___x_3514_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; lean_object* v___x_3516_; 
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref_known(v___x_3514_, 1);
v___x_3516_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3515_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3524_; 
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3524_ == 0)
{
lean_object* v_unused_3525_; 
v_unused_3525_ = lean_ctor_get(v___x_3516_, 0);
lean_dec(v_unused_3525_);
v___x_3518_ = v___x_3516_;
v_isShared_3519_ = v_isSharedCheck_3524_;
goto v_resetjp_3517_;
}
else
{
lean_dec(v___x_3516_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3524_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3520_; lean_object* v___x_3522_; 
v___x_3520_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 0, v___x_3520_);
v___x_3522_ = v___x_3518_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3520_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
v_a_3526_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_3516_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3516_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
else
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3541_; 
v_a_3534_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___x_3514_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3514_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
v___jp_3033_:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
return v___x_3035_;
}
v___jp_3036_:
{
uint8_t v___x_3037_; lean_object* v___x_3038_; 
v___x_3037_ = 0;
v___x_3038_ = lean_io_exit(v___x_3037_);
return v___x_3038_;
}
v___jp_3039_:
{
lean_object* v___x_3041_; uint8_t v___x_3042_; 
v___x_3041_ = lean_display_cumulative_profiling_times();
v___x_3042_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__0, &l___private_Lean_Shell_0__Lean_shellMain___closed__0_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__0);
if (v___x_3042_ == 0)
{
if (lean_obj_tag(v___y_3040_) == 0)
{
if (v___x_3042_ == 0)
{
uint8_t v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = 1;
v___x_3044_ = lean_io_exit(v___x_3043_);
return v___x_3044_;
}
else
{
goto v___jp_3036_;
}
}
else
{
lean_dec_ref_known(v___y_3040_, 1);
goto v___jp_3036_;
}
}
else
{
if (lean_obj_tag(v___y_3040_) == 0)
{
goto v___jp_3033_;
}
else
{
lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3052_; 
v_isSharedCheck_3052_ = !lean_is_exclusive(v___y_3040_);
if (v_isSharedCheck_3052_ == 0)
{
lean_object* v_unused_3053_; 
v_unused_3053_ = lean_ctor_get(v___y_3040_, 0);
lean_dec(v_unused_3053_);
v___x_3046_ = v___y_3040_;
v_isShared_3047_ = v_isSharedCheck_3052_;
goto v_resetjp_3045_;
}
else
{
lean_dec(v___y_3040_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3052_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
if (v___x_3042_ == 0)
{
lean_del_object(v___x_3046_);
goto v___jp_3033_;
}
else
{
lean_object* v___x_3048_; lean_object* v___x_3050_; 
v___x_3048_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3047_ == 0)
{
lean_ctor_set_tag(v___x_3046_, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3048_);
v___x_3050_ = v___x_3046_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3048_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
}
}
v___jp_3054_:
{
lean_object* v___x_3056_; 
v___x_3056_ = l_Lean_printImportsJson(v_fns_3055_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3064_; 
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3064_ == 0)
{
lean_object* v_unused_3065_; 
v_unused_3065_ = lean_ctor_get(v___x_3056_, 0);
lean_dec(v_unused_3065_);
v___x_3058_ = v___x_3056_;
v_isShared_3059_ = v_isSharedCheck_3064_;
goto v_resetjp_3057_;
}
else
{
lean_dec(v___x_3056_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3064_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3060_; lean_object* v___x_3062_; 
v___x_3060_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 0, v___x_3060_);
v___x_3062_ = v___x_3058_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3060_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
v_a_3066_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_3056_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3056_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
v___jp_3097_:
{
if (lean_obj_tag(v_bcFileName_x3f_3089_) == 1)
{
lean_object* v_val_3101_; lean_object* v___x_3102_; 
v_val_3101_ = lean_ctor_get(v_bcFileName_x3f_3089_, 0);
lean_inc(v_val_3101_);
lean_dec_ref_known(v_bcFileName_x3f_3089_, 1);
v___x_3102_ = lean_init_llvm();
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
lean_dec_ref_known(v___x_3102_, 1);
v___x_3103_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__1));
v___x_3104_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_emitLLVM___boxed), 4, 3);
lean_closure_set(v___x_3104_, 0, v___y_3099_);
lean_closure_set(v___x_3104_, 1, v___y_3098_);
lean_closure_set(v___x_3104_, 2, v_val_3101_);
v___x_3105_ = lean_box(0);
v___x_3106_ = l_Lean_profileitIOUnsafe___redArg(v___x_3103_, v_leanOpts_3074_, v___x_3104_, v___x_3105_);
lean_dec_ref(v_leanOpts_3074_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_dec_ref_known(v___x_3106_, 1);
v___y_3040_ = v___y_3100_;
goto v___jp_3039_;
}
else
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
lean_dec(v___y_3100_);
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3109_ = v___x_3106_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3106_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3112_; 
if (v_isShared_3110_ == 0)
{
v___x_3112_ = v___x_3109_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_a_3107_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
}
else
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3122_; 
lean_dec(v_val_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v_leanOpts_3074_);
v_a_3115_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3117_ = v___x_3102_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3102_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3115_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
else
{
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec(v_bcFileName_x3f_3089_);
lean_dec_ref(v_leanOpts_3074_);
v___y_3040_ = v___y_3100_;
goto v___jp_3039_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object* v_args_3542_, lean_object* v_opts_3543_, lean_object* v_a_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = lean_shell_main(v_args_3542_, v_opts_3543_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(lean_object* v_val_3546_, lean_object* v_inst_3547_, lean_object* v_R_3548_, lean_object* v_a_3549_, lean_object* v_b_3550_, lean_object* v_c_3551_){
_start:
{
lean_object* v___x_3552_; 
v___x_3552_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3546_, v_a_3549_, v_b_3550_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___boxed(lean_object* v_val_3553_, lean_object* v_inst_3554_, lean_object* v_R_3555_, lean_object* v_a_3556_, lean_object* v_b_3557_, lean_object* v_c_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(v_val_3553_, v_inst_3554_, v_R_3555_, v_a_3556_, v_b_3557_, v_c_3558_);
lean_dec(v_b_3557_);
lean_dec_ref(v_val_3553_);
return v_res_3559_;
}
}
lean_object* runtime_initialize_Lean_Elab_Frontend(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ParseImportsFast(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Watchdog(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_FileWorker(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_EmitC(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
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
res = runtime_initialize_Lean_Compiler_Options(builtin);
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
