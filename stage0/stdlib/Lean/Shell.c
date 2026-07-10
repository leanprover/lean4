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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_setOption(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
extern lean_object* l_Lean_version_specialDesc;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_versionStringCore;
extern uint8_t l_Lean_version_isRelease;
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
uint32_t lean_uint32_add(uint32_t, uint32_t);
extern lean_object* l_Lean_Options_empty;
lean_object* lean_io_exit(uint8_t);
lean_object* l_Lean_printImportsJson(lean_object*);
lean_object* lean_display_cumulative_profiling_times();
lean_object* l_Lean_Options_mergeBy(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_runFrontend(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
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
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shortVersionString___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Shell_0__Lean_shortVersionString___closed__5;
static const lean_string_object l___private_Lean_Shell_0__Lean_shortVersionString___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "-pre"};
static const lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__6 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shortVersionString___closed__6_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shortVersionString___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__7;
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
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__0_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Shell_0__Lean_shellMain___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__0_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Shell_0__Lean_shellMain___closed__1;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__2;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "LLVM code generation"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__3 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__3_value;
static const lean_array_object l___private_Lean_Shell_0__Lean_shellMain___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__4 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__4_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "C code generation"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__5 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__5_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__6;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__7;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__8 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__8_value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_shellMain___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__8_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__9 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__9_value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_shellMain___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__10 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__10_value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_shellMain___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__11 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__11_value;
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
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__18;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__19;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "failed to create '"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__20 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__20_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_stdin"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__21 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__21_value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_shellMain___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__21_value),LEAN_SCALAR_PTR_LITERAL(37, 142, 62, 167, 41, 238, 22, 79)}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__22 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__22_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "lean4"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__23 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__23_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__24;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__25;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unknown language '"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__26 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__26_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Expected exactly one file name"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__27 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__27_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "<stdin>"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__28 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__28_value;
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
static uint8_t _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__5(void){
_start:
{
uint8_t v___x_91_; uint8_t v___x_92_; 
v___x_91_ = l_Lean_version_isRelease;
v___x_92_ = lean_bool_not(v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__7(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__6));
v___x_95_ = l_Lean_versionStringCore;
v___x_96_ = lean_string_append(v___x_95_, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString(void){
_start:
{
uint8_t v___x_97_; 
v___x_97_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_shortVersionString___closed__1, &l___private_Lean_Shell_0__Lean_shortVersionString___closed__1_once, _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__1);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; 
v___x_98_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shortVersionString___closed__4, &l___private_Lean_Shell_0__Lean_shortVersionString___closed__4_once, _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__4);
return v___x_98_;
}
else
{
uint8_t v___x_99_; 
v___x_99_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_shortVersionString___closed__5, &l___private_Lean_Shell_0__Lean_shortVersionString___closed__5_once, _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__5);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_versionStringCore;
return v___x_100_;
}
else
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shortVersionString___closed__7, &l___private_Lean_Shell_0__Lean_shortVersionString___closed__7_once, _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__7);
return v___x_101_;
}
}
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__2(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_box(0);
v___x_105_ = lean_internal_get_build_type(v___x_104_);
return v___x_105_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__4(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_107_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_108_ = l_Lean_githash;
v___x_109_ = lean_string_dec_eq(v___x_108_, v___x_107_);
return v___x_109_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__6(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_111_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_112_ = l_System_Platform_target;
v___x_113_ = lean_string_dec_eq(v___x_112_, v___x_111_);
return v___x_113_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__7(void){
_start:
{
lean_object* v___x_114_; lean_object* v_ver_115_; lean_object* v___x_116_; 
v___x_114_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__1));
v_ver_115_ = l___private_Lean_Shell_0__Lean_shortVersionString;
v___x_116_ = lean_string_append(v_ver_115_, v___x_114_);
return v___x_116_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__8(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v_ver_119_; 
v___x_117_ = l_System_Platform_target;
v___x_118_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__7, &l___private_Lean_Shell_0__Lean_versionHeader___closed__7_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__7);
v_ver_119_ = lean_string_append(v___x_118_, v___x_117_);
return v_ver_119_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader(void){
_start:
{
lean_object* v_ver_121_; lean_object* v_ver_131_; lean_object* v_ver_137_; uint8_t v___x_138_; 
v_ver_137_ = l___private_Lean_Shell_0__Lean_shortVersionString;
v___x_138_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__6, &l___private_Lean_Shell_0__Lean_versionHeader___closed__6_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__6);
if (v___x_138_ == 0)
{
lean_object* v_ver_139_; 
v_ver_139_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__8, &l___private_Lean_Shell_0__Lean_versionHeader___closed__8_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__8);
v_ver_131_ = v_ver_139_;
goto v___jp_130_;
}
else
{
v_ver_131_ = v_ver_137_;
goto v___jp_130_;
}
v___jp_120_:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_122_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__0));
v___x_123_ = lean_string_append(v___x_122_, v_ver_121_);
lean_dec_ref(v_ver_121_);
v___x_124_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__1));
v___x_125_ = lean_string_append(v___x_123_, v___x_124_);
v___x_126_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__2, &l___private_Lean_Shell_0__Lean_versionHeader___closed__2_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__2);
v___x_127_ = lean_string_append(v___x_125_, v___x_126_);
v___x_128_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__3));
v___x_129_ = lean_string_append(v___x_127_, v___x_128_);
return v___x_129_;
}
v___jp_130_:
{
lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_132_ = l_Lean_githash;
v___x_133_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__4, &l___private_Lean_Shell_0__Lean_versionHeader___closed__4_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__4);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v_ver_136_; 
v___x_134_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__5));
lean_inc_ref(v_ver_131_);
v___x_135_ = lean_string_append(v_ver_131_, v___x_134_);
v_ver_136_ = lean_string_append(v___x_135_, v___x_132_);
v_ver_121_ = v_ver_136_;
goto v___jp_120_;
}
else
{
lean_inc_ref(v_ver_131_);
v_ver_121_ = v_ver_131_;
goto v___jp_120_;
}
}
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_featuresString___closed__0(void){
_start:
{
lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_140_ = lean_box(0);
v___x_141_ = lean_internal_has_llvm_backend(v___x_140_);
return v___x_141_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_featuresString(void){
_start:
{
uint8_t v___x_144_; 
v___x_144_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_featuresString___closed__0, &l___private_Lean_Shell_0__Lean_featuresString___closed__0_once, _init_l___private_Lean_Shell_0__Lean_featuresString___closed__0);
if (v___x_144_ == 0)
{
lean_object* v___x_145_; 
v___x_145_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_featuresString___closed__1));
return v___x_145_;
}
else
{
lean_object* v___x_146_; 
v___x_146_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_featuresString___closed__2));
return v___x_146_;
}
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__16(void){
_start:
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = lean_box(0);
v___x_164_ = lean_internal_is_debug(v___x_163_);
return v___x_164_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__40(void){
_start:
{
lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_188_ = lean_box(0);
v___x_189_ = lean_internal_is_multi_thread(v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHelp(uint8_t v_useStderr_194_){
_start:
{
lean_object* v___y_197_; lean_object* v___y_201_; lean_object* v_out_236_; 
if (v_useStderr_194_ == 0)
{
lean_object* v___x_292_; 
v___x_292_ = lean_get_stdout();
v_out_236_ = v___x_292_;
goto v___jp_235_;
}
else
{
lean_object* v___x_293_; 
v___x_293_ = lean_get_stderr();
v_out_236_ = v___x_293_;
goto v___jp_235_;
}
v___jp_196_:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__0));
v___x_199_ = l_IO_FS_Stream_putStrLn(v___y_197_, v___x_198_);
return v___x_199_;
}
v___jp_200_:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__1));
lean_inc_ref(v___y_201_);
v___x_203_ = l_IO_FS_Stream_putStrLn(v___y_201_, v___x_202_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_dec_ref_known(v___x_203_, 1);
v___x_204_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__2));
lean_inc_ref(v___y_201_);
v___x_205_ = l_IO_FS_Stream_putStrLn(v___y_201_, v___x_204_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec_ref_known(v___x_205_, 1);
v___x_206_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__3));
lean_inc_ref(v___y_201_);
v___x_207_ = l_IO_FS_Stream_putStrLn(v___y_201_, v___x_206_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; 
lean_dec_ref_known(v___x_207_, 1);
v___x_208_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__4));
lean_inc_ref(v___y_201_);
v___x_209_ = l_IO_FS_Stream_putStrLn(v___y_201_, v___x_208_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; 
lean_dec_ref_known(v___x_209_, 1);
v___x_210_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__5));
lean_inc_ref(v___y_201_);
v___x_211_ = l_IO_FS_Stream_putStrLn(v___y_201_, v___x_210_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec_ref_known(v___x_211_, 1);
v___x_212_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__6));
lean_inc_ref(v___y_201_);
v___x_213_ = l_IO_FS_Stream_putStrLn(v___y_201_, v___x_212_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec_ref_known(v___x_213_, 1);
v___x_214_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__7));
lean_inc_ref(v___y_201_);
v___x_215_ = l_IO_FS_Stream_putStrLn(v___y_201_, v___x_214_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; 
lean_dec_ref_known(v___x_215_, 1);
v___x_216_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__8));
lean_inc_ref(v___y_201_);
v___x_217_ = l_IO_FS_Stream_putStrLn(v___y_201_, v___x_216_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; 
lean_dec_ref_known(v___x_217_, 1);
v___x_218_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__9));
lean_inc_ref(v___y_201_);
v___x_219_ = l_IO_FS_Stream_putStrLn(v___y_201_, v___x_218_);
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v___x_220_; lean_object* v___x_221_; 
lean_dec_ref_known(v___x_219_, 1);
v___x_220_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__10));
lean_inc_ref(v___y_201_);
v___x_221_ = l_IO_FS_Stream_putStrLn(v___y_201_, v___x_220_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v___x_222_; lean_object* v___x_223_; 
lean_dec_ref_known(v___x_221_, 1);
v___x_222_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__11));
lean_inc_ref(v___y_201_);
v___x_223_ = l_IO_FS_Stream_putStrLn(v___y_201_, v___x_222_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; 
lean_dec_ref_known(v___x_223_, 1);
v___x_224_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__12));
lean_inc_ref(v___y_201_);
v___x_225_ = l_IO_FS_Stream_putStrLn(v___y_201_, v___x_224_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; 
lean_dec_ref_known(v___x_225_, 1);
v___x_226_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__13));
lean_inc_ref(v___y_201_);
v___x_227_ = l_IO_FS_Stream_putStrLn(v___y_201_, v___x_226_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_dec_ref_known(v___x_227_, 1);
v___x_228_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__14));
lean_inc_ref(v___y_201_);
v___x_229_ = l_IO_FS_Stream_putStrLn(v___y_201_, v___x_228_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v___x_230_; lean_object* v___x_231_; 
lean_dec_ref_known(v___x_229_, 1);
v___x_230_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__15));
lean_inc_ref(v___y_201_);
v___x_231_ = l_IO_FS_Stream_putStrLn(v___y_201_, v___x_230_);
if (lean_obj_tag(v___x_231_) == 0)
{
uint8_t v___x_232_; 
lean_dec_ref_known(v___x_231_, 1);
v___x_232_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__16, &l___private_Lean_Shell_0__Lean_displayHelp___closed__16_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__16);
if (v___x_232_ == 0)
{
v___y_197_ = v___y_201_;
goto v___jp_196_;
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__17));
lean_inc_ref(v___y_201_);
v___x_234_ = l_IO_FS_Stream_putStrLn(v___y_201_, v___x_233_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_dec_ref_known(v___x_234_, 1);
v___y_197_ = v___y_201_;
goto v___jp_196_;
}
else
{
lean_dec_ref(v___y_201_);
return v___x_234_;
}
}
}
else
{
lean_dec_ref(v___y_201_);
return v___x_231_;
}
}
else
{
lean_dec_ref(v___y_201_);
return v___x_229_;
}
}
else
{
lean_dec_ref(v___y_201_);
return v___x_227_;
}
}
else
{
lean_dec_ref(v___y_201_);
return v___x_225_;
}
}
else
{
lean_dec_ref(v___y_201_);
return v___x_223_;
}
}
else
{
lean_dec_ref(v___y_201_);
return v___x_221_;
}
}
else
{
lean_dec_ref(v___y_201_);
return v___x_219_;
}
}
else
{
lean_dec_ref(v___y_201_);
return v___x_217_;
}
}
else
{
lean_dec_ref(v___y_201_);
return v___x_215_;
}
}
else
{
lean_dec_ref(v___y_201_);
return v___x_213_;
}
}
else
{
lean_dec_ref(v___y_201_);
return v___x_211_;
}
}
else
{
lean_dec_ref(v___y_201_);
return v___x_209_;
}
}
else
{
lean_dec_ref(v___y_201_);
return v___x_207_;
}
}
else
{
lean_dec_ref(v___y_201_);
return v___x_205_;
}
}
else
{
lean_dec_ref(v___y_201_);
return v___x_203_;
}
}
v___jp_235_:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = l___private_Lean_Shell_0__Lean_versionHeader;
lean_inc_ref(v_out_236_);
v___x_238_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_237_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
lean_dec_ref_known(v___x_238_, 1);
v___x_239_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__18));
lean_inc_ref(v_out_236_);
v___x_240_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_239_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v___x_241_; lean_object* v___x_242_; 
lean_dec_ref_known(v___x_240_, 1);
v___x_241_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__19));
lean_inc_ref(v_out_236_);
v___x_242_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_241_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec_ref_known(v___x_242_, 1);
v___x_243_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__20));
lean_inc_ref(v_out_236_);
v___x_244_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_243_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v___x_245_; lean_object* v___x_246_; 
lean_dec_ref_known(v___x_244_, 1);
v___x_245_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__21));
lean_inc_ref(v_out_236_);
v___x_246_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_245_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec_ref_known(v___x_246_, 1);
v___x_247_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__22));
lean_inc_ref(v_out_236_);
v___x_248_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_247_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec_ref_known(v___x_248_, 1);
v___x_249_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__23));
lean_inc_ref(v_out_236_);
v___x_250_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_249_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec_ref_known(v___x_250_, 1);
v___x_251_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__24));
lean_inc_ref(v_out_236_);
v___x_252_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_251_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec_ref_known(v___x_252_, 1);
v___x_253_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__25));
lean_inc_ref(v_out_236_);
v___x_254_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_253_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec_ref_known(v___x_254_, 1);
v___x_255_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__26));
lean_inc_ref(v_out_236_);
v___x_256_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_255_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec_ref_known(v___x_256_, 1);
v___x_257_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__27));
lean_inc_ref(v_out_236_);
v___x_258_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_257_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec_ref_known(v___x_258_, 1);
v___x_259_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__28));
lean_inc_ref(v_out_236_);
v___x_260_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_259_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; 
lean_dec_ref_known(v___x_260_, 1);
v___x_261_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__29));
lean_inc_ref(v_out_236_);
v___x_262_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_261_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec_ref_known(v___x_262_, 1);
v___x_263_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__30));
lean_inc_ref(v_out_236_);
v___x_264_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_263_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec_ref_known(v___x_264_, 1);
v___x_265_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__31));
lean_inc_ref(v_out_236_);
v___x_266_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_265_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec_ref_known(v___x_266_, 1);
v___x_267_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__32));
lean_inc_ref(v_out_236_);
v___x_268_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_267_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; 
lean_dec_ref_known(v___x_268_, 1);
v___x_269_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__33));
lean_inc_ref(v_out_236_);
v___x_270_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_269_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec_ref_known(v___x_270_, 1);
v___x_271_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__34));
lean_inc_ref(v_out_236_);
v___x_272_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_271_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; 
lean_dec_ref_known(v___x_272_, 1);
v___x_273_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__35));
lean_inc_ref(v_out_236_);
v___x_274_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_273_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; 
lean_dec_ref_known(v___x_274_, 1);
v___x_275_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__36));
lean_inc_ref(v_out_236_);
v___x_276_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_275_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; 
lean_dec_ref_known(v___x_276_, 1);
v___x_277_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__37));
lean_inc_ref(v_out_236_);
v___x_278_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_277_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; 
lean_dec_ref_known(v___x_278_, 1);
v___x_279_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__38));
lean_inc_ref(v_out_236_);
v___x_280_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_279_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec_ref_known(v___x_280_, 1);
v___x_281_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__39));
lean_inc_ref(v_out_236_);
v___x_282_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_281_);
if (lean_obj_tag(v___x_282_) == 0)
{
uint8_t v___x_283_; 
lean_dec_ref_known(v___x_282_, 1);
v___x_283_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__40, &l___private_Lean_Shell_0__Lean_displayHelp___closed__40_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__40);
if (v___x_283_ == 0)
{
v___y_201_ = v_out_236_;
goto v___jp_200_;
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__41));
lean_inc_ref(v_out_236_);
v___x_285_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_284_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec_ref_known(v___x_285_, 1);
v___x_286_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__42));
lean_inc_ref(v_out_236_);
v___x_287_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_286_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v___x_288_; lean_object* v___x_289_; 
lean_dec_ref_known(v___x_287_, 1);
v___x_288_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__43));
lean_inc_ref(v_out_236_);
v___x_289_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_288_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; 
lean_dec_ref_known(v___x_289_, 1);
v___x_290_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__44));
lean_inc_ref(v_out_236_);
v___x_291_ = l_IO_FS_Stream_putStrLn(v_out_236_, v___x_290_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_dec_ref_known(v___x_291_, 1);
v___y_201_ = v_out_236_;
goto v___jp_200_;
}
else
{
lean_dec_ref(v_out_236_);
return v___x_291_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_289_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_287_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_285_;
}
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_282_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_280_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_278_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_276_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_274_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_272_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_270_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_268_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_266_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_264_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_262_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_260_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_258_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_256_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_254_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_252_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_250_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_248_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_246_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_244_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_242_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_240_;
}
}
else
{
lean_dec_ref(v_out_236_);
return v___x_238_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHelp___boxed(lean_object* v_useStderr_294_, lean_object* v_a_295_){
_start:
{
uint8_t v_useStderr_boxed_296_; lean_object* v_res_297_; 
v_useStderr_boxed_296_ = lean_unbox(v_useStderr_294_);
v_res_297_ = l___private_Lean_Shell_0__Lean_displayHelp(v_useStderr_boxed_296_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(uint8_t v_x_298_){
_start:
{
switch(v_x_298_)
{
case 0:
{
lean_object* v___x_299_; 
v___x_299_ = lean_unsigned_to_nat(0u);
return v___x_299_;
}
case 1:
{
lean_object* v___x_300_; 
v___x_300_ = lean_unsigned_to_nat(1u);
return v___x_300_;
}
default: 
{
lean_object* v___x_301_; 
v___x_301_ = lean_unsigned_to_nat(2u);
return v___x_301_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx___boxed(lean_object* v_x_302_){
_start:
{
uint8_t v_x_boxed_303_; lean_object* v_res_304_; 
v_x_boxed_303_ = lean_unbox(v_x_302_);
v_res_304_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(v_x_boxed_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx(uint8_t v_x_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(v_x_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx___boxed(lean_object* v_x_307_){
_start:
{
uint8_t v_x_4__boxed_308_; lean_object* v_res_309_; 
v_x_4__boxed_308_ = lean_unbox(v_x_307_);
v_res_309_ = l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx(v_x_4__boxed_308_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg(lean_object* v_k_310_){
_start:
{
lean_inc(v_k_310_);
return v_k_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg___boxed(lean_object* v_k_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg(v_k_311_);
lean_dec(v_k_311_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim(lean_object* v_motive_313_, lean_object* v_ctorIdx_314_, uint8_t v_t_315_, lean_object* v_h_316_, lean_object* v_k_317_){
_start:
{
lean_inc(v_k_317_);
return v_k_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___boxed(lean_object* v_motive_318_, lean_object* v_ctorIdx_319_, lean_object* v_t_320_, lean_object* v_h_321_, lean_object* v_k_322_){
_start:
{
uint8_t v_t_boxed_323_; lean_object* v_res_324_; 
v_t_boxed_323_ = lean_unbox(v_t_320_);
v_res_324_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim(v_motive_318_, v_ctorIdx_319_, v_t_boxed_323_, v_h_321_, v_k_322_);
lean_dec(v_k_322_);
lean_dec(v_ctorIdx_319_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg(lean_object* v_frontend_325_){
_start:
{
lean_inc(v_frontend_325_);
return v_frontend_325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg___boxed(lean_object* v_frontend_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg(v_frontend_326_);
lean_dec(v_frontend_326_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim(lean_object* v_motive_328_, uint8_t v_t_329_, lean_object* v_h_330_, lean_object* v_frontend_331_){
_start:
{
lean_inc(v_frontend_331_);
return v_frontend_331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___boxed(lean_object* v_motive_332_, lean_object* v_t_333_, lean_object* v_h_334_, lean_object* v_frontend_335_){
_start:
{
uint8_t v_t_boxed_336_; lean_object* v_res_337_; 
v_t_boxed_336_ = lean_unbox(v_t_333_);
v_res_337_ = l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim(v_motive_332_, v_t_boxed_336_, v_h_334_, v_frontend_335_);
lean_dec(v_frontend_335_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg(lean_object* v_watchdog_338_){
_start:
{
lean_inc(v_watchdog_338_);
return v_watchdog_338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg___boxed(lean_object* v_watchdog_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg(v_watchdog_339_);
lean_dec(v_watchdog_339_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim(lean_object* v_motive_341_, uint8_t v_t_342_, lean_object* v_h_343_, lean_object* v_watchdog_344_){
_start:
{
lean_inc(v_watchdog_344_);
return v_watchdog_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___boxed(lean_object* v_motive_345_, lean_object* v_t_346_, lean_object* v_h_347_, lean_object* v_watchdog_348_){
_start:
{
uint8_t v_t_boxed_349_; lean_object* v_res_350_; 
v_t_boxed_349_ = lean_unbox(v_t_346_);
v_res_350_ = l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim(v_motive_345_, v_t_boxed_349_, v_h_347_, v_watchdog_348_);
lean_dec(v_watchdog_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg(lean_object* v_worker_351_){
_start:
{
lean_inc(v_worker_351_);
return v_worker_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg___boxed(lean_object* v_worker_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg(v_worker_352_);
lean_dec(v_worker_352_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim(lean_object* v_motive_354_, uint8_t v_t_355_, lean_object* v_h_356_, lean_object* v_worker_357_){
_start:
{
lean_inc(v_worker_357_);
return v_worker_357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___boxed(lean_object* v_motive_358_, lean_object* v_t_359_, lean_object* v_h_360_, lean_object* v_worker_361_){
_start:
{
uint8_t v_t_boxed_362_; lean_object* v_res_363_; 
v_t_boxed_362_ = lean_unbox(v_t_359_);
v_res_363_ = l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim(v_motive_358_, v_t_boxed_362_, v_h_360_, v_worker_361_);
lean_dec(v_worker_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(lean_object* v_name_364_, lean_object* v_decl_365_, lean_object* v_ref_366_){
_start:
{
lean_object* v_defValue_368_; lean_object* v_descr_369_; lean_object* v_deprecation_x3f_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_defValue_368_ = lean_ctor_get(v_decl_365_, 0);
v_descr_369_ = lean_ctor_get(v_decl_365_, 1);
v_deprecation_x3f_370_ = lean_ctor_get(v_decl_365_, 2);
lean_inc(v_defValue_368_);
v___x_371_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_371_, 0, v_defValue_368_);
lean_inc(v_deprecation_x3f_370_);
lean_inc_ref(v_descr_369_);
lean_inc_n(v_name_364_, 2);
v___x_372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_372_, 0, v_name_364_);
lean_ctor_set(v___x_372_, 1, v_ref_366_);
lean_ctor_set(v___x_372_, 2, v___x_371_);
lean_ctor_set(v___x_372_, 3, v_descr_369_);
lean_ctor_set(v___x_372_, 4, v_deprecation_x3f_370_);
v___x_373_ = lean_register_option(v_name_364_, v___x_372_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_381_; 
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_381_ == 0)
{
lean_object* v_unused_382_; 
v_unused_382_ = lean_ctor_get(v___x_373_, 0);
lean_dec(v_unused_382_);
v___x_375_ = v___x_373_;
v_isShared_376_ = v_isSharedCheck_381_;
goto v_resetjp_374_;
}
else
{
lean_dec(v___x_373_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_381_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_379_; 
lean_inc(v_defValue_368_);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v_name_364_);
lean_ctor_set(v___x_377_, 1, v_defValue_368_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_377_);
v___x_379_ = v___x_375_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_dec(v_name_364_);
v_a_383_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_373_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_373_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0___boxed(lean_object* v_name_391_, lean_object* v_decl_392_, lean_object* v_ref_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v_name_391_, v_decl_392_, v_ref_393_);
lean_dec_ref(v_decl_392_);
return v_res_395_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = lean_box(0);
v___x_400_ = lean_internal_get_default_max_memory(v___x_399_);
return v___x_400_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_401_ = lean_box(0);
v___x_402_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_403_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
v___x_404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v___x_402_);
lean_ctor_set(v___x_404_, 2, v___x_401_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_428_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_));
v___x_429_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
v___x_430_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__13_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_));
v___x_431_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v___x_428_, v___x_429_, v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2____boxed(lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
return v_res_433_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_box(0);
v___x_438_ = lean_internal_get_default_max_heartbeat(v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_439_ = lean_box(0);
v___x_440_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_441_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
v___x_442_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v___x_440_);
lean_ctor_set(v___x_442_, 2, v___x_439_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_447_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_));
v___x_448_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
v___x_449_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_));
v___x_450_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v___x_447_, v___x_448_, v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2____boxed(lean_object* v_a_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_();
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(lean_object* v_name_453_, lean_object* v_decl_454_, lean_object* v_ref_455_){
_start:
{
lean_object* v_defValue_457_; lean_object* v_descr_458_; lean_object* v_deprecation_x3f_459_; lean_object* v___x_460_; uint8_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v_defValue_457_ = lean_ctor_get(v_decl_454_, 0);
v_descr_458_ = lean_ctor_get(v_decl_454_, 1);
v_deprecation_x3f_459_ = lean_ctor_get(v_decl_454_, 2);
v___x_460_ = lean_alloc_ctor(1, 0, 1);
v___x_461_ = lean_unbox(v_defValue_457_);
lean_ctor_set_uint8(v___x_460_, 0, v___x_461_);
lean_inc(v_deprecation_x3f_459_);
lean_inc_ref(v_descr_458_);
lean_inc_n(v_name_453_, 2);
v___x_462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_462_, 0, v_name_453_);
lean_ctor_set(v___x_462_, 1, v_ref_455_);
lean_ctor_set(v___x_462_, 2, v___x_460_);
lean_ctor_set(v___x_462_, 3, v_descr_458_);
lean_ctor_set(v___x_462_, 4, v_deprecation_x3f_459_);
v___x_463_ = lean_register_option(v_name_453_, v___x_462_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_471_; 
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_471_ == 0)
{
lean_object* v_unused_472_; 
v_unused_472_ = lean_ctor_get(v___x_463_, 0);
lean_dec(v_unused_472_);
v___x_465_ = v___x_463_;
v_isShared_466_ = v_isSharedCheck_471_;
goto v_resetjp_464_;
}
else
{
lean_dec(v___x_463_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_471_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v___x_469_; 
lean_inc(v_defValue_457_);
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v_name_453_);
lean_ctor_set(v___x_467_, 1, v_defValue_457_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v___x_467_);
v___x_469_ = v___x_465_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_dec(v_name_453_);
v_a_473_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_463_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_463_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0___boxed(lean_object* v_name_481_, lean_object* v_decl_482_, lean_object* v_ref_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(v_name_481_, v_decl_482_, v_ref_483_);
lean_dec_ref(v_decl_482_);
return v_res_485_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_489_ = lean_box(0);
v___x_490_ = lean_internal_get_default_verbose(v___x_489_);
return v___x_490_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_491_ = lean_box(0);
v___x_492_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_493_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_);
v___x_494_ = lean_box(v___x_493_);
v___x_495_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v___x_492_);
lean_ctor_set(v___x_495_, 2, v___x_491_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_500_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_));
v___x_501_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_);
v___x_502_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_));
v___x_503_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(v___x_500_, v___x_501_, v___x_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2____boxed(lean_object* v_a_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_();
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getOptionOverrides___boxed(lean_object* v_x_00___x40_Lean_Shell_1930944040____hygCtx___hyg_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = lean_internal_get_option_overrides(v_x_00___x40_Lean_Shell_1930944040____hygCtx___hyg_507_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getBelieverTrustLevel___boxed(lean_object* v_x_00___x40_Lean_Shell_1075205639____hygCtx___hyg_510_){
_start:
{
uint32_t v_res_511_; lean_object* v_r_512_; 
v_res_511_ = lean_internal_get_believer_trust_level(v_x_00___x40_Lean_Shell_1075205639____hygCtx___hyg_510_);
v_r_512_ = lean_box_uint32(v_res_511_);
return v_r_512_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0(void){
_start:
{
lean_object* v___x_513_; uint32_t v___x_514_; 
v___x_513_ = lean_box(0);
v___x_514_ = lean_internal_get_believer_trust_level(v___x_513_);
return v___x_514_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1(void){
_start:
{
uint32_t v___x_515_; uint32_t v___x_516_; uint32_t v___x_517_; 
v___x_515_ = 1;
v___x_516_ = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0, &l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0_once, _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0);
v___x_517_ = lean_uint32_add(v___x_516_, v___x_515_);
return v___x_517_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel(void){
_start:
{
uint32_t v___x_518_; 
v___x_518_ = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1, &l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1_once, _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1);
return v___x_518_;
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
v___x_521_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__40, &l___private_Lean_Shell_0__Lean_displayHelp___closed__40_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__40);
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
static lean_object* _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1(void){
_start:
{
lean_object* v___x_526_; uint32_t v___x_527_; uint32_t v___x_528_; uint8_t v___x_529_; uint8_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_526_ = lean_box(0);
v___x_527_ = l___private_Lean_Shell_0__Lean_defaultNumThreads;
v___x_528_ = l___private_Lean_Shell_0__Lean_defaultTrustLevel;
v___x_529_ = 0;
v___x_530_ = 0;
v___x_531_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0));
v___x_532_ = l_Lean_Options_empty;
v___x_533_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v___x_531_);
lean_ctor_set(v___x_533_, 2, v___x_532_);
lean_ctor_set(v___x_533_, 3, v___x_526_);
lean_ctor_set(v___x_533_, 4, v___x_526_);
lean_ctor_set(v___x_533_, 5, v___x_526_);
lean_ctor_set(v___x_533_, 6, v___x_526_);
lean_ctor_set(v___x_533_, 7, v___x_526_);
lean_ctor_set(v___x_533_, 8, v___x_526_);
lean_ctor_set(v___x_533_, 9, v___x_531_);
lean_ctor_set(v___x_533_, 10, v___x_526_);
lean_ctor_set(v___x_533_, 11, v___x_526_);
lean_ctor_set(v___x_533_, 12, v___x_526_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*13 + 8, v___x_530_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*13 + 9, v___x_529_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*13 + 10, v___x_529_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*13 + 11, v___x_529_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*13 + 12, v___x_529_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*13 + 13, v___x_529_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*13 + 14, v___x_529_);
lean_ctor_set_uint32(v___x_533_, sizeof(void*)*13, v___x_528_);
lean_ctor_set_uint32(v___x_533_, sizeof(void*)*13 + 4, v___x_527_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*13 + 15, v___x_529_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*13 + 16, v___x_529_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*13 + 17, v___x_529_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* lean_shell_options_mk(lean_object* v_x_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1, &l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1_once, _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1);
return v___x_535_;
}
}
LEAN_EXPORT uint8_t lean_shell_options_get_run(lean_object* v_opts_536_){
_start:
{
uint8_t v_run_537_; 
v_run_537_ = lean_ctor_get_uint8(v_opts_536_, sizeof(void*)*13 + 17);
lean_dec_ref(v_opts_536_);
return v_run_537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getRun___boxed(lean_object* v_opts_538_){
_start:
{
uint8_t v_res_539_; lean_object* v_r_540_; 
v_res_539_ = lean_shell_options_get_run(v_opts_538_);
v_r_540_ = lean_box(v_res_539_);
return v_r_540_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(lean_object* v_opts_541_, lean_object* v_opt_542_){
_start:
{
lean_object* v_name_543_; lean_object* v_defValue_544_; lean_object* v_map_545_; lean_object* v___x_546_; 
v_name_543_ = lean_ctor_get(v_opt_542_, 0);
v_defValue_544_ = lean_ctor_get(v_opt_542_, 1);
v_map_545_ = lean_ctor_get(v_opts_541_, 0);
v___x_546_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_545_, v_name_543_);
if (lean_obj_tag(v___x_546_) == 0)
{
uint8_t v___x_547_; 
v___x_547_ = lean_unbox(v_defValue_544_);
return v___x_547_;
}
else
{
lean_object* v_val_548_; 
v_val_548_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_val_548_);
lean_dec_ref_known(v___x_546_, 1);
if (lean_obj_tag(v_val_548_) == 1)
{
uint8_t v_v_549_; 
v_v_549_ = lean_ctor_get_uint8(v_val_548_, 0);
lean_dec_ref_known(v_val_548_, 0);
return v_v_549_;
}
else
{
uint8_t v___x_550_; 
lean_dec(v_val_548_);
v___x_550_ = lean_unbox(v_defValue_544_);
return v___x_550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0___boxed(lean_object* v_opts_551_, lean_object* v_opt_552_){
_start:
{
uint8_t v_res_553_; lean_object* v_r_554_; 
v_res_553_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v_opts_551_, v_opt_552_);
lean_dec_ref(v_opt_552_);
lean_dec_ref(v_opts_551_);
v_r_554_ = lean_box(v_res_553_);
return v_r_554_;
}
}
LEAN_EXPORT uint8_t lean_shell_options_get_profiler(lean_object* v_opts_555_){
_start:
{
lean_object* v_leanOpts_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_leanOpts_556_ = lean_ctor_get(v_opts_555_, 0);
lean_inc_ref(v_leanOpts_556_);
lean_dec_ref(v_opts_555_);
v___x_557_ = l_Lean_profiler;
v___x_558_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v_leanOpts_556_, v___x_557_);
lean_dec_ref(v_leanOpts_556_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getProfiler___boxed(lean_object* v_opts_559_){
_start:
{
uint8_t v_res_560_; lean_object* v_r_561_; 
v_res_560_ = lean_shell_options_get_profiler(v_opts_559_);
v_r_561_ = lean_box(v_res_560_);
return v_r_561_;
}
}
LEAN_EXPORT uint32_t lean_shell_options_get_num_threads(lean_object* v_opts_562_){
_start:
{
uint32_t v_numThreads_563_; 
v_numThreads_563_ = lean_ctor_get_uint32(v_opts_562_, sizeof(void*)*13 + 4);
lean_dec_ref(v_opts_562_);
return v_numThreads_563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getNumThreads___boxed(lean_object* v_opts_564_){
_start:
{
uint32_t v_res_565_; lean_object* v_r_566_; 
v_res_565_ = lean_shell_options_get_num_threads(v_opts_564_);
v_r_566_ = lean_box_uint32(v_res_565_);
return v_r_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_checkOptArg(lean_object* v_optName_569_, lean_object* v_optArg_x3f_570_){
_start:
{
if (lean_obj_tag(v_optArg_x3f_570_) == 1)
{
lean_object* v_val_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
v_val_572_ = lean_ctor_get(v_optArg_x3f_570_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v_optArg_x3f_570_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v_optArg_x3f_570_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_val_572_);
lean_dec(v_optArg_x3f_570_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
lean_ctor_set_tag(v___x_574_, 0);
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_val_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec(v_optArg_x3f_570_);
v___x_580_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__0));
v___x_581_ = lean_string_append(v___x_580_, v_optName_569_);
v___x_582_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__1));
v___x_583_ = lean_string_append(v___x_581_, v___x_582_);
v___x_584_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
v___x_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_checkOptArg___boxed(lean_object* v_optName_586_, lean_object* v_optArg_x3f_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Lean_Shell_0__Lean_checkOptArg(v_optName_586_, v_optArg_x3f_587_);
lean_dec_ref(v_optName_586_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0(lean_object* v_o_593_, lean_object* v_k_594_, lean_object* v_v_595_){
_start:
{
lean_object* v_map_596_; uint8_t v_hasTrace_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_611_; 
v_map_596_ = lean_ctor_get(v_o_593_, 0);
v_hasTrace_597_ = lean_ctor_get_uint8(v_o_593_, sizeof(void*)*1);
v_isSharedCheck_611_ = !lean_is_exclusive(v_o_593_);
if (v_isSharedCheck_611_ == 0)
{
v___x_599_ = v_o_593_;
v_isShared_600_ = v_isSharedCheck_611_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_map_596_);
lean_dec(v_o_593_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_611_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v_v_595_);
lean_inc(v_k_594_);
v___x_602_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_594_, v___x_601_, v_map_596_);
if (v_hasTrace_597_ == 0)
{
lean_object* v___x_603_; uint8_t v___x_604_; lean_object* v___x_606_; 
v___x_603_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_604_ = l_Lean_Name_isPrefixOf(v___x_603_, v_k_594_);
lean_dec(v_k_594_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_602_);
v___x_606_ = v___x_599_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_602_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_ctor_set_uint8(v___x_606_, sizeof(void*)*1, v___x_604_);
return v___x_606_;
}
}
else
{
lean_object* v___x_609_; 
lean_dec(v_k_594_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_602_);
v___x_609_ = v___x_599_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_602_);
lean_ctor_set_uint8(v_reuseFailAlloc_610_, sizeof(void*)*1, v_hasTrace_597_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(lean_object* v___x_612_, lean_object* v_arg_613_, lean_object* v_a_614_, lean_object* v_b_615_){
_start:
{
lean_object* v_startInclusive_616_; lean_object* v_endExclusive_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v_startInclusive_616_ = lean_ctor_get(v___x_612_, 1);
v_endExclusive_617_ = lean_ctor_get(v___x_612_, 2);
v___x_618_ = lean_nat_sub(v_endExclusive_617_, v_startInclusive_616_);
v___x_619_ = lean_nat_dec_eq(v_a_614_, v___x_618_);
lean_dec(v___x_618_);
if (v___x_619_ == 0)
{
uint32_t v___x_620_; uint32_t v___x_621_; uint8_t v___x_622_; 
v___x_620_ = lean_string_utf8_get_fast(v_arg_613_, v_a_614_);
v___x_621_ = 61;
v___x_622_ = lean_uint32_dec_eq(v___x_620_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_box(0);
v___x_624_ = lean_string_utf8_next_fast(v_arg_613_, v_a_614_);
lean_dec(v_a_614_);
v_a_614_ = v___x_624_;
v_b_615_ = v___x_623_;
goto _start;
}
else
{
lean_object* v___x_626_; 
v___x_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_626_, 0, v_a_614_);
return v___x_626_;
}
}
else
{
lean_dec(v_a_614_);
lean_inc(v_b_615_);
return v_b_615_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg___boxed(lean_object* v___x_627_, lean_object* v_arg_628_, lean_object* v_a_629_, lean_object* v_b_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_627_, v_arg_628_, v_a_629_, v_b_630_);
lean_dec(v_b_630_);
lean_dec_ref(v_arg_628_);
lean_dec_ref(v___x_627_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_setConfigOption(lean_object* v_opts_635_, lean_object* v_arg_636_){
_start:
{
lean_object* v___y_639_; lean_object* v_searcher_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v_searcher_670_ = lean_unsigned_to_nat(0u);
v___x_671_ = lean_string_utf8_byte_size(v_arg_636_);
lean_inc_ref(v_arg_636_);
v___x_672_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_672_, 0, v_arg_636_);
lean_ctor_set(v___x_672_, 1, v_searcher_670_);
lean_ctor_set(v___x_672_, 2, v___x_671_);
v___x_673_ = lean_box(0);
v___x_674_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_672_, v_arg_636_, v_searcher_670_, v___x_673_);
lean_dec_ref_known(v___x_672_, 3);
if (lean_obj_tag(v___x_674_) == 0)
{
v___y_639_ = v___x_671_;
goto v___jp_638_;
}
else
{
lean_object* v_val_675_; 
v_val_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_val_675_);
lean_dec_ref_known(v___x_674_, 1);
v___y_639_ = v_val_675_;
goto v___jp_638_;
}
v___jp_638_:
{
lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_640_ = lean_string_utf8_byte_size(v_arg_636_);
v___x_641_ = lean_nat_dec_eq(v___y_639_, v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_659_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_659_ == 0)
{
v___x_645_ = v___x_642_;
v_isShared_646_ = v_isSharedCheck_659_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_642_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_659_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v_name_650_; lean_object* v_val_651_; lean_object* v___x_652_; 
v___x_647_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_639_);
lean_inc_ref(v_arg_636_);
v___x_648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_648_, 0, v_arg_636_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
lean_ctor_set(v___x_648_, 2, v___y_639_);
v___x_649_ = lean_string_utf8_next_fast(v_arg_636_, v___y_639_);
lean_dec(v___y_639_);
v_name_650_ = l_String_Slice_toName(v___x_648_);
lean_dec_ref_known(v___x_648_, 3);
v_val_651_ = lean_string_utf8_extract(v_arg_636_, v___x_649_, v___x_640_);
lean_dec_ref(v_arg_636_);
v___x_652_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_643_, v_name_650_);
lean_dec(v_a_643_);
if (lean_obj_tag(v___x_652_) == 1)
{
lean_object* v_val_653_; lean_object* v___x_654_; 
lean_del_object(v___x_645_);
v_val_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_val_653_);
lean_dec_ref_known(v___x_652_, 1);
v___x_654_ = l_Lean_Language_Lean_setOption(v_opts_635_, v_val_653_, v_name_650_, v_val_651_);
return v___x_654_;
}
else
{
lean_object* v___x_655_; lean_object* v___x_657_; 
lean_dec(v___x_652_);
v___x_655_ = l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0(v_opts_635_, v_name_650_, v_val_651_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v___x_655_);
v___x_657_ = v___x_645_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
lean_dec(v___y_639_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v_opts_635_);
v_a_660_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_642_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_642_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
else
{
lean_object* v___x_668_; lean_object* v___x_669_; 
lean_dec(v___y_639_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v_opts_635_);
v___x_668_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_setConfigOption___closed__1));
v___x_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_setConfigOption___boxed(lean_object* v_opts_676_, lean_object* v_arg_677_, lean_object* v_a_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_opts_676_, v_arg_677_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(lean_object* v___x_680_, lean_object* v_arg_681_, lean_object* v_inst_682_, lean_object* v_R_683_, lean_object* v_a_684_, lean_object* v_b_685_, lean_object* v_c_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_680_, v_arg_681_, v_a_684_, v_b_685_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___boxed(lean_object* v___x_688_, lean_object* v_arg_689_, lean_object* v_inst_690_, lean_object* v_R_691_, lean_object* v_a_692_, lean_object* v_b_693_, lean_object* v_c_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(v___x_688_, v_arg_689_, v_inst_690_, v_R_691_, v_a_692_, v_b_693_, v_c_694_);
lean_dec(v_b_693_);
lean_dec_ref(v_arg_689_);
lean_dec_ref(v___x_688_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(lean_object* v_msg_697_){
_start:
{
lean_object* v___f_699_; lean_object* v___x_700_; 
v___f_699_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_700_ = l_IO_eprint___redArg(v___f_699_, v_msg_697_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
else
{
lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_716_; 
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_716_ == 0)
{
lean_object* v_unused_717_; 
v_unused_717_ = lean_ctor_get(v___x_700_, 0);
lean_dec(v_unused_717_);
v___x_710_ = v___x_700_;
v_isShared_711_ = v_isSharedCheck_716_;
goto v_resetjp_709_;
}
else
{
lean_dec(v___x_700_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_716_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_712_ = lean_box(0);
if (v_isShared_711_ == 0)
{
lean_ctor_set_tag(v___x_710_, 0);
lean_ctor_set(v___x_710_, 0, v___x_712_);
v___x_714_ = v___x_710_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___boxed(lean_object* v_msg_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(v_msg_718_);
return v_res_720_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_723_; lean_object* v___x_724_; 
v___x_723_ = 1;
v___x_724_ = lean_box_uint32(v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(lean_object* v_x_725_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = lean_apply_1(v_x_725_, lean_box(0));
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
else
{
lean_object* v_a_743_; lean_object* v___x_748_; lean_object* v___f_749_; lean_object* v___x_750_; 
v_a_743_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_743_);
lean_dec_ref_known(v___x_734_, 1);
v___x_748_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___f_749_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_750_ = l_IO_eprint___redArg(v___f_749_, v___x_748_);
lean_dec_ref(v___x_750_);
goto v___jp_744_;
v___jp_744_:
{
lean_object* v___x_745_; lean_object* v___f_746_; lean_object* v___x_747_; 
v___x_745_ = lean_io_error_to_string(v_a_743_);
v___f_746_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_747_ = l_IO_eprint___redArg(v___f_746_, v___x_745_);
lean_dec_ref(v___x_747_);
goto v___jp_730_;
}
}
v___jp_727_:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
return v___x_729_;
}
v___jp_730_:
{
lean_object* v___x_731_; lean_object* v___f_732_; lean_object* v___x_733_; 
v___x_731_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___f_732_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_733_ = l_IO_eprint___redArg(v___f_732_, v___x_731_);
lean_dec_ref(v___x_733_);
goto v___jp_727_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed(lean_object* v_x_751_, lean_object* v_a_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(v_x_751_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(lean_object* v_00_u03b1_754_, lean_object* v_x_755_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = lean_apply_1(v_x_755_, lean_box(0));
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_764_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_764_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_778_; lean_object* v___f_779_; lean_object* v___x_780_; 
v_a_773_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_773_);
lean_dec_ref_known(v___x_764_, 1);
v___x_778_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___f_779_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_780_ = l_IO_eprint___redArg(v___f_779_, v___x_778_);
lean_dec_ref(v___x_780_);
goto v___jp_774_;
v___jp_774_:
{
lean_object* v___x_775_; lean_object* v___f_776_; lean_object* v___x_777_; 
v___x_775_ = lean_io_error_to_string(v_a_773_);
v___f_776_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_777_ = l_IO_eprint___redArg(v___f_776_, v___x_775_);
lean_dec_ref(v___x_777_);
goto v___jp_760_;
}
}
v___jp_757_:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
return v___x_759_;
}
v___jp_760_:
{
lean_object* v___x_761_; lean_object* v___f_762_; lean_object* v___x_763_; 
v___x_761_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___f_762_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_763_ = l_IO_eprint___redArg(v___f_762_, v___x_761_);
lean_dec_ref(v___x_763_);
goto v___jp_757_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___boxed(lean_object* v_00_u03b1_781_, lean_object* v_x_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(v_00_u03b1_781_, v_x_782_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(lean_object* v_opt_787_){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___f_796_; lean_object* v___x_797_; 
v___x_792_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__0));
v___x_793_ = lean_string_append(v___x_792_, v_opt_787_);
v___x_794_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
v___x_795_ = lean_string_append(v___x_793_, v___x_794_);
v___f_796_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_797_ = l_IO_eprint___redArg(v___f_796_, v___x_795_);
lean_dec_ref(v___x_797_);
goto v___jp_789_;
v___jp_789_:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
return v___x_791_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___boxed(lean_object* v_opt_798_, lean_object* v_a_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(v_opt_798_);
lean_dec_ref(v_opt_798_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(lean_object* v_opt_803_){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___f_812_; lean_object* v___x_813_; 
v___x_808_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__0));
v___x_809_ = lean_string_append(v___x_808_, v_opt_803_);
v___x_810_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__1));
v___x_811_ = lean_string_append(v___x_809_, v___x_810_);
v___f_812_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_813_ = l_IO_eprint___redArg(v___f_812_, v___x_811_);
lean_dec_ref(v___x_813_);
goto v___jp_805_;
v___jp_805_:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
return v___x_807_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___boxed(lean_object* v_opt_814_, lean_object* v_a_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(v_opt_814_);
lean_dec_ref(v_opt_814_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(lean_object* v_s_817_){
_start:
{
lean_object* v___x_819_; lean_object* v_putStr_820_; lean_object* v___x_821_; 
v___x_819_ = lean_get_stderr();
v_putStr_820_ = lean_ctor_get(v___x_819_, 4);
lean_inc_ref(v_putStr_820_);
lean_dec_ref(v___x_819_);
v___x_821_ = lean_apply_2(v_putStr_820_, v_s_817_, lean_box(0));
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0___boxed(lean_object* v_s_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v_s_822_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(lean_object* v_s_825_){
_start:
{
lean_object* v___x_827_; lean_object* v_putStr_828_; lean_object* v___x_829_; 
v___x_827_ = lean_get_stdout();
v_putStr_828_ = lean_ctor_get(v___x_827_, 4);
lean_inc_ref(v_putStr_828_);
lean_dec_ref(v___x_827_);
v___x_829_ = lean_apply_2(v_putStr_828_, v_s_825_, lean_box(0));
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5___boxed(lean_object* v_s_830_, lean_object* v_a_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v_s_830_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(lean_object* v_s_833_){
_start:
{
uint32_t v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_835_ = 10;
v___x_836_ = lean_string_push(v_s_833_, v___x_835_);
v___x_837_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3___boxed(lean_object* v_s_838_, lean_object* v_a_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v_s_838_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(lean_object* v_o_841_, lean_object* v_k_842_, uint8_t v_v_843_){
_start:
{
lean_object* v_map_844_; uint8_t v_hasTrace_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_859_; 
v_map_844_ = lean_ctor_get(v_o_841_, 0);
v_hasTrace_845_ = lean_ctor_get_uint8(v_o_841_, sizeof(void*)*1);
v_isSharedCheck_859_ = !lean_is_exclusive(v_o_841_);
if (v_isSharedCheck_859_ == 0)
{
v___x_847_ = v_o_841_;
v_isShared_848_ = v_isSharedCheck_859_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_map_844_);
lean_dec(v_o_841_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_859_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_849_, 0, v_v_843_);
lean_inc(v_k_842_);
v___x_850_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_842_, v___x_849_, v_map_844_);
if (v_hasTrace_845_ == 0)
{
lean_object* v___x_851_; uint8_t v___x_852_; lean_object* v___x_854_; 
v___x_851_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_852_ = l_Lean_Name_isPrefixOf(v___x_851_, v_k_842_);
lean_dec(v_k_842_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_850_);
v___x_854_ = v___x_847_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_850_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_ctor_set_uint8(v___x_854_, sizeof(void*)*1, v___x_852_);
return v___x_854_;
}
}
else
{
lean_object* v___x_857_; 
lean_dec(v_k_842_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_850_);
v___x_857_ = v___x_847_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_850_);
lean_ctor_set_uint8(v_reuseFailAlloc_858_, sizeof(void*)*1, v_hasTrace_845_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1___boxed(lean_object* v_o_860_, lean_object* v_k_861_, lean_object* v_v_862_){
_start:
{
uint8_t v_v_boxed_863_; lean_object* v_res_864_; 
v_v_boxed_863_ = lean_unbox(v_v_862_);
v_res_864_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(v_o_860_, v_k_861_, v_v_boxed_863_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(lean_object* v_opts_865_, lean_object* v_opt_866_, uint8_t v_val_867_){
_start:
{
lean_object* v_name_868_; lean_object* v___x_869_; 
v_name_868_ = lean_ctor_get(v_opt_866_, 0);
lean_inc(v_name_868_);
lean_dec_ref(v_opt_866_);
v___x_869_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(v_opts_865_, v_name_868_, v_val_867_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1___boxed(lean_object* v_opts_870_, lean_object* v_opt_871_, lean_object* v_val_872_){
_start:
{
uint8_t v_val_boxed_873_; lean_object* v_res_874_; 
v_val_boxed_873_ = lean_unbox(v_val_872_);
v_res_874_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_opts_870_, v_opt_871_, v_val_boxed_873_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__3(lean_object* v_o_875_, lean_object* v_k_876_, lean_object* v_v_877_){
_start:
{
lean_object* v_map_878_; uint8_t v_hasTrace_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_893_; 
v_map_878_ = lean_ctor_get(v_o_875_, 0);
v_hasTrace_879_ = lean_ctor_get_uint8(v_o_875_, sizeof(void*)*1);
v_isSharedCheck_893_ = !lean_is_exclusive(v_o_875_);
if (v_isSharedCheck_893_ == 0)
{
v___x_881_ = v_o_875_;
v_isShared_882_ = v_isSharedCheck_893_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_map_878_);
lean_dec(v_o_875_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_893_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_883_, 0, v_v_877_);
lean_inc(v_k_876_);
v___x_884_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_876_, v___x_883_, v_map_878_);
if (v_hasTrace_879_ == 0)
{
lean_object* v___x_885_; uint8_t v___x_886_; lean_object* v___x_888_; 
v___x_885_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_886_ = l_Lean_Name_isPrefixOf(v___x_885_, v_k_876_);
lean_dec(v_k_876_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_884_);
v___x_888_ = v___x_881_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_884_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_ctor_set_uint8(v___x_888_, sizeof(void*)*1, v___x_886_);
return v___x_888_;
}
}
else
{
lean_object* v___x_891_; 
lean_dec(v_k_876_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_884_);
v___x_891_ = v___x_881_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_884_);
lean_ctor_set_uint8(v_reuseFailAlloc_892_, sizeof(void*)*1, v_hasTrace_879_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(lean_object* v_opts_894_, lean_object* v_opt_895_, lean_object* v_val_896_){
_start:
{
lean_object* v_name_897_; lean_object* v___x_898_; 
v_name_897_ = lean_ctor_get(v_opt_895_, 0);
lean_inc(v_name_897_);
lean_dec_ref(v_opt_895_);
v___x_898_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__3(v_opts_894_, v_name_897_, v_val_896_);
return v___x_898_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28(void){
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
lean_object* v___y_1057_; lean_object* v___y_1103_; uint32_t v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = 101;
v___x_1164_ = lean_uint32_dec_eq(v_opt_942_, v___x_1163_);
if (v___x_1164_ == 0)
{
uint32_t v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = 106;
v___x_1166_ = lean_uint32_dec_eq(v_opt_942_, v___x_1165_);
if (v___x_1166_ == 0)
{
uint32_t v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = 118;
v___x_1168_ = lean_uint32_dec_eq(v_opt_942_, v___x_1167_);
if (v___x_1168_ == 0)
{
uint32_t v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = 86;
v___x_1170_ = lean_uint32_dec_eq(v_opt_942_, v___x_1169_);
if (v___x_1170_ == 0)
{
uint32_t v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = 103;
v___x_1172_ = lean_uint32_dec_eq(v_opt_942_, v___x_1171_);
if (v___x_1172_ == 0)
{
uint32_t v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = 104;
v___x_1174_ = lean_uint32_dec_eq(v_opt_942_, v___x_1173_);
if (v___x_1174_ == 0)
{
uint32_t v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = 102;
v___x_1176_ = lean_uint32_dec_eq(v_opt_942_, v___x_1175_);
if (v___x_1176_ == 0)
{
uint32_t v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = 99;
v___x_1178_ = lean_uint32_dec_eq(v_opt_942_, v___x_1177_);
if (v___x_1178_ == 0)
{
uint32_t v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = 98;
v___x_1180_ = lean_uint32_dec_eq(v_opt_942_, v___x_1179_);
if (v___x_1180_ == 0)
{
uint32_t v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = 115;
v___x_1182_ = lean_uint32_dec_eq(v_opt_942_, v___x_1181_);
if (v___x_1182_ == 0)
{
uint32_t v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = 73;
v___x_1184_ = lean_uint32_dec_eq(v_opt_942_, v___x_1183_);
if (v___x_1184_ == 0)
{
uint32_t v___x_1185_; uint8_t v___x_1186_; 
v___x_1185_ = 114;
v___x_1186_ = lean_uint32_dec_eq(v_opt_942_, v___x_1185_);
if (v___x_1186_ == 0)
{
uint32_t v___x_1187_; uint8_t v___x_1188_; 
v___x_1187_ = 111;
v___x_1188_ = lean_uint32_dec_eq(v_opt_942_, v___x_1187_);
if (v___x_1188_ == 0)
{
uint32_t v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = 105;
v___x_1190_ = lean_uint32_dec_eq(v_opt_942_, v___x_1189_);
if (v___x_1190_ == 0)
{
uint32_t v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = 82;
v___x_1192_ = lean_uint32_dec_eq(v_opt_942_, v___x_1191_);
if (v___x_1192_ == 0)
{
uint32_t v___x_1193_; uint8_t v___x_1194_; 
v___x_1193_ = 77;
v___x_1194_ = lean_uint32_dec_eq(v_opt_942_, v___x_1193_);
if (v___x_1194_ == 0)
{
uint32_t v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = 84;
v___x_1196_ = lean_uint32_dec_eq(v_opt_942_, v___x_1195_);
if (v___x_1196_ == 0)
{
uint32_t v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = 116;
v___x_1198_ = lean_uint32_dec_eq(v_opt_942_, v___x_1197_);
if (v___x_1198_ == 0)
{
uint32_t v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = 113;
v___x_1200_ = lean_uint32_dec_eq(v_opt_942_, v___x_1199_);
if (v___x_1200_ == 0)
{
uint32_t v___x_1201_; uint8_t v___x_1202_; 
v___x_1201_ = 100;
v___x_1202_ = lean_uint32_dec_eq(v_opt_942_, v___x_1201_);
if (v___x_1202_ == 0)
{
uint32_t v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = 79;
v___x_1204_ = lean_uint32_dec_eq(v_opt_942_, v___x_1203_);
if (v___x_1204_ == 0)
{
uint32_t v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = 78;
v___x_1206_ = lean_uint32_dec_eq(v_opt_942_, v___x_1205_);
if (v___x_1206_ == 0)
{
uint32_t v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = 74;
v___x_1208_ = lean_uint32_dec_eq(v_opt_942_, v___x_1207_);
if (v___x_1208_ == 0)
{
uint32_t v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = 97;
v___x_1210_ = lean_uint32_dec_eq(v_opt_942_, v___x_1209_);
if (v___x_1210_ == 0)
{
uint32_t v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = 120;
v___x_1212_ = lean_uint32_dec_eq(v_opt_942_, v___x_1211_);
if (v___x_1212_ == 0)
{
uint32_t v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = 76;
v___x_1214_ = lean_uint32_dec_eq(v_opt_942_, v___x_1213_);
if (v___x_1214_ == 0)
{
uint32_t v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = 68;
v___x_1216_ = lean_uint32_dec_eq(v_opt_942_, v___x_1215_);
if (v___x_1216_ == 0)
{
uint32_t v___x_1217_; uint8_t v___x_1218_; 
v___x_1217_ = 83;
v___x_1218_ = lean_uint32_dec_eq(v_opt_942_, v___x_1217_);
if (v___x_1218_ == 0)
{
uint32_t v___x_1219_; uint8_t v___x_1220_; 
v___x_1219_ = 87;
v___x_1220_ = lean_uint32_dec_eq(v_opt_942_, v___x_1219_);
if (v___x_1220_ == 0)
{
uint32_t v___x_1221_; uint8_t v___x_1222_; 
v___x_1221_ = 80;
v___x_1222_ = lean_uint32_dec_eq(v_opt_942_, v___x_1221_);
if (v___x_1222_ == 0)
{
uint32_t v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = 66;
v___x_1224_ = lean_uint32_dec_eq(v_opt_942_, v___x_1223_);
if (v___x_1224_ == 0)
{
uint32_t v___x_1225_; uint8_t v___x_1226_; 
v___x_1225_ = 112;
v___x_1226_ = lean_uint32_dec_eq(v_opt_942_, v___x_1225_);
if (v___x_1226_ == 0)
{
uint32_t v___x_1227_; uint8_t v___x_1228_; 
v___x_1227_ = 108;
v___x_1228_ = lean_uint32_dec_eq(v_opt_942_, v___x_1227_);
if (v___x_1228_ == 0)
{
uint32_t v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = 117;
v___x_1230_ = lean_uint32_dec_eq(v_opt_942_, v___x_1229_);
if (v___x_1230_ == 0)
{
uint32_t v___x_1231_; uint8_t v___x_1232_; 
v___x_1231_ = 69;
v___x_1232_ = lean_uint32_dec_eq(v_opt_942_, v___x_1231_);
if (v___x_1232_ == 0)
{
uint32_t v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = 89;
v___x_1234_ = lean_uint32_dec_eq(v_opt_942_, v___x_1233_);
if (v___x_1234_ == 0)
{
uint32_t v___x_1235_; uint8_t v___x_1236_; 
v___x_1235_ = 90;
v___x_1236_ = lean_uint32_dec_eq(v_opt_942_, v___x_1235_);
if (v___x_1236_ == 0)
{
uint32_t v___x_1237_; uint8_t v___x_1238_; 
v___x_1237_ = 72;
v___x_1238_ = lean_uint32_dec_eq(v_opt_942_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_dec(v_optArg_x3f_943_);
lean_dec_ref(v_opts_941_);
goto v___jp_1075_;
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1));
v___x_1240_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1239_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1281_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1281_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1281_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v_leanOpts_1245_; lean_object* v_forwardedArgs_1246_; uint8_t v_component_1247_; uint8_t v_printPrefix_1248_; uint8_t v_printLibDir_1249_; uint8_t v_useStdin_1250_; uint8_t v_onlyDeps_1251_; uint8_t v_onlySrcDeps_1252_; uint8_t v_depsJson_1253_; lean_object* v_opts_1254_; uint32_t v_trustLevel_1255_; uint32_t v_numThreads_1256_; lean_object* v_rootDir_x3f_1257_; lean_object* v_setupFileName_x3f_1258_; lean_object* v_oleanFileName_x3f_1259_; lean_object* v_ileanFileName_x3f_1260_; lean_object* v_cFileName_x3f_1261_; lean_object* v_bcFileName_x3f_1262_; uint8_t v_jsonOutput_1263_; lean_object* v_errorOnKinds_1264_; uint8_t v_printStats_1265_; uint8_t v_run_1266_; lean_object* v_incrSaveFileName_x3f_1267_; lean_object* v_incrLoadFileName_x3f_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1279_; 
v_leanOpts_1245_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1246_ = lean_ctor_get(v_opts_941_, 1);
v_component_1247_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_1248_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_1249_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_1250_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_1251_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1252_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_1253_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_1254_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1255_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_1256_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1257_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1258_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1259_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1260_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1261_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1262_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1263_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_1264_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1265_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_1266_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1267_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_1268_ = lean_ctor_get(v_opts_941_, 11);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; 
v_unused_1280_ = lean_ctor_get(v_opts_941_, 12);
lean_dec(v_unused_1280_);
v___x_1270_ = v_opts_941_;
v_isShared_1271_ = v_isSharedCheck_1279_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_incrLoadFileName_x3f_1268_);
lean_inc(v_incrSaveFileName_x3f_1267_);
lean_inc(v_errorOnKinds_1264_);
lean_inc(v_bcFileName_x3f_1262_);
lean_inc(v_cFileName_x3f_1261_);
lean_inc(v_ileanFileName_x3f_1260_);
lean_inc(v_oleanFileName_x3f_1259_);
lean_inc(v_setupFileName_x3f_1258_);
lean_inc(v_rootDir_x3f_1257_);
lean_inc(v_opts_1254_);
lean_inc(v_forwardedArgs_1246_);
lean_inc(v_leanOpts_1245_);
lean_dec(v_opts_941_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1279_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1272_; lean_object* v___x_1274_; 
v___x_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1272_, 0, v_a_1241_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 12, v___x_1272_);
v___x_1274_ = v___x_1270_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_leanOpts_1245_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_forwardedArgs_1246_);
lean_ctor_set(v_reuseFailAlloc_1278_, 2, v_opts_1254_);
lean_ctor_set(v_reuseFailAlloc_1278_, 3, v_rootDir_x3f_1257_);
lean_ctor_set(v_reuseFailAlloc_1278_, 4, v_setupFileName_x3f_1258_);
lean_ctor_set(v_reuseFailAlloc_1278_, 5, v_oleanFileName_x3f_1259_);
lean_ctor_set(v_reuseFailAlloc_1278_, 6, v_ileanFileName_x3f_1260_);
lean_ctor_set(v_reuseFailAlloc_1278_, 7, v_cFileName_x3f_1261_);
lean_ctor_set(v_reuseFailAlloc_1278_, 8, v_bcFileName_x3f_1262_);
lean_ctor_set(v_reuseFailAlloc_1278_, 9, v_errorOnKinds_1264_);
lean_ctor_set(v_reuseFailAlloc_1278_, 10, v_incrSaveFileName_x3f_1267_);
lean_ctor_set(v_reuseFailAlloc_1278_, 11, v_incrLoadFileName_x3f_1268_);
lean_ctor_set(v_reuseFailAlloc_1278_, 12, v___x_1272_);
lean_ctor_set_uint8(v_reuseFailAlloc_1278_, sizeof(void*)*13 + 8, v_component_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1278_, sizeof(void*)*13 + 9, v_printPrefix_1248_);
lean_ctor_set_uint8(v_reuseFailAlloc_1278_, sizeof(void*)*13 + 10, v_printLibDir_1249_);
lean_ctor_set_uint8(v_reuseFailAlloc_1278_, sizeof(void*)*13 + 11, v_useStdin_1250_);
lean_ctor_set_uint8(v_reuseFailAlloc_1278_, sizeof(void*)*13 + 12, v_onlyDeps_1251_);
lean_ctor_set_uint8(v_reuseFailAlloc_1278_, sizeof(void*)*13 + 13, v_onlySrcDeps_1252_);
lean_ctor_set_uint8(v_reuseFailAlloc_1278_, sizeof(void*)*13 + 14, v_depsJson_1253_);
lean_ctor_set_uint32(v_reuseFailAlloc_1278_, sizeof(void*)*13, v_trustLevel_1255_);
lean_ctor_set_uint32(v_reuseFailAlloc_1278_, sizeof(void*)*13 + 4, v_numThreads_1256_);
lean_ctor_set_uint8(v_reuseFailAlloc_1278_, sizeof(void*)*13 + 15, v_jsonOutput_1263_);
lean_ctor_set_uint8(v_reuseFailAlloc_1278_, sizeof(void*)*13 + 16, v_printStats_1265_);
lean_ctor_set_uint8(v_reuseFailAlloc_1278_, sizeof(void*)*13 + 17, v_run_1266_);
v___x_1274_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
lean_object* v___x_1276_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v___x_1274_);
v___x_1276_ = v___x_1243_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
lean_dec_ref(v_opts_941_);
v_a_1282_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1282_);
lean_dec_ref_known(v___x_1240_, 1);
v___x_1286_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1287_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1286_);
lean_dec_ref(v___x_1287_);
goto v___jp_1283_;
v___jp_1283_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_io_error_to_string(v_a_1282_);
v___x_1285_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1284_);
lean_dec_ref(v___x_1285_);
goto v___jp_1047_;
}
}
}
}
else
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2));
v___x_1289_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1288_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1330_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1292_ = v___x_1289_;
v_isShared_1293_ = v_isSharedCheck_1330_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1289_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1330_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v_leanOpts_1294_; lean_object* v_forwardedArgs_1295_; uint8_t v_component_1296_; uint8_t v_printPrefix_1297_; uint8_t v_printLibDir_1298_; uint8_t v_useStdin_1299_; uint8_t v_onlyDeps_1300_; uint8_t v_onlySrcDeps_1301_; uint8_t v_depsJson_1302_; lean_object* v_opts_1303_; uint32_t v_trustLevel_1304_; uint32_t v_numThreads_1305_; lean_object* v_rootDir_x3f_1306_; lean_object* v_setupFileName_x3f_1307_; lean_object* v_oleanFileName_x3f_1308_; lean_object* v_ileanFileName_x3f_1309_; lean_object* v_cFileName_x3f_1310_; lean_object* v_bcFileName_x3f_1311_; uint8_t v_jsonOutput_1312_; lean_object* v_errorOnKinds_1313_; uint8_t v_printStats_1314_; uint8_t v_run_1315_; lean_object* v_incrSaveFileName_x3f_1316_; lean_object* v_incrHeaderSaveFileName_x3f_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1328_; 
v_leanOpts_1294_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1295_ = lean_ctor_get(v_opts_941_, 1);
v_component_1296_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_1297_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_1298_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_1299_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_1300_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1301_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_1302_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_1303_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1304_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_1305_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1306_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1307_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1308_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1309_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1310_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1311_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1312_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_1313_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1314_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_1315_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1316_ = lean_ctor_get(v_opts_941_, 10);
v_incrHeaderSaveFileName_x3f_1317_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1328_ == 0)
{
lean_object* v_unused_1329_; 
v_unused_1329_ = lean_ctor_get(v_opts_941_, 11);
lean_dec(v_unused_1329_);
v___x_1319_ = v_opts_941_;
v_isShared_1320_ = v_isSharedCheck_1328_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1317_);
lean_inc(v_incrSaveFileName_x3f_1316_);
lean_inc(v_errorOnKinds_1313_);
lean_inc(v_bcFileName_x3f_1311_);
lean_inc(v_cFileName_x3f_1310_);
lean_inc(v_ileanFileName_x3f_1309_);
lean_inc(v_oleanFileName_x3f_1308_);
lean_inc(v_setupFileName_x3f_1307_);
lean_inc(v_rootDir_x3f_1306_);
lean_inc(v_opts_1303_);
lean_inc(v_forwardedArgs_1295_);
lean_inc(v_leanOpts_1294_);
lean_dec(v_opts_941_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1328_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v___x_1323_; 
v___x_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1321_, 0, v_a_1290_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 11, v___x_1321_);
v___x_1323_ = v___x_1319_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_leanOpts_1294_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_forwardedArgs_1295_);
lean_ctor_set(v_reuseFailAlloc_1327_, 2, v_opts_1303_);
lean_ctor_set(v_reuseFailAlloc_1327_, 3, v_rootDir_x3f_1306_);
lean_ctor_set(v_reuseFailAlloc_1327_, 4, v_setupFileName_x3f_1307_);
lean_ctor_set(v_reuseFailAlloc_1327_, 5, v_oleanFileName_x3f_1308_);
lean_ctor_set(v_reuseFailAlloc_1327_, 6, v_ileanFileName_x3f_1309_);
lean_ctor_set(v_reuseFailAlloc_1327_, 7, v_cFileName_x3f_1310_);
lean_ctor_set(v_reuseFailAlloc_1327_, 8, v_bcFileName_x3f_1311_);
lean_ctor_set(v_reuseFailAlloc_1327_, 9, v_errorOnKinds_1313_);
lean_ctor_set(v_reuseFailAlloc_1327_, 10, v_incrSaveFileName_x3f_1316_);
lean_ctor_set(v_reuseFailAlloc_1327_, 11, v___x_1321_);
lean_ctor_set(v_reuseFailAlloc_1327_, 12, v_incrHeaderSaveFileName_x3f_1317_);
lean_ctor_set_uint8(v_reuseFailAlloc_1327_, sizeof(void*)*13 + 8, v_component_1296_);
lean_ctor_set_uint8(v_reuseFailAlloc_1327_, sizeof(void*)*13 + 9, v_printPrefix_1297_);
lean_ctor_set_uint8(v_reuseFailAlloc_1327_, sizeof(void*)*13 + 10, v_printLibDir_1298_);
lean_ctor_set_uint8(v_reuseFailAlloc_1327_, sizeof(void*)*13 + 11, v_useStdin_1299_);
lean_ctor_set_uint8(v_reuseFailAlloc_1327_, sizeof(void*)*13 + 12, v_onlyDeps_1300_);
lean_ctor_set_uint8(v_reuseFailAlloc_1327_, sizeof(void*)*13 + 13, v_onlySrcDeps_1301_);
lean_ctor_set_uint8(v_reuseFailAlloc_1327_, sizeof(void*)*13 + 14, v_depsJson_1302_);
lean_ctor_set_uint32(v_reuseFailAlloc_1327_, sizeof(void*)*13, v_trustLevel_1304_);
lean_ctor_set_uint32(v_reuseFailAlloc_1327_, sizeof(void*)*13 + 4, v_numThreads_1305_);
lean_ctor_set_uint8(v_reuseFailAlloc_1327_, sizeof(void*)*13 + 15, v_jsonOutput_1312_);
lean_ctor_set_uint8(v_reuseFailAlloc_1327_, sizeof(void*)*13 + 16, v_printStats_1314_);
lean_ctor_set_uint8(v_reuseFailAlloc_1327_, sizeof(void*)*13 + 17, v_run_1315_);
v___x_1323_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
lean_object* v___x_1325_; 
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 0, v___x_1323_);
v___x_1325_ = v___x_1292_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_dec_ref(v_opts_941_);
v_a_1331_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1331_);
lean_dec_ref_known(v___x_1289_, 1);
v___x_1335_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1336_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1335_);
lean_dec_ref(v___x_1336_);
goto v___jp_1332_;
v___jp_1332_:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = lean_io_error_to_string(v_a_1331_);
v___x_1334_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1333_);
lean_dec_ref(v___x_1334_);
goto v___jp_1081_;
}
}
}
}
else
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3));
v___x_1338_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1337_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1379_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1341_ = v___x_1338_;
v_isShared_1342_ = v_isSharedCheck_1379_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1338_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1379_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v_leanOpts_1343_; lean_object* v_forwardedArgs_1344_; uint8_t v_component_1345_; uint8_t v_printPrefix_1346_; uint8_t v_printLibDir_1347_; uint8_t v_useStdin_1348_; uint8_t v_onlyDeps_1349_; uint8_t v_onlySrcDeps_1350_; uint8_t v_depsJson_1351_; lean_object* v_opts_1352_; uint32_t v_trustLevel_1353_; uint32_t v_numThreads_1354_; lean_object* v_rootDir_x3f_1355_; lean_object* v_setupFileName_x3f_1356_; lean_object* v_oleanFileName_x3f_1357_; lean_object* v_ileanFileName_x3f_1358_; lean_object* v_cFileName_x3f_1359_; lean_object* v_bcFileName_x3f_1360_; uint8_t v_jsonOutput_1361_; lean_object* v_errorOnKinds_1362_; uint8_t v_printStats_1363_; uint8_t v_run_1364_; lean_object* v_incrLoadFileName_x3f_1365_; lean_object* v_incrHeaderSaveFileName_x3f_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1377_; 
v_leanOpts_1343_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1344_ = lean_ctor_get(v_opts_941_, 1);
v_component_1345_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_1346_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_1347_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_1348_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_1349_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1350_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_1351_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_1352_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1353_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_1354_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1355_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1356_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1357_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1358_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1359_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1360_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1361_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_1362_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1363_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_1364_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrLoadFileName_x3f_1365_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_1366_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1377_ == 0)
{
lean_object* v_unused_1378_; 
v_unused_1378_ = lean_ctor_get(v_opts_941_, 10);
lean_dec(v_unused_1378_);
v___x_1368_ = v_opts_941_;
v_isShared_1369_ = v_isSharedCheck_1377_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1366_);
lean_inc(v_incrLoadFileName_x3f_1365_);
lean_inc(v_errorOnKinds_1362_);
lean_inc(v_bcFileName_x3f_1360_);
lean_inc(v_cFileName_x3f_1359_);
lean_inc(v_ileanFileName_x3f_1358_);
lean_inc(v_oleanFileName_x3f_1357_);
lean_inc(v_setupFileName_x3f_1356_);
lean_inc(v_rootDir_x3f_1355_);
lean_inc(v_opts_1352_);
lean_inc(v_forwardedArgs_1344_);
lean_inc(v_leanOpts_1343_);
lean_dec(v_opts_941_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1377_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1370_, 0, v_a_1339_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 10, v___x_1370_);
v___x_1372_ = v___x_1368_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_leanOpts_1343_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_forwardedArgs_1344_);
lean_ctor_set(v_reuseFailAlloc_1376_, 2, v_opts_1352_);
lean_ctor_set(v_reuseFailAlloc_1376_, 3, v_rootDir_x3f_1355_);
lean_ctor_set(v_reuseFailAlloc_1376_, 4, v_setupFileName_x3f_1356_);
lean_ctor_set(v_reuseFailAlloc_1376_, 5, v_oleanFileName_x3f_1357_);
lean_ctor_set(v_reuseFailAlloc_1376_, 6, v_ileanFileName_x3f_1358_);
lean_ctor_set(v_reuseFailAlloc_1376_, 7, v_cFileName_x3f_1359_);
lean_ctor_set(v_reuseFailAlloc_1376_, 8, v_bcFileName_x3f_1360_);
lean_ctor_set(v_reuseFailAlloc_1376_, 9, v_errorOnKinds_1362_);
lean_ctor_set(v_reuseFailAlloc_1376_, 10, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1376_, 11, v_incrLoadFileName_x3f_1365_);
lean_ctor_set(v_reuseFailAlloc_1376_, 12, v_incrHeaderSaveFileName_x3f_1366_);
lean_ctor_set_uint8(v_reuseFailAlloc_1376_, sizeof(void*)*13 + 8, v_component_1345_);
lean_ctor_set_uint8(v_reuseFailAlloc_1376_, sizeof(void*)*13 + 9, v_printPrefix_1346_);
lean_ctor_set_uint8(v_reuseFailAlloc_1376_, sizeof(void*)*13 + 10, v_printLibDir_1347_);
lean_ctor_set_uint8(v_reuseFailAlloc_1376_, sizeof(void*)*13 + 11, v_useStdin_1348_);
lean_ctor_set_uint8(v_reuseFailAlloc_1376_, sizeof(void*)*13 + 12, v_onlyDeps_1349_);
lean_ctor_set_uint8(v_reuseFailAlloc_1376_, sizeof(void*)*13 + 13, v_onlySrcDeps_1350_);
lean_ctor_set_uint8(v_reuseFailAlloc_1376_, sizeof(void*)*13 + 14, v_depsJson_1351_);
lean_ctor_set_uint32(v_reuseFailAlloc_1376_, sizeof(void*)*13, v_trustLevel_1353_);
lean_ctor_set_uint32(v_reuseFailAlloc_1376_, sizeof(void*)*13 + 4, v_numThreads_1354_);
lean_ctor_set_uint8(v_reuseFailAlloc_1376_, sizeof(void*)*13 + 15, v_jsonOutput_1361_);
lean_ctor_set_uint8(v_reuseFailAlloc_1376_, sizeof(void*)*13 + 16, v_printStats_1363_);
lean_ctor_set_uint8(v_reuseFailAlloc_1376_, sizeof(void*)*13 + 17, v_run_1364_);
v___x_1372_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v___x_1374_; 
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v___x_1372_);
v___x_1374_ = v___x_1341_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
lean_dec_ref(v_opts_941_);
v_a_1380_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_a_1380_);
lean_dec_ref_known(v___x_1338_, 1);
v___x_1384_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1385_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1384_);
lean_dec_ref(v___x_1385_);
goto v___jp_1381_;
v___jp_1381_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = lean_io_error_to_string(v_a_1380_);
v___x_1383_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1382_);
lean_dec_ref(v___x_1383_);
goto v___jp_1041_;
}
}
}
}
else
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4));
v___x_1387_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1386_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1429_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1390_ = v___x_1387_;
v_isShared_1391_ = v_isSharedCheck_1429_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1387_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1429_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v_leanOpts_1392_; lean_object* v_forwardedArgs_1393_; uint8_t v_component_1394_; uint8_t v_printPrefix_1395_; uint8_t v_printLibDir_1396_; uint8_t v_useStdin_1397_; uint8_t v_onlyDeps_1398_; uint8_t v_onlySrcDeps_1399_; uint8_t v_depsJson_1400_; lean_object* v_opts_1401_; uint32_t v_trustLevel_1402_; uint32_t v_numThreads_1403_; lean_object* v_rootDir_x3f_1404_; lean_object* v_setupFileName_x3f_1405_; lean_object* v_oleanFileName_x3f_1406_; lean_object* v_ileanFileName_x3f_1407_; lean_object* v_cFileName_x3f_1408_; lean_object* v_bcFileName_x3f_1409_; uint8_t v_jsonOutput_1410_; lean_object* v_errorOnKinds_1411_; uint8_t v_printStats_1412_; uint8_t v_run_1413_; lean_object* v_incrSaveFileName_x3f_1414_; lean_object* v_incrLoadFileName_x3f_1415_; lean_object* v_incrHeaderSaveFileName_x3f_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1428_; 
v_leanOpts_1392_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1393_ = lean_ctor_get(v_opts_941_, 1);
v_component_1394_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_1395_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_1396_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_1397_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_1398_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1399_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_1400_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_1401_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1402_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_1403_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1404_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1405_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1406_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1407_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1408_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1409_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1410_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_1411_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1412_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_1413_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1414_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_1415_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_1416_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1418_ = v_opts_941_;
v_isShared_1419_ = v_isSharedCheck_1428_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1416_);
lean_inc(v_incrLoadFileName_x3f_1415_);
lean_inc(v_incrSaveFileName_x3f_1414_);
lean_inc(v_errorOnKinds_1411_);
lean_inc(v_bcFileName_x3f_1409_);
lean_inc(v_cFileName_x3f_1408_);
lean_inc(v_ileanFileName_x3f_1407_);
lean_inc(v_oleanFileName_x3f_1406_);
lean_inc(v_setupFileName_x3f_1405_);
lean_inc(v_rootDir_x3f_1404_);
lean_inc(v_opts_1401_);
lean_inc(v_forwardedArgs_1393_);
lean_inc(v_leanOpts_1392_);
lean_dec(v_opts_941_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1428_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1420_ = l_String_toName(v_a_1388_);
v___x_1421_ = lean_array_push(v_errorOnKinds_1411_, v___x_1420_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 9, v___x_1421_);
v___x_1423_ = v___x_1418_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_leanOpts_1392_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_forwardedArgs_1393_);
lean_ctor_set(v_reuseFailAlloc_1427_, 2, v_opts_1401_);
lean_ctor_set(v_reuseFailAlloc_1427_, 3, v_rootDir_x3f_1404_);
lean_ctor_set(v_reuseFailAlloc_1427_, 4, v_setupFileName_x3f_1405_);
lean_ctor_set(v_reuseFailAlloc_1427_, 5, v_oleanFileName_x3f_1406_);
lean_ctor_set(v_reuseFailAlloc_1427_, 6, v_ileanFileName_x3f_1407_);
lean_ctor_set(v_reuseFailAlloc_1427_, 7, v_cFileName_x3f_1408_);
lean_ctor_set(v_reuseFailAlloc_1427_, 8, v_bcFileName_x3f_1409_);
lean_ctor_set(v_reuseFailAlloc_1427_, 9, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1427_, 10, v_incrSaveFileName_x3f_1414_);
lean_ctor_set(v_reuseFailAlloc_1427_, 11, v_incrLoadFileName_x3f_1415_);
lean_ctor_set(v_reuseFailAlloc_1427_, 12, v_incrHeaderSaveFileName_x3f_1416_);
lean_ctor_set_uint8(v_reuseFailAlloc_1427_, sizeof(void*)*13 + 8, v_component_1394_);
lean_ctor_set_uint8(v_reuseFailAlloc_1427_, sizeof(void*)*13 + 9, v_printPrefix_1395_);
lean_ctor_set_uint8(v_reuseFailAlloc_1427_, sizeof(void*)*13 + 10, v_printLibDir_1396_);
lean_ctor_set_uint8(v_reuseFailAlloc_1427_, sizeof(void*)*13 + 11, v_useStdin_1397_);
lean_ctor_set_uint8(v_reuseFailAlloc_1427_, sizeof(void*)*13 + 12, v_onlyDeps_1398_);
lean_ctor_set_uint8(v_reuseFailAlloc_1427_, sizeof(void*)*13 + 13, v_onlySrcDeps_1399_);
lean_ctor_set_uint8(v_reuseFailAlloc_1427_, sizeof(void*)*13 + 14, v_depsJson_1400_);
lean_ctor_set_uint32(v_reuseFailAlloc_1427_, sizeof(void*)*13, v_trustLevel_1402_);
lean_ctor_set_uint32(v_reuseFailAlloc_1427_, sizeof(void*)*13 + 4, v_numThreads_1403_);
lean_ctor_set_uint8(v_reuseFailAlloc_1427_, sizeof(void*)*13 + 15, v_jsonOutput_1410_);
lean_ctor_set_uint8(v_reuseFailAlloc_1427_, sizeof(void*)*13 + 16, v_printStats_1412_);
lean_ctor_set_uint8(v_reuseFailAlloc_1427_, sizeof(void*)*13 + 17, v_run_1413_);
v___x_1423_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1425_; 
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v___x_1423_);
v___x_1425_ = v___x_1390_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
lean_dec_ref(v_opts_941_);
v_a_1430_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_a_1430_);
lean_dec_ref_known(v___x_1387_, 1);
v___x_1434_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1435_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1434_);
lean_dec_ref(v___x_1435_);
goto v___jp_1431_;
v___jp_1431_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = lean_io_error_to_string(v_a_1430_);
v___x_1433_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1432_);
lean_dec_ref(v___x_1433_);
goto v___jp_1087_;
}
}
}
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5));
v___x_1437_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1436_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1478_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1440_ = v___x_1437_;
v_isShared_1441_ = v_isSharedCheck_1478_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1437_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1478_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v_leanOpts_1442_; lean_object* v_forwardedArgs_1443_; uint8_t v_component_1444_; uint8_t v_printPrefix_1445_; uint8_t v_printLibDir_1446_; uint8_t v_useStdin_1447_; uint8_t v_onlyDeps_1448_; uint8_t v_onlySrcDeps_1449_; uint8_t v_depsJson_1450_; lean_object* v_opts_1451_; uint32_t v_trustLevel_1452_; uint32_t v_numThreads_1453_; lean_object* v_rootDir_x3f_1454_; lean_object* v_oleanFileName_x3f_1455_; lean_object* v_ileanFileName_x3f_1456_; lean_object* v_cFileName_x3f_1457_; lean_object* v_bcFileName_x3f_1458_; uint8_t v_jsonOutput_1459_; lean_object* v_errorOnKinds_1460_; uint8_t v_printStats_1461_; uint8_t v_run_1462_; lean_object* v_incrSaveFileName_x3f_1463_; lean_object* v_incrLoadFileName_x3f_1464_; lean_object* v_incrHeaderSaveFileName_x3f_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1476_; 
v_leanOpts_1442_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1443_ = lean_ctor_get(v_opts_941_, 1);
v_component_1444_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_1445_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_1446_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_1447_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_1448_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1449_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_1450_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_1451_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1452_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_1453_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1454_ = lean_ctor_get(v_opts_941_, 3);
v_oleanFileName_x3f_1455_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1456_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1457_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1458_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1459_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_1460_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1461_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_1462_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1463_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_1464_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_1465_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1476_ == 0)
{
lean_object* v_unused_1477_; 
v_unused_1477_ = lean_ctor_get(v_opts_941_, 4);
lean_dec(v_unused_1477_);
v___x_1467_ = v_opts_941_;
v_isShared_1468_ = v_isSharedCheck_1476_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1465_);
lean_inc(v_incrLoadFileName_x3f_1464_);
lean_inc(v_incrSaveFileName_x3f_1463_);
lean_inc(v_errorOnKinds_1460_);
lean_inc(v_bcFileName_x3f_1458_);
lean_inc(v_cFileName_x3f_1457_);
lean_inc(v_ileanFileName_x3f_1456_);
lean_inc(v_oleanFileName_x3f_1455_);
lean_inc(v_rootDir_x3f_1454_);
lean_inc(v_opts_1451_);
lean_inc(v_forwardedArgs_1443_);
lean_inc(v_leanOpts_1442_);
lean_dec(v_opts_941_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1476_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1469_; lean_object* v___x_1471_; 
v___x_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1469_, 0, v_a_1438_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 4, v___x_1469_);
v___x_1471_ = v___x_1467_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_leanOpts_1442_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_forwardedArgs_1443_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_opts_1451_);
lean_ctor_set(v_reuseFailAlloc_1475_, 3, v_rootDir_x3f_1454_);
lean_ctor_set(v_reuseFailAlloc_1475_, 4, v___x_1469_);
lean_ctor_set(v_reuseFailAlloc_1475_, 5, v_oleanFileName_x3f_1455_);
lean_ctor_set(v_reuseFailAlloc_1475_, 6, v_ileanFileName_x3f_1456_);
lean_ctor_set(v_reuseFailAlloc_1475_, 7, v_cFileName_x3f_1457_);
lean_ctor_set(v_reuseFailAlloc_1475_, 8, v_bcFileName_x3f_1458_);
lean_ctor_set(v_reuseFailAlloc_1475_, 9, v_errorOnKinds_1460_);
lean_ctor_set(v_reuseFailAlloc_1475_, 10, v_incrSaveFileName_x3f_1463_);
lean_ctor_set(v_reuseFailAlloc_1475_, 11, v_incrLoadFileName_x3f_1464_);
lean_ctor_set(v_reuseFailAlloc_1475_, 12, v_incrHeaderSaveFileName_x3f_1465_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*13 + 8, v_component_1444_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*13 + 9, v_printPrefix_1445_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*13 + 10, v_printLibDir_1446_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*13 + 11, v_useStdin_1447_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*13 + 12, v_onlyDeps_1448_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*13 + 13, v_onlySrcDeps_1449_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*13 + 14, v_depsJson_1450_);
lean_ctor_set_uint32(v_reuseFailAlloc_1475_, sizeof(void*)*13, v_trustLevel_1452_);
lean_ctor_set_uint32(v_reuseFailAlloc_1475_, sizeof(void*)*13 + 4, v_numThreads_1453_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*13 + 15, v_jsonOutput_1459_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*13 + 16, v_printStats_1461_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*13 + 17, v_run_1462_);
v___x_1471_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
lean_object* v___x_1473_; 
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v___x_1471_);
v___x_1473_ = v___x_1440_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_dec_ref(v_opts_941_);
v_a_1479_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1479_);
lean_dec_ref_known(v___x_1437_, 1);
v___x_1483_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1484_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1483_);
lean_dec_ref(v___x_1484_);
goto v___jp_1480_;
v___jp_1480_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = lean_io_error_to_string(v_a_1479_);
v___x_1482_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1481_);
lean_dec_ref(v___x_1482_);
goto v___jp_1035_;
}
}
}
}
else
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6));
v___x_1486_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1485_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; lean_object* v___x_1488_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc_n(v_a_1487_, 2);
lean_dec_ref_known(v___x_1486_, 1);
v___x_1488_ = lean_load_dynlib(v_a_1487_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1530_; 
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; 
v_unused_1531_ = lean_ctor_get(v___x_1488_, 0);
lean_dec(v_unused_1531_);
v___x_1490_ = v___x_1488_;
v_isShared_1491_ = v_isSharedCheck_1530_;
goto v_resetjp_1489_;
}
else
{
lean_dec(v___x_1488_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1530_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v_leanOpts_1492_; lean_object* v_forwardedArgs_1493_; uint8_t v_component_1494_; uint8_t v_printPrefix_1495_; uint8_t v_printLibDir_1496_; uint8_t v_useStdin_1497_; uint8_t v_onlyDeps_1498_; uint8_t v_onlySrcDeps_1499_; uint8_t v_depsJson_1500_; lean_object* v_opts_1501_; uint32_t v_trustLevel_1502_; uint32_t v_numThreads_1503_; lean_object* v_rootDir_x3f_1504_; lean_object* v_setupFileName_x3f_1505_; lean_object* v_oleanFileName_x3f_1506_; lean_object* v_ileanFileName_x3f_1507_; lean_object* v_cFileName_x3f_1508_; lean_object* v_bcFileName_x3f_1509_; uint8_t v_jsonOutput_1510_; lean_object* v_errorOnKinds_1511_; uint8_t v_printStats_1512_; uint8_t v_run_1513_; lean_object* v_incrSaveFileName_x3f_1514_; lean_object* v_incrLoadFileName_x3f_1515_; lean_object* v_incrHeaderSaveFileName_x3f_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1529_; 
v_leanOpts_1492_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1493_ = lean_ctor_get(v_opts_941_, 1);
v_component_1494_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_1495_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_1496_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_1497_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_1498_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1499_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_1500_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_1501_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1502_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_1503_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1504_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1505_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1506_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1507_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1508_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1509_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1510_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_1511_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1512_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_1513_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1514_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_1515_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_1516_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1518_ = v_opts_941_;
v_isShared_1519_ = v_isSharedCheck_1529_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1516_);
lean_inc(v_incrLoadFileName_x3f_1515_);
lean_inc(v_incrSaveFileName_x3f_1514_);
lean_inc(v_errorOnKinds_1511_);
lean_inc(v_bcFileName_x3f_1509_);
lean_inc(v_cFileName_x3f_1508_);
lean_inc(v_ileanFileName_x3f_1507_);
lean_inc(v_oleanFileName_x3f_1506_);
lean_inc(v_setupFileName_x3f_1505_);
lean_inc(v_rootDir_x3f_1504_);
lean_inc(v_opts_1501_);
lean_inc(v_forwardedArgs_1493_);
lean_inc(v_leanOpts_1492_);
lean_dec(v_opts_941_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1529_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1524_; 
v___x_1520_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7));
v___x_1521_ = lean_string_append(v___x_1520_, v_a_1487_);
lean_dec(v_a_1487_);
v___x_1522_ = lean_array_push(v_forwardedArgs_1493_, v___x_1521_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 1, v___x_1522_);
v___x_1524_ = v___x_1518_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_leanOpts_1492_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1528_, 2, v_opts_1501_);
lean_ctor_set(v_reuseFailAlloc_1528_, 3, v_rootDir_x3f_1504_);
lean_ctor_set(v_reuseFailAlloc_1528_, 4, v_setupFileName_x3f_1505_);
lean_ctor_set(v_reuseFailAlloc_1528_, 5, v_oleanFileName_x3f_1506_);
lean_ctor_set(v_reuseFailAlloc_1528_, 6, v_ileanFileName_x3f_1507_);
lean_ctor_set(v_reuseFailAlloc_1528_, 7, v_cFileName_x3f_1508_);
lean_ctor_set(v_reuseFailAlloc_1528_, 8, v_bcFileName_x3f_1509_);
lean_ctor_set(v_reuseFailAlloc_1528_, 9, v_errorOnKinds_1511_);
lean_ctor_set(v_reuseFailAlloc_1528_, 10, v_incrSaveFileName_x3f_1514_);
lean_ctor_set(v_reuseFailAlloc_1528_, 11, v_incrLoadFileName_x3f_1515_);
lean_ctor_set(v_reuseFailAlloc_1528_, 12, v_incrHeaderSaveFileName_x3f_1516_);
lean_ctor_set_uint8(v_reuseFailAlloc_1528_, sizeof(void*)*13 + 8, v_component_1494_);
lean_ctor_set_uint8(v_reuseFailAlloc_1528_, sizeof(void*)*13 + 9, v_printPrefix_1495_);
lean_ctor_set_uint8(v_reuseFailAlloc_1528_, sizeof(void*)*13 + 10, v_printLibDir_1496_);
lean_ctor_set_uint8(v_reuseFailAlloc_1528_, sizeof(void*)*13 + 11, v_useStdin_1497_);
lean_ctor_set_uint8(v_reuseFailAlloc_1528_, sizeof(void*)*13 + 12, v_onlyDeps_1498_);
lean_ctor_set_uint8(v_reuseFailAlloc_1528_, sizeof(void*)*13 + 13, v_onlySrcDeps_1499_);
lean_ctor_set_uint8(v_reuseFailAlloc_1528_, sizeof(void*)*13 + 14, v_depsJson_1500_);
lean_ctor_set_uint32(v_reuseFailAlloc_1528_, sizeof(void*)*13, v_trustLevel_1502_);
lean_ctor_set_uint32(v_reuseFailAlloc_1528_, sizeof(void*)*13 + 4, v_numThreads_1503_);
lean_ctor_set_uint8(v_reuseFailAlloc_1528_, sizeof(void*)*13 + 15, v_jsonOutput_1510_);
lean_ctor_set_uint8(v_reuseFailAlloc_1528_, sizeof(void*)*13 + 16, v_printStats_1512_);
lean_ctor_set_uint8(v_reuseFailAlloc_1528_, sizeof(void*)*13 + 17, v_run_1513_);
v___x_1524_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
lean_object* v___x_1526_; 
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 0, v___x_1524_);
v___x_1526_ = v___x_1490_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_dec(v_a_1487_);
lean_dec_ref(v_opts_941_);
v_a_1532_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v___x_1488_, 1);
v___x_1536_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1537_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1536_);
lean_dec_ref(v___x_1537_);
goto v___jp_1533_;
v___jp_1533_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = lean_io_error_to_string(v_a_1532_);
v___x_1535_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1534_);
lean_dec_ref(v___x_1535_);
goto v___jp_1093_;
}
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
lean_dec_ref(v_opts_941_);
v_a_1538_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___x_1486_, 1);
v___x_1542_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1543_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1542_);
lean_dec_ref(v___x_1543_);
goto v___jp_1539_;
v___jp_1539_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = lean_io_error_to_string(v_a_1538_);
v___x_1541_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1540_);
lean_dec_ref(v___x_1541_);
goto v___jp_1029_;
}
}
}
}
else
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8));
v___x_1545_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1544_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1618_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1548_ = v___x_1545_;
v_isShared_1549_ = v_isSharedCheck_1618_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1545_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1618_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v_fst_1551_; lean_object* v_snd_1552_; lean_object* v___y_1601_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1612_ = lean_unsigned_to_nat(0u);
v___x_1613_ = lean_string_utf8_byte_size(v_a_1546_);
lean_inc(v_a_1546_);
v___x_1614_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1614_, 0, v_a_1546_);
lean_ctor_set(v___x_1614_, 1, v___x_1612_);
lean_ctor_set(v___x_1614_, 2, v___x_1613_);
v___x_1615_ = lean_box(0);
v___x_1616_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_1614_, v_a_1546_, v___x_1612_, v___x_1615_);
lean_dec_ref_known(v___x_1614_, 3);
if (lean_obj_tag(v___x_1616_) == 0)
{
v___y_1601_ = v___x_1613_;
goto v___jp_1600_;
}
else
{
lean_object* v_val_1617_; 
v_val_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_val_1617_);
lean_dec_ref_known(v___x_1616_, 1);
v___y_1601_ = v_val_1617_;
goto v___jp_1600_;
}
v___jp_1550_:
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_load_plugin(v_fst_1551_, v_snd_1552_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1595_; 
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1595_ == 0)
{
lean_object* v_unused_1596_; 
v_unused_1596_ = lean_ctor_get(v___x_1553_, 0);
lean_dec(v_unused_1596_);
v___x_1555_ = v___x_1553_;
v_isShared_1556_ = v_isSharedCheck_1595_;
goto v_resetjp_1554_;
}
else
{
lean_dec(v___x_1553_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1595_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v_leanOpts_1557_; lean_object* v_forwardedArgs_1558_; uint8_t v_component_1559_; uint8_t v_printPrefix_1560_; uint8_t v_printLibDir_1561_; uint8_t v_useStdin_1562_; uint8_t v_onlyDeps_1563_; uint8_t v_onlySrcDeps_1564_; uint8_t v_depsJson_1565_; lean_object* v_opts_1566_; uint32_t v_trustLevel_1567_; uint32_t v_numThreads_1568_; lean_object* v_rootDir_x3f_1569_; lean_object* v_setupFileName_x3f_1570_; lean_object* v_oleanFileName_x3f_1571_; lean_object* v_ileanFileName_x3f_1572_; lean_object* v_cFileName_x3f_1573_; lean_object* v_bcFileName_x3f_1574_; uint8_t v_jsonOutput_1575_; lean_object* v_errorOnKinds_1576_; uint8_t v_printStats_1577_; uint8_t v_run_1578_; lean_object* v_incrSaveFileName_x3f_1579_; lean_object* v_incrLoadFileName_x3f_1580_; lean_object* v_incrHeaderSaveFileName_x3f_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1594_; 
v_leanOpts_1557_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1558_ = lean_ctor_get(v_opts_941_, 1);
v_component_1559_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_1560_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_1561_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_1562_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_1563_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1564_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_1565_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_1566_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1567_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_1568_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1569_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1570_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1571_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1572_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1573_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1574_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1575_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_1576_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1577_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_1578_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1579_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_1580_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_1581_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1583_ = v_opts_941_;
v_isShared_1584_ = v_isSharedCheck_1594_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1581_);
lean_inc(v_incrLoadFileName_x3f_1580_);
lean_inc(v_incrSaveFileName_x3f_1579_);
lean_inc(v_errorOnKinds_1576_);
lean_inc(v_bcFileName_x3f_1574_);
lean_inc(v_cFileName_x3f_1573_);
lean_inc(v_ileanFileName_x3f_1572_);
lean_inc(v_oleanFileName_x3f_1571_);
lean_inc(v_setupFileName_x3f_1570_);
lean_inc(v_rootDir_x3f_1569_);
lean_inc(v_opts_1566_);
lean_inc(v_forwardedArgs_1558_);
lean_inc(v_leanOpts_1557_);
lean_dec(v_opts_941_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1594_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1589_; 
v___x_1585_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9));
v___x_1586_ = lean_string_append(v___x_1585_, v_a_1546_);
lean_dec(v_a_1546_);
v___x_1587_ = lean_array_push(v_forwardedArgs_1558_, v___x_1586_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 1, v___x_1587_);
v___x_1589_ = v___x_1583_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_leanOpts_1557_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1593_, 2, v_opts_1566_);
lean_ctor_set(v_reuseFailAlloc_1593_, 3, v_rootDir_x3f_1569_);
lean_ctor_set(v_reuseFailAlloc_1593_, 4, v_setupFileName_x3f_1570_);
lean_ctor_set(v_reuseFailAlloc_1593_, 5, v_oleanFileName_x3f_1571_);
lean_ctor_set(v_reuseFailAlloc_1593_, 6, v_ileanFileName_x3f_1572_);
lean_ctor_set(v_reuseFailAlloc_1593_, 7, v_cFileName_x3f_1573_);
lean_ctor_set(v_reuseFailAlloc_1593_, 8, v_bcFileName_x3f_1574_);
lean_ctor_set(v_reuseFailAlloc_1593_, 9, v_errorOnKinds_1576_);
lean_ctor_set(v_reuseFailAlloc_1593_, 10, v_incrSaveFileName_x3f_1579_);
lean_ctor_set(v_reuseFailAlloc_1593_, 11, v_incrLoadFileName_x3f_1580_);
lean_ctor_set(v_reuseFailAlloc_1593_, 12, v_incrHeaderSaveFileName_x3f_1581_);
lean_ctor_set_uint8(v_reuseFailAlloc_1593_, sizeof(void*)*13 + 8, v_component_1559_);
lean_ctor_set_uint8(v_reuseFailAlloc_1593_, sizeof(void*)*13 + 9, v_printPrefix_1560_);
lean_ctor_set_uint8(v_reuseFailAlloc_1593_, sizeof(void*)*13 + 10, v_printLibDir_1561_);
lean_ctor_set_uint8(v_reuseFailAlloc_1593_, sizeof(void*)*13 + 11, v_useStdin_1562_);
lean_ctor_set_uint8(v_reuseFailAlloc_1593_, sizeof(void*)*13 + 12, v_onlyDeps_1563_);
lean_ctor_set_uint8(v_reuseFailAlloc_1593_, sizeof(void*)*13 + 13, v_onlySrcDeps_1564_);
lean_ctor_set_uint8(v_reuseFailAlloc_1593_, sizeof(void*)*13 + 14, v_depsJson_1565_);
lean_ctor_set_uint32(v_reuseFailAlloc_1593_, sizeof(void*)*13, v_trustLevel_1567_);
lean_ctor_set_uint32(v_reuseFailAlloc_1593_, sizeof(void*)*13 + 4, v_numThreads_1568_);
lean_ctor_set_uint8(v_reuseFailAlloc_1593_, sizeof(void*)*13 + 15, v_jsonOutput_1575_);
lean_ctor_set_uint8(v_reuseFailAlloc_1593_, sizeof(void*)*13 + 16, v_printStats_1577_);
lean_ctor_set_uint8(v_reuseFailAlloc_1593_, sizeof(void*)*13 + 17, v_run_1578_);
v___x_1589_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1591_; 
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1589_);
v___x_1591_ = v___x_1555_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
lean_dec(v_a_1546_);
lean_dec_ref(v_opts_941_);
v_a_1597_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1597_);
lean_dec_ref_known(v___x_1553_, 1);
v___x_1598_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1599_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1598_);
lean_dec_ref(v___x_1599_);
v___y_1103_ = v_a_1597_;
goto v___jp_1102_;
}
}
v___jp_1600_:
{
lean_object* v___x_1602_; uint8_t v___x_1603_; 
v___x_1602_ = lean_string_utf8_byte_size(v_a_1546_);
v___x_1603_ = lean_nat_dec_eq(v___y_1601_, v___x_1602_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1604_ = lean_unsigned_to_nat(0u);
v___x_1605_ = lean_string_utf8_next_fast(v_a_1546_, v___y_1601_);
v___x_1606_ = lean_string_utf8_extract(v_a_1546_, v___x_1604_, v___y_1601_);
lean_dec(v___y_1601_);
v___x_1607_ = lean_string_utf8_extract(v_a_1546_, v___x_1605_, v___x_1602_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set_tag(v___x_1548_, 1);
lean_ctor_set(v___x_1548_, 0, v___x_1607_);
v___x_1609_ = v___x_1548_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1607_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
v_fst_1551_ = v___x_1606_;
v_snd_1552_ = v___x_1609_;
goto v___jp_1550_;
}
}
else
{
lean_object* v___x_1611_; 
lean_dec(v___y_1601_);
lean_del_object(v___x_1548_);
v___x_1611_ = lean_box(0);
lean_inc(v_a_1546_);
v_fst_1551_ = v_a_1546_;
v_snd_1552_ = v___x_1611_;
goto v___jp_1550_;
}
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
lean_dec_ref(v_opts_941_);
v_a_1619_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1619_);
lean_dec_ref_known(v___x_1545_, 1);
v___x_1623_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1624_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1623_);
lean_dec_ref(v___x_1624_);
goto v___jp_1620_;
v___jp_1620_:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = lean_io_error_to_string(v_a_1619_);
v___x_1622_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1621_);
lean_dec_ref(v___x_1622_);
goto v___jp_1023_;
}
}
}
}
else
{
uint8_t v___x_1625_; 
v___x_1625_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__16, &l___private_Lean_Shell_0__Lean_displayHelp___closed__16_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__16);
if (v___x_1625_ == 0)
{
lean_dec(v_optArg_x3f_943_);
lean_dec_ref(v_opts_941_);
goto v___jp_1075_;
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10));
v___x_1627_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1626_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1636_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1630_ = v___x_1627_;
v_isShared_1631_ = v_isSharedCheck_1636_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1627_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1636_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1632_; lean_object* v___x_1634_; 
v___x_1632_ = lean_internal_enable_debug(v_a_1628_);
lean_dec(v_a_1628_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 0, v_opts_941_);
v___x_1634_ = v___x_1630_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_opts_941_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
lean_dec_ref(v_opts_941_);
v_a_1637_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1627_, 1);
v___x_1641_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1642_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1641_);
lean_dec_ref(v___x_1642_);
goto v___jp_1638_;
v___jp_1638_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = lean_io_error_to_string(v_a_1637_);
v___x_1640_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1639_);
lean_dec_ref(v___x_1640_);
goto v___jp_1109_;
}
}
}
}
}
else
{
lean_object* v_leanOpts_1643_; lean_object* v_forwardedArgs_1644_; uint8_t v_component_1645_; uint8_t v_printPrefix_1646_; uint8_t v_printLibDir_1647_; uint8_t v_useStdin_1648_; uint8_t v_onlyDeps_1649_; uint8_t v_onlySrcDeps_1650_; uint8_t v_depsJson_1651_; lean_object* v_opts_1652_; uint32_t v_trustLevel_1653_; uint32_t v_numThreads_1654_; lean_object* v_rootDir_x3f_1655_; lean_object* v_setupFileName_x3f_1656_; lean_object* v_oleanFileName_x3f_1657_; lean_object* v_ileanFileName_x3f_1658_; lean_object* v_cFileName_x3f_1659_; lean_object* v_bcFileName_x3f_1660_; uint8_t v_jsonOutput_1661_; lean_object* v_errorOnKinds_1662_; uint8_t v_printStats_1663_; uint8_t v_run_1664_; lean_object* v_incrSaveFileName_x3f_1665_; lean_object* v_incrLoadFileName_x3f_1666_; lean_object* v_incrHeaderSaveFileName_x3f_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1677_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_1643_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1644_ = lean_ctor_get(v_opts_941_, 1);
v_component_1645_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_1646_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_1647_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_1648_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_1649_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1650_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_1651_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_1652_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1653_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_1654_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1655_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1656_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1657_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1658_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1659_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1660_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1661_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_1662_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1663_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_1664_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1665_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_1666_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_1667_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1669_ = v_opts_941_;
v_isShared_1670_ = v_isSharedCheck_1677_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1667_);
lean_inc(v_incrLoadFileName_x3f_1666_);
lean_inc(v_incrSaveFileName_x3f_1665_);
lean_inc(v_errorOnKinds_1662_);
lean_inc(v_bcFileName_x3f_1660_);
lean_inc(v_cFileName_x3f_1659_);
lean_inc(v_ileanFileName_x3f_1658_);
lean_inc(v_oleanFileName_x3f_1657_);
lean_inc(v_setupFileName_x3f_1656_);
lean_inc(v_rootDir_x3f_1655_);
lean_inc(v_opts_1652_);
lean_inc(v_forwardedArgs_1644_);
lean_inc(v_leanOpts_1643_);
lean_dec(v_opts_941_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1677_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1674_; 
v___x_1671_ = l_Lean_profiler;
v___x_1672_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_1643_, v___x_1671_, v___x_1222_);
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 0, v___x_1672_);
v___x_1674_ = v___x_1669_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1672_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_forwardedArgs_1644_);
lean_ctor_set(v_reuseFailAlloc_1676_, 2, v_opts_1652_);
lean_ctor_set(v_reuseFailAlloc_1676_, 3, v_rootDir_x3f_1655_);
lean_ctor_set(v_reuseFailAlloc_1676_, 4, v_setupFileName_x3f_1656_);
lean_ctor_set(v_reuseFailAlloc_1676_, 5, v_oleanFileName_x3f_1657_);
lean_ctor_set(v_reuseFailAlloc_1676_, 6, v_ileanFileName_x3f_1658_);
lean_ctor_set(v_reuseFailAlloc_1676_, 7, v_cFileName_x3f_1659_);
lean_ctor_set(v_reuseFailAlloc_1676_, 8, v_bcFileName_x3f_1660_);
lean_ctor_set(v_reuseFailAlloc_1676_, 9, v_errorOnKinds_1662_);
lean_ctor_set(v_reuseFailAlloc_1676_, 10, v_incrSaveFileName_x3f_1665_);
lean_ctor_set(v_reuseFailAlloc_1676_, 11, v_incrLoadFileName_x3f_1666_);
lean_ctor_set(v_reuseFailAlloc_1676_, 12, v_incrHeaderSaveFileName_x3f_1667_);
lean_ctor_set_uint8(v_reuseFailAlloc_1676_, sizeof(void*)*13 + 8, v_component_1645_);
lean_ctor_set_uint8(v_reuseFailAlloc_1676_, sizeof(void*)*13 + 9, v_printPrefix_1646_);
lean_ctor_set_uint8(v_reuseFailAlloc_1676_, sizeof(void*)*13 + 10, v_printLibDir_1647_);
lean_ctor_set_uint8(v_reuseFailAlloc_1676_, sizeof(void*)*13 + 11, v_useStdin_1648_);
lean_ctor_set_uint8(v_reuseFailAlloc_1676_, sizeof(void*)*13 + 12, v_onlyDeps_1649_);
lean_ctor_set_uint8(v_reuseFailAlloc_1676_, sizeof(void*)*13 + 13, v_onlySrcDeps_1650_);
lean_ctor_set_uint8(v_reuseFailAlloc_1676_, sizeof(void*)*13 + 14, v_depsJson_1651_);
lean_ctor_set_uint32(v_reuseFailAlloc_1676_, sizeof(void*)*13, v_trustLevel_1653_);
lean_ctor_set_uint32(v_reuseFailAlloc_1676_, sizeof(void*)*13 + 4, v_numThreads_1654_);
lean_ctor_set_uint8(v_reuseFailAlloc_1676_, sizeof(void*)*13 + 15, v_jsonOutput_1661_);
lean_ctor_set_uint8(v_reuseFailAlloc_1676_, sizeof(void*)*13 + 16, v_printStats_1663_);
lean_ctor_set_uint8(v_reuseFailAlloc_1676_, sizeof(void*)*13 + 17, v_run_1664_);
v___x_1674_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
lean_object* v___x_1675_; 
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
return v___x_1675_;
}
}
}
}
else
{
lean_object* v_leanOpts_1678_; lean_object* v_forwardedArgs_1679_; uint8_t v_printPrefix_1680_; uint8_t v_printLibDir_1681_; uint8_t v_useStdin_1682_; uint8_t v_onlyDeps_1683_; uint8_t v_onlySrcDeps_1684_; uint8_t v_depsJson_1685_; lean_object* v_opts_1686_; uint32_t v_trustLevel_1687_; uint32_t v_numThreads_1688_; lean_object* v_rootDir_x3f_1689_; lean_object* v_setupFileName_x3f_1690_; lean_object* v_oleanFileName_x3f_1691_; lean_object* v_ileanFileName_x3f_1692_; lean_object* v_cFileName_x3f_1693_; lean_object* v_bcFileName_x3f_1694_; uint8_t v_jsonOutput_1695_; lean_object* v_errorOnKinds_1696_; uint8_t v_printStats_1697_; uint8_t v_run_1698_; lean_object* v_incrSaveFileName_x3f_1699_; lean_object* v_incrLoadFileName_x3f_1700_; lean_object* v_incrHeaderSaveFileName_x3f_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1710_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_1678_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1679_ = lean_ctor_get(v_opts_941_, 1);
v_printPrefix_1680_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_1681_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_1682_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_1683_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1684_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_1685_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_1686_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1687_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_1688_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1689_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1690_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1691_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1692_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1693_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1694_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1695_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_1696_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1697_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_1698_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1699_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_1700_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_1701_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1703_ = v_opts_941_;
v_isShared_1704_ = v_isSharedCheck_1710_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1701_);
lean_inc(v_incrLoadFileName_x3f_1700_);
lean_inc(v_incrSaveFileName_x3f_1699_);
lean_inc(v_errorOnKinds_1696_);
lean_inc(v_bcFileName_x3f_1694_);
lean_inc(v_cFileName_x3f_1693_);
lean_inc(v_ileanFileName_x3f_1692_);
lean_inc(v_oleanFileName_x3f_1691_);
lean_inc(v_setupFileName_x3f_1690_);
lean_inc(v_rootDir_x3f_1689_);
lean_inc(v_opts_1686_);
lean_inc(v_forwardedArgs_1679_);
lean_inc(v_leanOpts_1678_);
lean_dec(v_opts_941_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1710_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
uint8_t v___x_1705_; lean_object* v___x_1707_; 
v___x_1705_ = 2;
if (v_isShared_1704_ == 0)
{
v___x_1707_ = v___x_1703_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_leanOpts_1678_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v_forwardedArgs_1679_);
lean_ctor_set(v_reuseFailAlloc_1709_, 2, v_opts_1686_);
lean_ctor_set(v_reuseFailAlloc_1709_, 3, v_rootDir_x3f_1689_);
lean_ctor_set(v_reuseFailAlloc_1709_, 4, v_setupFileName_x3f_1690_);
lean_ctor_set(v_reuseFailAlloc_1709_, 5, v_oleanFileName_x3f_1691_);
lean_ctor_set(v_reuseFailAlloc_1709_, 6, v_ileanFileName_x3f_1692_);
lean_ctor_set(v_reuseFailAlloc_1709_, 7, v_cFileName_x3f_1693_);
lean_ctor_set(v_reuseFailAlloc_1709_, 8, v_bcFileName_x3f_1694_);
lean_ctor_set(v_reuseFailAlloc_1709_, 9, v_errorOnKinds_1696_);
lean_ctor_set(v_reuseFailAlloc_1709_, 10, v_incrSaveFileName_x3f_1699_);
lean_ctor_set(v_reuseFailAlloc_1709_, 11, v_incrLoadFileName_x3f_1700_);
lean_ctor_set(v_reuseFailAlloc_1709_, 12, v_incrHeaderSaveFileName_x3f_1701_);
lean_ctor_set_uint8(v_reuseFailAlloc_1709_, sizeof(void*)*13 + 9, v_printPrefix_1680_);
lean_ctor_set_uint8(v_reuseFailAlloc_1709_, sizeof(void*)*13 + 10, v_printLibDir_1681_);
lean_ctor_set_uint8(v_reuseFailAlloc_1709_, sizeof(void*)*13 + 11, v_useStdin_1682_);
lean_ctor_set_uint8(v_reuseFailAlloc_1709_, sizeof(void*)*13 + 12, v_onlyDeps_1683_);
lean_ctor_set_uint8(v_reuseFailAlloc_1709_, sizeof(void*)*13 + 13, v_onlySrcDeps_1684_);
lean_ctor_set_uint8(v_reuseFailAlloc_1709_, sizeof(void*)*13 + 14, v_depsJson_1685_);
lean_ctor_set_uint32(v_reuseFailAlloc_1709_, sizeof(void*)*13, v_trustLevel_1687_);
lean_ctor_set_uint32(v_reuseFailAlloc_1709_, sizeof(void*)*13 + 4, v_numThreads_1688_);
lean_ctor_set_uint8(v_reuseFailAlloc_1709_, sizeof(void*)*13 + 15, v_jsonOutput_1695_);
lean_ctor_set_uint8(v_reuseFailAlloc_1709_, sizeof(void*)*13 + 16, v_printStats_1697_);
lean_ctor_set_uint8(v_reuseFailAlloc_1709_, sizeof(void*)*13 + 17, v_run_1698_);
v___x_1707_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1708_; 
lean_ctor_set_uint8(v___x_1707_, sizeof(void*)*13 + 8, v___x_1705_);
v___x_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
return v___x_1708_;
}
}
}
}
else
{
lean_object* v_leanOpts_1711_; lean_object* v_forwardedArgs_1712_; uint8_t v_printPrefix_1713_; uint8_t v_printLibDir_1714_; uint8_t v_useStdin_1715_; uint8_t v_onlyDeps_1716_; uint8_t v_onlySrcDeps_1717_; uint8_t v_depsJson_1718_; lean_object* v_opts_1719_; uint32_t v_trustLevel_1720_; uint32_t v_numThreads_1721_; lean_object* v_rootDir_x3f_1722_; lean_object* v_setupFileName_x3f_1723_; lean_object* v_oleanFileName_x3f_1724_; lean_object* v_ileanFileName_x3f_1725_; lean_object* v_cFileName_x3f_1726_; lean_object* v_bcFileName_x3f_1727_; uint8_t v_jsonOutput_1728_; lean_object* v_errorOnKinds_1729_; uint8_t v_printStats_1730_; uint8_t v_run_1731_; lean_object* v_incrSaveFileName_x3f_1732_; lean_object* v_incrLoadFileName_x3f_1733_; lean_object* v_incrHeaderSaveFileName_x3f_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1743_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_1711_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1712_ = lean_ctor_get(v_opts_941_, 1);
v_printPrefix_1713_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_1714_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_1715_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_1716_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1717_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_1718_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_1719_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1720_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_1721_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1722_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1723_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1724_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1725_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1726_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1727_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1728_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_1729_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1730_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_1731_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1732_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_1733_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_1734_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1736_ = v_opts_941_;
v_isShared_1737_ = v_isSharedCheck_1743_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1734_);
lean_inc(v_incrLoadFileName_x3f_1733_);
lean_inc(v_incrSaveFileName_x3f_1732_);
lean_inc(v_errorOnKinds_1729_);
lean_inc(v_bcFileName_x3f_1727_);
lean_inc(v_cFileName_x3f_1726_);
lean_inc(v_ileanFileName_x3f_1725_);
lean_inc(v_oleanFileName_x3f_1724_);
lean_inc(v_setupFileName_x3f_1723_);
lean_inc(v_rootDir_x3f_1722_);
lean_inc(v_opts_1719_);
lean_inc(v_forwardedArgs_1712_);
lean_inc(v_leanOpts_1711_);
lean_dec(v_opts_941_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1743_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
uint8_t v___x_1738_; lean_object* v___x_1740_; 
v___x_1738_ = 1;
if (v_isShared_1737_ == 0)
{
v___x_1740_ = v___x_1736_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_leanOpts_1711_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_forwardedArgs_1712_);
lean_ctor_set(v_reuseFailAlloc_1742_, 2, v_opts_1719_);
lean_ctor_set(v_reuseFailAlloc_1742_, 3, v_rootDir_x3f_1722_);
lean_ctor_set(v_reuseFailAlloc_1742_, 4, v_setupFileName_x3f_1723_);
lean_ctor_set(v_reuseFailAlloc_1742_, 5, v_oleanFileName_x3f_1724_);
lean_ctor_set(v_reuseFailAlloc_1742_, 6, v_ileanFileName_x3f_1725_);
lean_ctor_set(v_reuseFailAlloc_1742_, 7, v_cFileName_x3f_1726_);
lean_ctor_set(v_reuseFailAlloc_1742_, 8, v_bcFileName_x3f_1727_);
lean_ctor_set(v_reuseFailAlloc_1742_, 9, v_errorOnKinds_1729_);
lean_ctor_set(v_reuseFailAlloc_1742_, 10, v_incrSaveFileName_x3f_1732_);
lean_ctor_set(v_reuseFailAlloc_1742_, 11, v_incrLoadFileName_x3f_1733_);
lean_ctor_set(v_reuseFailAlloc_1742_, 12, v_incrHeaderSaveFileName_x3f_1734_);
lean_ctor_set_uint8(v_reuseFailAlloc_1742_, sizeof(void*)*13 + 9, v_printPrefix_1713_);
lean_ctor_set_uint8(v_reuseFailAlloc_1742_, sizeof(void*)*13 + 10, v_printLibDir_1714_);
lean_ctor_set_uint8(v_reuseFailAlloc_1742_, sizeof(void*)*13 + 11, v_useStdin_1715_);
lean_ctor_set_uint8(v_reuseFailAlloc_1742_, sizeof(void*)*13 + 12, v_onlyDeps_1716_);
lean_ctor_set_uint8(v_reuseFailAlloc_1742_, sizeof(void*)*13 + 13, v_onlySrcDeps_1717_);
lean_ctor_set_uint8(v_reuseFailAlloc_1742_, sizeof(void*)*13 + 14, v_depsJson_1718_);
lean_ctor_set_uint32(v_reuseFailAlloc_1742_, sizeof(void*)*13, v_trustLevel_1720_);
lean_ctor_set_uint32(v_reuseFailAlloc_1742_, sizeof(void*)*13 + 4, v_numThreads_1721_);
lean_ctor_set_uint8(v_reuseFailAlloc_1742_, sizeof(void*)*13 + 15, v_jsonOutput_1728_);
lean_ctor_set_uint8(v_reuseFailAlloc_1742_, sizeof(void*)*13 + 16, v_printStats_1730_);
lean_ctor_set_uint8(v_reuseFailAlloc_1742_, sizeof(void*)*13 + 17, v_run_1731_);
v___x_1740_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v___x_1741_; 
lean_ctor_set_uint8(v___x_1740_, sizeof(void*)*13 + 8, v___x_1738_);
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
return v___x_1741_;
}
}
}
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11));
v___x_1745_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1744_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v_leanOpts_1747_; lean_object* v_forwardedArgs_1748_; uint8_t v_component_1749_; uint8_t v_printPrefix_1750_; uint8_t v_printLibDir_1751_; uint8_t v_useStdin_1752_; uint8_t v_onlyDeps_1753_; uint8_t v_onlySrcDeps_1754_; uint8_t v_depsJson_1755_; lean_object* v_opts_1756_; uint32_t v_trustLevel_1757_; uint32_t v_numThreads_1758_; lean_object* v_rootDir_x3f_1759_; lean_object* v_setupFileName_x3f_1760_; lean_object* v_oleanFileName_x3f_1761_; lean_object* v_ileanFileName_x3f_1762_; lean_object* v_cFileName_x3f_1763_; lean_object* v_bcFileName_x3f_1764_; uint8_t v_jsonOutput_1765_; lean_object* v_errorOnKinds_1766_; uint8_t v_printStats_1767_; uint8_t v_run_1768_; lean_object* v_incrSaveFileName_x3f_1769_; lean_object* v_incrLoadFileName_x3f_1770_; lean_object* v_incrHeaderSaveFileName_x3f_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1796_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1746_);
lean_dec_ref_known(v___x_1745_, 1);
v_leanOpts_1747_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1748_ = lean_ctor_get(v_opts_941_, 1);
v_component_1749_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_1750_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_1751_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_1752_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_1753_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1754_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_1755_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_1756_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1757_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_1758_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1759_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1760_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1761_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1762_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1763_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1764_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1765_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_1766_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1767_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_1768_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1769_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_1770_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_1771_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1773_ = v_opts_941_;
v_isShared_1774_ = v_isSharedCheck_1796_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1771_);
lean_inc(v_incrLoadFileName_x3f_1770_);
lean_inc(v_incrSaveFileName_x3f_1769_);
lean_inc(v_errorOnKinds_1766_);
lean_inc(v_bcFileName_x3f_1764_);
lean_inc(v_cFileName_x3f_1763_);
lean_inc(v_ileanFileName_x3f_1762_);
lean_inc(v_oleanFileName_x3f_1761_);
lean_inc(v_setupFileName_x3f_1760_);
lean_inc(v_rootDir_x3f_1759_);
lean_inc(v_opts_1756_);
lean_inc(v_forwardedArgs_1748_);
lean_inc(v_leanOpts_1747_);
lean_dec(v_opts_941_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1796_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; 
lean_inc(v_a_1746_);
v___x_1775_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_leanOpts_1747_, v_a_1746_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1789_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1789_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1789_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1780_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12));
v___x_1781_ = lean_string_append(v___x_1780_, v_a_1746_);
lean_dec(v_a_1746_);
v___x_1782_ = lean_array_push(v_forwardedArgs_1748_, v___x_1781_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 1, v___x_1782_);
lean_ctor_set(v___x_1773_, 0, v_a_1776_);
v___x_1784_ = v___x_1773_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1776_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1788_, 2, v_opts_1756_);
lean_ctor_set(v_reuseFailAlloc_1788_, 3, v_rootDir_x3f_1759_);
lean_ctor_set(v_reuseFailAlloc_1788_, 4, v_setupFileName_x3f_1760_);
lean_ctor_set(v_reuseFailAlloc_1788_, 5, v_oleanFileName_x3f_1761_);
lean_ctor_set(v_reuseFailAlloc_1788_, 6, v_ileanFileName_x3f_1762_);
lean_ctor_set(v_reuseFailAlloc_1788_, 7, v_cFileName_x3f_1763_);
lean_ctor_set(v_reuseFailAlloc_1788_, 8, v_bcFileName_x3f_1764_);
lean_ctor_set(v_reuseFailAlloc_1788_, 9, v_errorOnKinds_1766_);
lean_ctor_set(v_reuseFailAlloc_1788_, 10, v_incrSaveFileName_x3f_1769_);
lean_ctor_set(v_reuseFailAlloc_1788_, 11, v_incrLoadFileName_x3f_1770_);
lean_ctor_set(v_reuseFailAlloc_1788_, 12, v_incrHeaderSaveFileName_x3f_1771_);
lean_ctor_set_uint8(v_reuseFailAlloc_1788_, sizeof(void*)*13 + 8, v_component_1749_);
lean_ctor_set_uint8(v_reuseFailAlloc_1788_, sizeof(void*)*13 + 9, v_printPrefix_1750_);
lean_ctor_set_uint8(v_reuseFailAlloc_1788_, sizeof(void*)*13 + 10, v_printLibDir_1751_);
lean_ctor_set_uint8(v_reuseFailAlloc_1788_, sizeof(void*)*13 + 11, v_useStdin_1752_);
lean_ctor_set_uint8(v_reuseFailAlloc_1788_, sizeof(void*)*13 + 12, v_onlyDeps_1753_);
lean_ctor_set_uint8(v_reuseFailAlloc_1788_, sizeof(void*)*13 + 13, v_onlySrcDeps_1754_);
lean_ctor_set_uint8(v_reuseFailAlloc_1788_, sizeof(void*)*13 + 14, v_depsJson_1755_);
lean_ctor_set_uint32(v_reuseFailAlloc_1788_, sizeof(void*)*13, v_trustLevel_1757_);
lean_ctor_set_uint32(v_reuseFailAlloc_1788_, sizeof(void*)*13 + 4, v_numThreads_1758_);
lean_ctor_set_uint8(v_reuseFailAlloc_1788_, sizeof(void*)*13 + 15, v_jsonOutput_1765_);
lean_ctor_set_uint8(v_reuseFailAlloc_1788_, sizeof(void*)*13 + 16, v_printStats_1767_);
lean_ctor_set_uint8(v_reuseFailAlloc_1788_, sizeof(void*)*13 + 17, v_run_1768_);
v___x_1784_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
lean_object* v___x_1786_; 
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1784_);
v___x_1786_ = v___x_1778_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
lean_del_object(v___x_1773_);
lean_dec(v_incrHeaderSaveFileName_x3f_1771_);
lean_dec(v_incrLoadFileName_x3f_1770_);
lean_dec(v_incrSaveFileName_x3f_1769_);
lean_dec_ref(v_errorOnKinds_1766_);
lean_dec(v_bcFileName_x3f_1764_);
lean_dec(v_cFileName_x3f_1763_);
lean_dec(v_ileanFileName_x3f_1762_);
lean_dec(v_oleanFileName_x3f_1761_);
lean_dec(v_setupFileName_x3f_1760_);
lean_dec(v_rootDir_x3f_1759_);
lean_dec_ref(v_opts_1756_);
lean_dec_ref(v_forwardedArgs_1748_);
lean_dec(v_a_1746_);
v_a_1790_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1790_);
lean_dec_ref_known(v___x_1775_, 1);
v___x_1794_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1795_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1794_);
lean_dec_ref(v___x_1795_);
goto v___jp_1791_;
v___jp_1791_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = lean_io_error_to_string(v_a_1790_);
v___x_1793_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1792_);
lean_dec_ref(v___x_1793_);
goto v___jp_1017_;
}
}
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
lean_dec_ref(v_opts_941_);
v_a_1797_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1797_);
lean_dec_ref_known(v___x_1745_, 1);
v___x_1801_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1802_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1801_);
lean_dec_ref(v___x_1802_);
goto v___jp_1798_;
v___jp_1798_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = lean_io_error_to_string(v_a_1797_);
v___x_1800_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1799_);
lean_dec_ref(v___x_1800_);
goto v___jp_1115_;
}
}
}
}
else
{
lean_object* v_leanOpts_1803_; lean_object* v_forwardedArgs_1804_; uint8_t v_component_1805_; uint8_t v_printPrefix_1806_; uint8_t v_useStdin_1807_; uint8_t v_onlyDeps_1808_; uint8_t v_onlySrcDeps_1809_; uint8_t v_depsJson_1810_; lean_object* v_opts_1811_; uint32_t v_trustLevel_1812_; uint32_t v_numThreads_1813_; lean_object* v_rootDir_x3f_1814_; lean_object* v_setupFileName_x3f_1815_; lean_object* v_oleanFileName_x3f_1816_; lean_object* v_ileanFileName_x3f_1817_; lean_object* v_cFileName_x3f_1818_; lean_object* v_bcFileName_x3f_1819_; uint8_t v_jsonOutput_1820_; lean_object* v_errorOnKinds_1821_; uint8_t v_printStats_1822_; uint8_t v_run_1823_; lean_object* v_incrSaveFileName_x3f_1824_; lean_object* v_incrLoadFileName_x3f_1825_; lean_object* v_incrHeaderSaveFileName_x3f_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1834_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_1803_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1804_ = lean_ctor_get(v_opts_941_, 1);
v_component_1805_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_1806_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_useStdin_1807_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_1808_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1809_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_1810_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_1811_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1812_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_1813_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1814_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1815_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1816_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1817_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1818_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1819_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1820_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_1821_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1822_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_1823_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1824_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_1825_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_1826_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_1834_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1828_ = v_opts_941_;
v_isShared_1829_ = v_isSharedCheck_1834_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1826_);
lean_inc(v_incrLoadFileName_x3f_1825_);
lean_inc(v_incrSaveFileName_x3f_1824_);
lean_inc(v_errorOnKinds_1821_);
lean_inc(v_bcFileName_x3f_1819_);
lean_inc(v_cFileName_x3f_1818_);
lean_inc(v_ileanFileName_x3f_1817_);
lean_inc(v_oleanFileName_x3f_1816_);
lean_inc(v_setupFileName_x3f_1815_);
lean_inc(v_rootDir_x3f_1814_);
lean_inc(v_opts_1811_);
lean_inc(v_forwardedArgs_1804_);
lean_inc(v_leanOpts_1803_);
lean_dec(v_opts_941_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1834_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_leanOpts_1803_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v_forwardedArgs_1804_);
lean_ctor_set(v_reuseFailAlloc_1833_, 2, v_opts_1811_);
lean_ctor_set(v_reuseFailAlloc_1833_, 3, v_rootDir_x3f_1814_);
lean_ctor_set(v_reuseFailAlloc_1833_, 4, v_setupFileName_x3f_1815_);
lean_ctor_set(v_reuseFailAlloc_1833_, 5, v_oleanFileName_x3f_1816_);
lean_ctor_set(v_reuseFailAlloc_1833_, 6, v_ileanFileName_x3f_1817_);
lean_ctor_set(v_reuseFailAlloc_1833_, 7, v_cFileName_x3f_1818_);
lean_ctor_set(v_reuseFailAlloc_1833_, 8, v_bcFileName_x3f_1819_);
lean_ctor_set(v_reuseFailAlloc_1833_, 9, v_errorOnKinds_1821_);
lean_ctor_set(v_reuseFailAlloc_1833_, 10, v_incrSaveFileName_x3f_1824_);
lean_ctor_set(v_reuseFailAlloc_1833_, 11, v_incrLoadFileName_x3f_1825_);
lean_ctor_set(v_reuseFailAlloc_1833_, 12, v_incrHeaderSaveFileName_x3f_1826_);
lean_ctor_set_uint8(v_reuseFailAlloc_1833_, sizeof(void*)*13 + 8, v_component_1805_);
lean_ctor_set_uint8(v_reuseFailAlloc_1833_, sizeof(void*)*13 + 9, v_printPrefix_1806_);
lean_ctor_set_uint8(v_reuseFailAlloc_1833_, sizeof(void*)*13 + 11, v_useStdin_1807_);
lean_ctor_set_uint8(v_reuseFailAlloc_1833_, sizeof(void*)*13 + 12, v_onlyDeps_1808_);
lean_ctor_set_uint8(v_reuseFailAlloc_1833_, sizeof(void*)*13 + 13, v_onlySrcDeps_1809_);
lean_ctor_set_uint8(v_reuseFailAlloc_1833_, sizeof(void*)*13 + 14, v_depsJson_1810_);
lean_ctor_set_uint32(v_reuseFailAlloc_1833_, sizeof(void*)*13, v_trustLevel_1812_);
lean_ctor_set_uint32(v_reuseFailAlloc_1833_, sizeof(void*)*13 + 4, v_numThreads_1813_);
lean_ctor_set_uint8(v_reuseFailAlloc_1833_, sizeof(void*)*13 + 15, v_jsonOutput_1820_);
lean_ctor_set_uint8(v_reuseFailAlloc_1833_, sizeof(void*)*13 + 16, v_printStats_1822_);
lean_ctor_set_uint8(v_reuseFailAlloc_1833_, sizeof(void*)*13 + 17, v_run_1823_);
v___x_1831_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
lean_object* v___x_1832_; 
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*13 + 10, v___x_1214_);
v___x_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
return v___x_1832_;
}
}
}
}
else
{
lean_object* v_leanOpts_1835_; lean_object* v_forwardedArgs_1836_; uint8_t v_component_1837_; uint8_t v_printLibDir_1838_; uint8_t v_useStdin_1839_; uint8_t v_onlyDeps_1840_; uint8_t v_onlySrcDeps_1841_; uint8_t v_depsJson_1842_; lean_object* v_opts_1843_; uint32_t v_trustLevel_1844_; uint32_t v_numThreads_1845_; lean_object* v_rootDir_x3f_1846_; lean_object* v_setupFileName_x3f_1847_; lean_object* v_oleanFileName_x3f_1848_; lean_object* v_ileanFileName_x3f_1849_; lean_object* v_cFileName_x3f_1850_; lean_object* v_bcFileName_x3f_1851_; uint8_t v_jsonOutput_1852_; lean_object* v_errorOnKinds_1853_; uint8_t v_printStats_1854_; uint8_t v_run_1855_; lean_object* v_incrSaveFileName_x3f_1856_; lean_object* v_incrLoadFileName_x3f_1857_; lean_object* v_incrHeaderSaveFileName_x3f_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1866_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_1835_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1836_ = lean_ctor_get(v_opts_941_, 1);
v_component_1837_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printLibDir_1838_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_1839_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_1840_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1841_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_1842_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_1843_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1844_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_1845_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1846_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1847_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1848_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1849_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1850_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1851_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1852_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_1853_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1854_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_1855_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1856_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_1857_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_1858_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_1866_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1860_ = v_opts_941_;
v_isShared_1861_ = v_isSharedCheck_1866_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1858_);
lean_inc(v_incrLoadFileName_x3f_1857_);
lean_inc(v_incrSaveFileName_x3f_1856_);
lean_inc(v_errorOnKinds_1853_);
lean_inc(v_bcFileName_x3f_1851_);
lean_inc(v_cFileName_x3f_1850_);
lean_inc(v_ileanFileName_x3f_1849_);
lean_inc(v_oleanFileName_x3f_1848_);
lean_inc(v_setupFileName_x3f_1847_);
lean_inc(v_rootDir_x3f_1846_);
lean_inc(v_opts_1843_);
lean_inc(v_forwardedArgs_1836_);
lean_inc(v_leanOpts_1835_);
lean_dec(v_opts_941_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1866_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_leanOpts_1835_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v_forwardedArgs_1836_);
lean_ctor_set(v_reuseFailAlloc_1865_, 2, v_opts_1843_);
lean_ctor_set(v_reuseFailAlloc_1865_, 3, v_rootDir_x3f_1846_);
lean_ctor_set(v_reuseFailAlloc_1865_, 4, v_setupFileName_x3f_1847_);
lean_ctor_set(v_reuseFailAlloc_1865_, 5, v_oleanFileName_x3f_1848_);
lean_ctor_set(v_reuseFailAlloc_1865_, 6, v_ileanFileName_x3f_1849_);
lean_ctor_set(v_reuseFailAlloc_1865_, 7, v_cFileName_x3f_1850_);
lean_ctor_set(v_reuseFailAlloc_1865_, 8, v_bcFileName_x3f_1851_);
lean_ctor_set(v_reuseFailAlloc_1865_, 9, v_errorOnKinds_1853_);
lean_ctor_set(v_reuseFailAlloc_1865_, 10, v_incrSaveFileName_x3f_1856_);
lean_ctor_set(v_reuseFailAlloc_1865_, 11, v_incrLoadFileName_x3f_1857_);
lean_ctor_set(v_reuseFailAlloc_1865_, 12, v_incrHeaderSaveFileName_x3f_1858_);
lean_ctor_set_uint8(v_reuseFailAlloc_1865_, sizeof(void*)*13 + 8, v_component_1837_);
lean_ctor_set_uint8(v_reuseFailAlloc_1865_, sizeof(void*)*13 + 10, v_printLibDir_1838_);
lean_ctor_set_uint8(v_reuseFailAlloc_1865_, sizeof(void*)*13 + 11, v_useStdin_1839_);
lean_ctor_set_uint8(v_reuseFailAlloc_1865_, sizeof(void*)*13 + 12, v_onlyDeps_1840_);
lean_ctor_set_uint8(v_reuseFailAlloc_1865_, sizeof(void*)*13 + 13, v_onlySrcDeps_1841_);
lean_ctor_set_uint8(v_reuseFailAlloc_1865_, sizeof(void*)*13 + 14, v_depsJson_1842_);
lean_ctor_set_uint32(v_reuseFailAlloc_1865_, sizeof(void*)*13, v_trustLevel_1844_);
lean_ctor_set_uint32(v_reuseFailAlloc_1865_, sizeof(void*)*13 + 4, v_numThreads_1845_);
lean_ctor_set_uint8(v_reuseFailAlloc_1865_, sizeof(void*)*13 + 15, v_jsonOutput_1852_);
lean_ctor_set_uint8(v_reuseFailAlloc_1865_, sizeof(void*)*13 + 16, v_printStats_1854_);
lean_ctor_set_uint8(v_reuseFailAlloc_1865_, sizeof(void*)*13 + 17, v_run_1855_);
v___x_1863_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1864_; 
lean_ctor_set_uint8(v___x_1863_, sizeof(void*)*13 + 9, v___x_1212_);
v___x_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
return v___x_1864_;
}
}
}
}
else
{
lean_object* v_leanOpts_1867_; lean_object* v_forwardedArgs_1868_; uint8_t v_component_1869_; uint8_t v_printPrefix_1870_; uint8_t v_printLibDir_1871_; uint8_t v_useStdin_1872_; uint8_t v_onlyDeps_1873_; uint8_t v_onlySrcDeps_1874_; uint8_t v_depsJson_1875_; lean_object* v_opts_1876_; uint32_t v_trustLevel_1877_; uint32_t v_numThreads_1878_; lean_object* v_rootDir_x3f_1879_; lean_object* v_setupFileName_x3f_1880_; lean_object* v_oleanFileName_x3f_1881_; lean_object* v_ileanFileName_x3f_1882_; lean_object* v_cFileName_x3f_1883_; lean_object* v_bcFileName_x3f_1884_; uint8_t v_jsonOutput_1885_; lean_object* v_errorOnKinds_1886_; uint8_t v_run_1887_; lean_object* v_incrSaveFileName_x3f_1888_; lean_object* v_incrLoadFileName_x3f_1889_; lean_object* v_incrHeaderSaveFileName_x3f_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1898_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_1867_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1868_ = lean_ctor_get(v_opts_941_, 1);
v_component_1869_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_1870_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_1871_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_1872_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_1873_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1874_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_1875_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_1876_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1877_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_1878_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1879_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1880_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1881_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1882_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1883_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1884_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1885_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_1886_ = lean_ctor_get(v_opts_941_, 9);
v_run_1887_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1888_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_1889_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_1890_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_1898_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1892_ = v_opts_941_;
v_isShared_1893_ = v_isSharedCheck_1898_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1890_);
lean_inc(v_incrLoadFileName_x3f_1889_);
lean_inc(v_incrSaveFileName_x3f_1888_);
lean_inc(v_errorOnKinds_1886_);
lean_inc(v_bcFileName_x3f_1884_);
lean_inc(v_cFileName_x3f_1883_);
lean_inc(v_ileanFileName_x3f_1882_);
lean_inc(v_oleanFileName_x3f_1881_);
lean_inc(v_setupFileName_x3f_1880_);
lean_inc(v_rootDir_x3f_1879_);
lean_inc(v_opts_1876_);
lean_inc(v_forwardedArgs_1868_);
lean_inc(v_leanOpts_1867_);
lean_dec(v_opts_941_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1898_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_leanOpts_1867_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v_forwardedArgs_1868_);
lean_ctor_set(v_reuseFailAlloc_1897_, 2, v_opts_1876_);
lean_ctor_set(v_reuseFailAlloc_1897_, 3, v_rootDir_x3f_1879_);
lean_ctor_set(v_reuseFailAlloc_1897_, 4, v_setupFileName_x3f_1880_);
lean_ctor_set(v_reuseFailAlloc_1897_, 5, v_oleanFileName_x3f_1881_);
lean_ctor_set(v_reuseFailAlloc_1897_, 6, v_ileanFileName_x3f_1882_);
lean_ctor_set(v_reuseFailAlloc_1897_, 7, v_cFileName_x3f_1883_);
lean_ctor_set(v_reuseFailAlloc_1897_, 8, v_bcFileName_x3f_1884_);
lean_ctor_set(v_reuseFailAlloc_1897_, 9, v_errorOnKinds_1886_);
lean_ctor_set(v_reuseFailAlloc_1897_, 10, v_incrSaveFileName_x3f_1888_);
lean_ctor_set(v_reuseFailAlloc_1897_, 11, v_incrLoadFileName_x3f_1889_);
lean_ctor_set(v_reuseFailAlloc_1897_, 12, v_incrHeaderSaveFileName_x3f_1890_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, sizeof(void*)*13 + 8, v_component_1869_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, sizeof(void*)*13 + 9, v_printPrefix_1870_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, sizeof(void*)*13 + 10, v_printLibDir_1871_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, sizeof(void*)*13 + 11, v_useStdin_1872_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, sizeof(void*)*13 + 12, v_onlyDeps_1873_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, sizeof(void*)*13 + 13, v_onlySrcDeps_1874_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, sizeof(void*)*13 + 14, v_depsJson_1875_);
lean_ctor_set_uint32(v_reuseFailAlloc_1897_, sizeof(void*)*13, v_trustLevel_1877_);
lean_ctor_set_uint32(v_reuseFailAlloc_1897_, sizeof(void*)*13 + 4, v_numThreads_1878_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, sizeof(void*)*13 + 15, v_jsonOutput_1885_);
lean_ctor_set_uint8(v_reuseFailAlloc_1897_, sizeof(void*)*13 + 17, v_run_1887_);
v___x_1895_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1896_; 
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*13 + 16, v___x_1210_);
v___x_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
return v___x_1896_;
}
}
}
}
else
{
lean_object* v_leanOpts_1899_; lean_object* v_forwardedArgs_1900_; uint8_t v_component_1901_; uint8_t v_printPrefix_1902_; uint8_t v_printLibDir_1903_; uint8_t v_useStdin_1904_; uint8_t v_onlyDeps_1905_; uint8_t v_onlySrcDeps_1906_; uint8_t v_depsJson_1907_; lean_object* v_opts_1908_; uint32_t v_trustLevel_1909_; uint32_t v_numThreads_1910_; lean_object* v_rootDir_x3f_1911_; lean_object* v_setupFileName_x3f_1912_; lean_object* v_oleanFileName_x3f_1913_; lean_object* v_ileanFileName_x3f_1914_; lean_object* v_cFileName_x3f_1915_; lean_object* v_bcFileName_x3f_1916_; lean_object* v_errorOnKinds_1917_; uint8_t v_printStats_1918_; uint8_t v_run_1919_; lean_object* v_incrSaveFileName_x3f_1920_; lean_object* v_incrLoadFileName_x3f_1921_; lean_object* v_incrHeaderSaveFileName_x3f_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1930_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_1899_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1900_ = lean_ctor_get(v_opts_941_, 1);
v_component_1901_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_1902_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_1903_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_1904_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_1905_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1906_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_1907_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_1908_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1909_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_1910_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1911_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1912_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1913_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1914_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1915_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1916_ = lean_ctor_get(v_opts_941_, 8);
v_errorOnKinds_1917_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1918_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_1919_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1920_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_1921_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_1922_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_1930_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1924_ = v_opts_941_;
v_isShared_1925_ = v_isSharedCheck_1930_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1922_);
lean_inc(v_incrLoadFileName_x3f_1921_);
lean_inc(v_incrSaveFileName_x3f_1920_);
lean_inc(v_errorOnKinds_1917_);
lean_inc(v_bcFileName_x3f_1916_);
lean_inc(v_cFileName_x3f_1915_);
lean_inc(v_ileanFileName_x3f_1914_);
lean_inc(v_oleanFileName_x3f_1913_);
lean_inc(v_setupFileName_x3f_1912_);
lean_inc(v_rootDir_x3f_1911_);
lean_inc(v_opts_1908_);
lean_inc(v_forwardedArgs_1900_);
lean_inc(v_leanOpts_1899_);
lean_dec(v_opts_941_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1930_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_leanOpts_1899_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_forwardedArgs_1900_);
lean_ctor_set(v_reuseFailAlloc_1929_, 2, v_opts_1908_);
lean_ctor_set(v_reuseFailAlloc_1929_, 3, v_rootDir_x3f_1911_);
lean_ctor_set(v_reuseFailAlloc_1929_, 4, v_setupFileName_x3f_1912_);
lean_ctor_set(v_reuseFailAlloc_1929_, 5, v_oleanFileName_x3f_1913_);
lean_ctor_set(v_reuseFailAlloc_1929_, 6, v_ileanFileName_x3f_1914_);
lean_ctor_set(v_reuseFailAlloc_1929_, 7, v_cFileName_x3f_1915_);
lean_ctor_set(v_reuseFailAlloc_1929_, 8, v_bcFileName_x3f_1916_);
lean_ctor_set(v_reuseFailAlloc_1929_, 9, v_errorOnKinds_1917_);
lean_ctor_set(v_reuseFailAlloc_1929_, 10, v_incrSaveFileName_x3f_1920_);
lean_ctor_set(v_reuseFailAlloc_1929_, 11, v_incrLoadFileName_x3f_1921_);
lean_ctor_set(v_reuseFailAlloc_1929_, 12, v_incrHeaderSaveFileName_x3f_1922_);
lean_ctor_set_uint8(v_reuseFailAlloc_1929_, sizeof(void*)*13 + 8, v_component_1901_);
lean_ctor_set_uint8(v_reuseFailAlloc_1929_, sizeof(void*)*13 + 9, v_printPrefix_1902_);
lean_ctor_set_uint8(v_reuseFailAlloc_1929_, sizeof(void*)*13 + 10, v_printLibDir_1903_);
lean_ctor_set_uint8(v_reuseFailAlloc_1929_, sizeof(void*)*13 + 11, v_useStdin_1904_);
lean_ctor_set_uint8(v_reuseFailAlloc_1929_, sizeof(void*)*13 + 12, v_onlyDeps_1905_);
lean_ctor_set_uint8(v_reuseFailAlloc_1929_, sizeof(void*)*13 + 13, v_onlySrcDeps_1906_);
lean_ctor_set_uint8(v_reuseFailAlloc_1929_, sizeof(void*)*13 + 14, v_depsJson_1907_);
lean_ctor_set_uint32(v_reuseFailAlloc_1929_, sizeof(void*)*13, v_trustLevel_1909_);
lean_ctor_set_uint32(v_reuseFailAlloc_1929_, sizeof(void*)*13 + 4, v_numThreads_1910_);
lean_ctor_set_uint8(v_reuseFailAlloc_1929_, sizeof(void*)*13 + 16, v_printStats_1918_);
lean_ctor_set_uint8(v_reuseFailAlloc_1929_, sizeof(void*)*13 + 17, v_run_1919_);
v___x_1927_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1928_; 
lean_ctor_set_uint8(v___x_1927_, sizeof(void*)*13 + 15, v___x_1208_);
v___x_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
return v___x_1928_;
}
}
}
}
else
{
lean_object* v_leanOpts_1931_; lean_object* v_forwardedArgs_1932_; uint8_t v_component_1933_; uint8_t v_printPrefix_1934_; uint8_t v_printLibDir_1935_; uint8_t v_useStdin_1936_; uint8_t v_onlySrcDeps_1937_; lean_object* v_opts_1938_; uint32_t v_trustLevel_1939_; uint32_t v_numThreads_1940_; lean_object* v_rootDir_x3f_1941_; lean_object* v_setupFileName_x3f_1942_; lean_object* v_oleanFileName_x3f_1943_; lean_object* v_ileanFileName_x3f_1944_; lean_object* v_cFileName_x3f_1945_; lean_object* v_bcFileName_x3f_1946_; uint8_t v_jsonOutput_1947_; lean_object* v_errorOnKinds_1948_; uint8_t v_printStats_1949_; uint8_t v_run_1950_; lean_object* v_incrSaveFileName_x3f_1951_; lean_object* v_incrLoadFileName_x3f_1952_; lean_object* v_incrHeaderSaveFileName_x3f_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1961_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_1931_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1932_ = lean_ctor_get(v_opts_941_, 1);
v_component_1933_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_1934_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_1935_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_1936_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlySrcDeps_1937_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_opts_1938_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1939_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_1940_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1941_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1942_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1943_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1944_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1945_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1946_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1947_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_1948_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1949_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_1950_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1951_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_1952_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_1953_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_1961_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1955_ = v_opts_941_;
v_isShared_1956_ = v_isSharedCheck_1961_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1953_);
lean_inc(v_incrLoadFileName_x3f_1952_);
lean_inc(v_incrSaveFileName_x3f_1951_);
lean_inc(v_errorOnKinds_1948_);
lean_inc(v_bcFileName_x3f_1946_);
lean_inc(v_cFileName_x3f_1945_);
lean_inc(v_ileanFileName_x3f_1944_);
lean_inc(v_oleanFileName_x3f_1943_);
lean_inc(v_setupFileName_x3f_1942_);
lean_inc(v_rootDir_x3f_1941_);
lean_inc(v_opts_1938_);
lean_inc(v_forwardedArgs_1932_);
lean_inc(v_leanOpts_1931_);
lean_dec(v_opts_941_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1961_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_leanOpts_1931_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v_forwardedArgs_1932_);
lean_ctor_set(v_reuseFailAlloc_1960_, 2, v_opts_1938_);
lean_ctor_set(v_reuseFailAlloc_1960_, 3, v_rootDir_x3f_1941_);
lean_ctor_set(v_reuseFailAlloc_1960_, 4, v_setupFileName_x3f_1942_);
lean_ctor_set(v_reuseFailAlloc_1960_, 5, v_oleanFileName_x3f_1943_);
lean_ctor_set(v_reuseFailAlloc_1960_, 6, v_ileanFileName_x3f_1944_);
lean_ctor_set(v_reuseFailAlloc_1960_, 7, v_cFileName_x3f_1945_);
lean_ctor_set(v_reuseFailAlloc_1960_, 8, v_bcFileName_x3f_1946_);
lean_ctor_set(v_reuseFailAlloc_1960_, 9, v_errorOnKinds_1948_);
lean_ctor_set(v_reuseFailAlloc_1960_, 10, v_incrSaveFileName_x3f_1951_);
lean_ctor_set(v_reuseFailAlloc_1960_, 11, v_incrLoadFileName_x3f_1952_);
lean_ctor_set(v_reuseFailAlloc_1960_, 12, v_incrHeaderSaveFileName_x3f_1953_);
lean_ctor_set_uint8(v_reuseFailAlloc_1960_, sizeof(void*)*13 + 8, v_component_1933_);
lean_ctor_set_uint8(v_reuseFailAlloc_1960_, sizeof(void*)*13 + 9, v_printPrefix_1934_);
lean_ctor_set_uint8(v_reuseFailAlloc_1960_, sizeof(void*)*13 + 10, v_printLibDir_1935_);
lean_ctor_set_uint8(v_reuseFailAlloc_1960_, sizeof(void*)*13 + 11, v_useStdin_1936_);
lean_ctor_set_uint8(v_reuseFailAlloc_1960_, sizeof(void*)*13 + 13, v_onlySrcDeps_1937_);
lean_ctor_set_uint32(v_reuseFailAlloc_1960_, sizeof(void*)*13, v_trustLevel_1939_);
lean_ctor_set_uint32(v_reuseFailAlloc_1960_, sizeof(void*)*13 + 4, v_numThreads_1940_);
lean_ctor_set_uint8(v_reuseFailAlloc_1960_, sizeof(void*)*13 + 15, v_jsonOutput_1947_);
lean_ctor_set_uint8(v_reuseFailAlloc_1960_, sizeof(void*)*13 + 16, v_printStats_1949_);
lean_ctor_set_uint8(v_reuseFailAlloc_1960_, sizeof(void*)*13 + 17, v_run_1950_);
v___x_1958_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
lean_object* v___x_1959_; 
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*13 + 12, v___x_1206_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*13 + 14, v___x_1206_);
v___x_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1958_);
return v___x_1959_;
}
}
}
}
else
{
lean_object* v_leanOpts_1962_; lean_object* v_forwardedArgs_1963_; uint8_t v_component_1964_; uint8_t v_printPrefix_1965_; uint8_t v_printLibDir_1966_; uint8_t v_useStdin_1967_; uint8_t v_onlyDeps_1968_; uint8_t v_depsJson_1969_; lean_object* v_opts_1970_; uint32_t v_trustLevel_1971_; uint32_t v_numThreads_1972_; lean_object* v_rootDir_x3f_1973_; lean_object* v_setupFileName_x3f_1974_; lean_object* v_oleanFileName_x3f_1975_; lean_object* v_ileanFileName_x3f_1976_; lean_object* v_cFileName_x3f_1977_; lean_object* v_bcFileName_x3f_1978_; uint8_t v_jsonOutput_1979_; lean_object* v_errorOnKinds_1980_; uint8_t v_printStats_1981_; uint8_t v_run_1982_; lean_object* v_incrSaveFileName_x3f_1983_; lean_object* v_incrLoadFileName_x3f_1984_; lean_object* v_incrHeaderSaveFileName_x3f_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1993_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_1962_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1963_ = lean_ctor_get(v_opts_941_, 1);
v_component_1964_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_1965_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_1966_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_1967_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_1968_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_depsJson_1969_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_1970_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_1971_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_1972_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1973_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_1974_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_1975_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_1976_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_1977_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_1978_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_1979_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_1980_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_1981_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_1982_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1983_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_1984_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_1985_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_1993_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1987_ = v_opts_941_;
v_isShared_1988_ = v_isSharedCheck_1993_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1985_);
lean_inc(v_incrLoadFileName_x3f_1984_);
lean_inc(v_incrSaveFileName_x3f_1983_);
lean_inc(v_errorOnKinds_1980_);
lean_inc(v_bcFileName_x3f_1978_);
lean_inc(v_cFileName_x3f_1977_);
lean_inc(v_ileanFileName_x3f_1976_);
lean_inc(v_oleanFileName_x3f_1975_);
lean_inc(v_setupFileName_x3f_1974_);
lean_inc(v_rootDir_x3f_1973_);
lean_inc(v_opts_1970_);
lean_inc(v_forwardedArgs_1963_);
lean_inc(v_leanOpts_1962_);
lean_dec(v_opts_941_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1993_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_leanOpts_1962_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_forwardedArgs_1963_);
lean_ctor_set(v_reuseFailAlloc_1992_, 2, v_opts_1970_);
lean_ctor_set(v_reuseFailAlloc_1992_, 3, v_rootDir_x3f_1973_);
lean_ctor_set(v_reuseFailAlloc_1992_, 4, v_setupFileName_x3f_1974_);
lean_ctor_set(v_reuseFailAlloc_1992_, 5, v_oleanFileName_x3f_1975_);
lean_ctor_set(v_reuseFailAlloc_1992_, 6, v_ileanFileName_x3f_1976_);
lean_ctor_set(v_reuseFailAlloc_1992_, 7, v_cFileName_x3f_1977_);
lean_ctor_set(v_reuseFailAlloc_1992_, 8, v_bcFileName_x3f_1978_);
lean_ctor_set(v_reuseFailAlloc_1992_, 9, v_errorOnKinds_1980_);
lean_ctor_set(v_reuseFailAlloc_1992_, 10, v_incrSaveFileName_x3f_1983_);
lean_ctor_set(v_reuseFailAlloc_1992_, 11, v_incrLoadFileName_x3f_1984_);
lean_ctor_set(v_reuseFailAlloc_1992_, 12, v_incrHeaderSaveFileName_x3f_1985_);
lean_ctor_set_uint8(v_reuseFailAlloc_1992_, sizeof(void*)*13 + 8, v_component_1964_);
lean_ctor_set_uint8(v_reuseFailAlloc_1992_, sizeof(void*)*13 + 9, v_printPrefix_1965_);
lean_ctor_set_uint8(v_reuseFailAlloc_1992_, sizeof(void*)*13 + 10, v_printLibDir_1966_);
lean_ctor_set_uint8(v_reuseFailAlloc_1992_, sizeof(void*)*13 + 11, v_useStdin_1967_);
lean_ctor_set_uint8(v_reuseFailAlloc_1992_, sizeof(void*)*13 + 12, v_onlyDeps_1968_);
lean_ctor_set_uint8(v_reuseFailAlloc_1992_, sizeof(void*)*13 + 14, v_depsJson_1969_);
lean_ctor_set_uint32(v_reuseFailAlloc_1992_, sizeof(void*)*13, v_trustLevel_1971_);
lean_ctor_set_uint32(v_reuseFailAlloc_1992_, sizeof(void*)*13 + 4, v_numThreads_1972_);
lean_ctor_set_uint8(v_reuseFailAlloc_1992_, sizeof(void*)*13 + 15, v_jsonOutput_1979_);
lean_ctor_set_uint8(v_reuseFailAlloc_1992_, sizeof(void*)*13 + 16, v_printStats_1981_);
lean_ctor_set_uint8(v_reuseFailAlloc_1992_, sizeof(void*)*13 + 17, v_run_1982_);
v___x_1990_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1991_; 
lean_ctor_set_uint8(v___x_1990_, sizeof(void*)*13 + 13, v___x_1204_);
v___x_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
return v___x_1991_;
}
}
}
}
else
{
lean_object* v_leanOpts_1994_; lean_object* v_forwardedArgs_1995_; uint8_t v_component_1996_; uint8_t v_printPrefix_1997_; uint8_t v_printLibDir_1998_; uint8_t v_useStdin_1999_; uint8_t v_onlySrcDeps_2000_; uint8_t v_depsJson_2001_; lean_object* v_opts_2002_; uint32_t v_trustLevel_2003_; uint32_t v_numThreads_2004_; lean_object* v_rootDir_x3f_2005_; lean_object* v_setupFileName_x3f_2006_; lean_object* v_oleanFileName_x3f_2007_; lean_object* v_ileanFileName_x3f_2008_; lean_object* v_cFileName_x3f_2009_; lean_object* v_bcFileName_x3f_2010_; uint8_t v_jsonOutput_2011_; lean_object* v_errorOnKinds_2012_; uint8_t v_printStats_2013_; uint8_t v_run_2014_; lean_object* v_incrSaveFileName_x3f_2015_; lean_object* v_incrLoadFileName_x3f_2016_; lean_object* v_incrHeaderSaveFileName_x3f_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2025_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_1994_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_1995_ = lean_ctor_get(v_opts_941_, 1);
v_component_1996_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_1997_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_1998_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_1999_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlySrcDeps_2000_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_2001_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_2002_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_2003_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_2004_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2005_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_2006_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_2007_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_2008_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_2009_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_2010_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_2011_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_2012_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_2013_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_2014_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2015_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_2016_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_2017_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_2025_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2019_ = v_opts_941_;
v_isShared_2020_ = v_isSharedCheck_2025_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2017_);
lean_inc(v_incrLoadFileName_x3f_2016_);
lean_inc(v_incrSaveFileName_x3f_2015_);
lean_inc(v_errorOnKinds_2012_);
lean_inc(v_bcFileName_x3f_2010_);
lean_inc(v_cFileName_x3f_2009_);
lean_inc(v_ileanFileName_x3f_2008_);
lean_inc(v_oleanFileName_x3f_2007_);
lean_inc(v_setupFileName_x3f_2006_);
lean_inc(v_rootDir_x3f_2005_);
lean_inc(v_opts_2002_);
lean_inc(v_forwardedArgs_1995_);
lean_inc(v_leanOpts_1994_);
lean_dec(v_opts_941_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2025_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_leanOpts_1994_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_forwardedArgs_1995_);
lean_ctor_set(v_reuseFailAlloc_2024_, 2, v_opts_2002_);
lean_ctor_set(v_reuseFailAlloc_2024_, 3, v_rootDir_x3f_2005_);
lean_ctor_set(v_reuseFailAlloc_2024_, 4, v_setupFileName_x3f_2006_);
lean_ctor_set(v_reuseFailAlloc_2024_, 5, v_oleanFileName_x3f_2007_);
lean_ctor_set(v_reuseFailAlloc_2024_, 6, v_ileanFileName_x3f_2008_);
lean_ctor_set(v_reuseFailAlloc_2024_, 7, v_cFileName_x3f_2009_);
lean_ctor_set(v_reuseFailAlloc_2024_, 8, v_bcFileName_x3f_2010_);
lean_ctor_set(v_reuseFailAlloc_2024_, 9, v_errorOnKinds_2012_);
lean_ctor_set(v_reuseFailAlloc_2024_, 10, v_incrSaveFileName_x3f_2015_);
lean_ctor_set(v_reuseFailAlloc_2024_, 11, v_incrLoadFileName_x3f_2016_);
lean_ctor_set(v_reuseFailAlloc_2024_, 12, v_incrHeaderSaveFileName_x3f_2017_);
lean_ctor_set_uint8(v_reuseFailAlloc_2024_, sizeof(void*)*13 + 8, v_component_1996_);
lean_ctor_set_uint8(v_reuseFailAlloc_2024_, sizeof(void*)*13 + 9, v_printPrefix_1997_);
lean_ctor_set_uint8(v_reuseFailAlloc_2024_, sizeof(void*)*13 + 10, v_printLibDir_1998_);
lean_ctor_set_uint8(v_reuseFailAlloc_2024_, sizeof(void*)*13 + 11, v_useStdin_1999_);
lean_ctor_set_uint8(v_reuseFailAlloc_2024_, sizeof(void*)*13 + 13, v_onlySrcDeps_2000_);
lean_ctor_set_uint8(v_reuseFailAlloc_2024_, sizeof(void*)*13 + 14, v_depsJson_2001_);
lean_ctor_set_uint32(v_reuseFailAlloc_2024_, sizeof(void*)*13, v_trustLevel_2003_);
lean_ctor_set_uint32(v_reuseFailAlloc_2024_, sizeof(void*)*13 + 4, v_numThreads_2004_);
lean_ctor_set_uint8(v_reuseFailAlloc_2024_, sizeof(void*)*13 + 15, v_jsonOutput_2011_);
lean_ctor_set_uint8(v_reuseFailAlloc_2024_, sizeof(void*)*13 + 16, v_printStats_2013_);
lean_ctor_set_uint8(v_reuseFailAlloc_2024_, sizeof(void*)*13 + 17, v_run_2014_);
v___x_2022_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2023_; 
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*13 + 12, v___x_1202_);
v___x_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
return v___x_2023_;
}
}
}
}
else
{
lean_object* v_leanOpts_2026_; lean_object* v_forwardedArgs_2027_; uint8_t v_component_2028_; uint8_t v_printPrefix_2029_; uint8_t v_printLibDir_2030_; uint8_t v_useStdin_2031_; uint8_t v_onlyDeps_2032_; uint8_t v_onlySrcDeps_2033_; uint8_t v_depsJson_2034_; lean_object* v_opts_2035_; uint32_t v_trustLevel_2036_; uint32_t v_numThreads_2037_; lean_object* v_rootDir_x3f_2038_; lean_object* v_setupFileName_x3f_2039_; lean_object* v_oleanFileName_x3f_2040_; lean_object* v_ileanFileName_x3f_2041_; lean_object* v_cFileName_x3f_2042_; lean_object* v_bcFileName_x3f_2043_; uint8_t v_jsonOutput_2044_; lean_object* v_errorOnKinds_2045_; uint8_t v_printStats_2046_; uint8_t v_run_2047_; lean_object* v_incrSaveFileName_x3f_2048_; lean_object* v_incrLoadFileName_x3f_2049_; lean_object* v_incrHeaderSaveFileName_x3f_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_2026_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_2027_ = lean_ctor_get(v_opts_941_, 1);
v_component_2028_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_2029_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_2030_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_2031_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_2032_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2033_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_2034_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_2035_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_2036_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_2037_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2038_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_2039_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_2040_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_2041_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_2042_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_2043_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_2044_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_2045_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_2046_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_2047_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2048_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_2049_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_2050_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_2060_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2052_ = v_opts_941_;
v_isShared_2053_ = v_isSharedCheck_2060_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2050_);
lean_inc(v_incrLoadFileName_x3f_2049_);
lean_inc(v_incrSaveFileName_x3f_2048_);
lean_inc(v_errorOnKinds_2045_);
lean_inc(v_bcFileName_x3f_2043_);
lean_inc(v_cFileName_x3f_2042_);
lean_inc(v_ileanFileName_x3f_2041_);
lean_inc(v_oleanFileName_x3f_2040_);
lean_inc(v_setupFileName_x3f_2039_);
lean_inc(v_rootDir_x3f_2038_);
lean_inc(v_opts_2035_);
lean_inc(v_forwardedArgs_2027_);
lean_inc(v_leanOpts_2026_);
lean_dec(v_opts_941_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2060_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2057_; 
v___x_2054_ = l___private_Lean_Shell_0__Lean_verbose;
v___x_2055_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_2026_, v___x_2054_, v___x_1198_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 0, v___x_2055_);
v___x_2057_ = v___x_2052_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2055_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v_forwardedArgs_2027_);
lean_ctor_set(v_reuseFailAlloc_2059_, 2, v_opts_2035_);
lean_ctor_set(v_reuseFailAlloc_2059_, 3, v_rootDir_x3f_2038_);
lean_ctor_set(v_reuseFailAlloc_2059_, 4, v_setupFileName_x3f_2039_);
lean_ctor_set(v_reuseFailAlloc_2059_, 5, v_oleanFileName_x3f_2040_);
lean_ctor_set(v_reuseFailAlloc_2059_, 6, v_ileanFileName_x3f_2041_);
lean_ctor_set(v_reuseFailAlloc_2059_, 7, v_cFileName_x3f_2042_);
lean_ctor_set(v_reuseFailAlloc_2059_, 8, v_bcFileName_x3f_2043_);
lean_ctor_set(v_reuseFailAlloc_2059_, 9, v_errorOnKinds_2045_);
lean_ctor_set(v_reuseFailAlloc_2059_, 10, v_incrSaveFileName_x3f_2048_);
lean_ctor_set(v_reuseFailAlloc_2059_, 11, v_incrLoadFileName_x3f_2049_);
lean_ctor_set(v_reuseFailAlloc_2059_, 12, v_incrHeaderSaveFileName_x3f_2050_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, sizeof(void*)*13 + 8, v_component_2028_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, sizeof(void*)*13 + 9, v_printPrefix_2029_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, sizeof(void*)*13 + 10, v_printLibDir_2030_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, sizeof(void*)*13 + 11, v_useStdin_2031_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, sizeof(void*)*13 + 12, v_onlyDeps_2032_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, sizeof(void*)*13 + 13, v_onlySrcDeps_2033_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, sizeof(void*)*13 + 14, v_depsJson_2034_);
lean_ctor_set_uint32(v_reuseFailAlloc_2059_, sizeof(void*)*13, v_trustLevel_2036_);
lean_ctor_set_uint32(v_reuseFailAlloc_2059_, sizeof(void*)*13 + 4, v_numThreads_2037_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, sizeof(void*)*13 + 15, v_jsonOutput_2044_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, sizeof(void*)*13 + 16, v_printStats_2046_);
lean_ctor_set_uint8(v_reuseFailAlloc_2059_, sizeof(void*)*13 + 17, v_run_2047_);
v___x_2057_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
lean_object* v___x_2058_; 
v___x_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
return v___x_2058_;
}
}
}
}
else
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13));
v___x_2062_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2061_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2116_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2065_ = v___x_2062_;
v_isShared_2066_ = v_isSharedCheck_2116_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2116_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2067_ = lean_unsigned_to_nat(0u);
v___x_2068_ = lean_string_utf8_byte_size(v_a_2063_);
lean_inc(v_a_2063_);
v___x_2069_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2069_, 0, v_a_2063_);
lean_ctor_set(v___x_2069_, 1, v___x_2067_);
lean_ctor_set(v___x_2069_, 2, v___x_2068_);
v___x_2070_ = l_String_Slice_toNat_x3f(v___x_2069_);
lean_dec_ref_known(v___x_2069_, 3);
if (lean_obj_tag(v___x_2070_) == 1)
{
lean_object* v_val_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; 
v_val_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_val_2071_);
lean_dec_ref_known(v___x_2070_, 1);
v___x_2072_ = lean_cstr_to_nat("4294967296");
v___x_2073_ = lean_nat_dec_lt(v_val_2071_, v___x_2072_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
lean_dec(v_val_2071_);
lean_del_object(v___x_2065_);
lean_dec(v_a_2063_);
lean_dec_ref(v_opts_941_);
v___x_2074_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14));
v___x_2075_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2074_);
lean_dec_ref(v___x_2075_);
goto v___jp_1011_;
}
else
{
lean_object* v_leanOpts_2076_; lean_object* v_forwardedArgs_2077_; uint8_t v_component_2078_; uint8_t v_printPrefix_2079_; uint8_t v_printLibDir_2080_; uint8_t v_useStdin_2081_; uint8_t v_onlyDeps_2082_; uint8_t v_onlySrcDeps_2083_; uint8_t v_depsJson_2084_; lean_object* v_opts_2085_; uint32_t v_numThreads_2086_; lean_object* v_rootDir_x3f_2087_; lean_object* v_setupFileName_x3f_2088_; lean_object* v_oleanFileName_x3f_2089_; lean_object* v_ileanFileName_x3f_2090_; lean_object* v_cFileName_x3f_2091_; lean_object* v_bcFileName_x3f_2092_; uint8_t v_jsonOutput_2093_; lean_object* v_errorOnKinds_2094_; uint8_t v_printStats_2095_; uint8_t v_run_2096_; lean_object* v_incrSaveFileName_x3f_2097_; lean_object* v_incrLoadFileName_x3f_2098_; lean_object* v_incrHeaderSaveFileName_x3f_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2113_; 
v_leanOpts_2076_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_2077_ = lean_ctor_get(v_opts_941_, 1);
v_component_2078_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_2079_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_2080_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_2081_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_2082_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2083_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_2084_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_2085_ = lean_ctor_get(v_opts_941_, 2);
v_numThreads_2086_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2087_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_2088_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_2089_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_2090_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_2091_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_2092_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_2093_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_2094_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_2095_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_2096_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2097_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_2098_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_2099_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_2113_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2101_ = v_opts_941_;
v_isShared_2102_ = v_isSharedCheck_2113_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2099_);
lean_inc(v_incrLoadFileName_x3f_2098_);
lean_inc(v_incrSaveFileName_x3f_2097_);
lean_inc(v_errorOnKinds_2094_);
lean_inc(v_bcFileName_x3f_2092_);
lean_inc(v_cFileName_x3f_2091_);
lean_inc(v_ileanFileName_x3f_2090_);
lean_inc(v_oleanFileName_x3f_2089_);
lean_inc(v_setupFileName_x3f_2088_);
lean_inc(v_rootDir_x3f_2087_);
lean_inc(v_opts_2085_);
lean_inc(v_forwardedArgs_2077_);
lean_inc(v_leanOpts_2076_);
lean_dec(v_opts_941_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2113_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
uint32_t v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2103_ = lean_uint32_of_nat(v_val_2071_);
lean_dec(v_val_2071_);
v___x_2104_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15));
v___x_2105_ = lean_string_append(v___x_2104_, v_a_2063_);
lean_dec(v_a_2063_);
v___x_2106_ = lean_array_push(v_forwardedArgs_2077_, v___x_2105_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 1, v___x_2106_);
v___x_2108_ = v___x_2101_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_leanOpts_2076_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v___x_2106_);
lean_ctor_set(v_reuseFailAlloc_2112_, 2, v_opts_2085_);
lean_ctor_set(v_reuseFailAlloc_2112_, 3, v_rootDir_x3f_2087_);
lean_ctor_set(v_reuseFailAlloc_2112_, 4, v_setupFileName_x3f_2088_);
lean_ctor_set(v_reuseFailAlloc_2112_, 5, v_oleanFileName_x3f_2089_);
lean_ctor_set(v_reuseFailAlloc_2112_, 6, v_ileanFileName_x3f_2090_);
lean_ctor_set(v_reuseFailAlloc_2112_, 7, v_cFileName_x3f_2091_);
lean_ctor_set(v_reuseFailAlloc_2112_, 8, v_bcFileName_x3f_2092_);
lean_ctor_set(v_reuseFailAlloc_2112_, 9, v_errorOnKinds_2094_);
lean_ctor_set(v_reuseFailAlloc_2112_, 10, v_incrSaveFileName_x3f_2097_);
lean_ctor_set(v_reuseFailAlloc_2112_, 11, v_incrLoadFileName_x3f_2098_);
lean_ctor_set(v_reuseFailAlloc_2112_, 12, v_incrHeaderSaveFileName_x3f_2099_);
lean_ctor_set_uint8(v_reuseFailAlloc_2112_, sizeof(void*)*13 + 8, v_component_2078_);
lean_ctor_set_uint8(v_reuseFailAlloc_2112_, sizeof(void*)*13 + 9, v_printPrefix_2079_);
lean_ctor_set_uint8(v_reuseFailAlloc_2112_, sizeof(void*)*13 + 10, v_printLibDir_2080_);
lean_ctor_set_uint8(v_reuseFailAlloc_2112_, sizeof(void*)*13 + 11, v_useStdin_2081_);
lean_ctor_set_uint8(v_reuseFailAlloc_2112_, sizeof(void*)*13 + 12, v_onlyDeps_2082_);
lean_ctor_set_uint8(v_reuseFailAlloc_2112_, sizeof(void*)*13 + 13, v_onlySrcDeps_2083_);
lean_ctor_set_uint8(v_reuseFailAlloc_2112_, sizeof(void*)*13 + 14, v_depsJson_2084_);
lean_ctor_set_uint32(v_reuseFailAlloc_2112_, sizeof(void*)*13 + 4, v_numThreads_2086_);
lean_ctor_set_uint8(v_reuseFailAlloc_2112_, sizeof(void*)*13 + 15, v_jsonOutput_2093_);
lean_ctor_set_uint8(v_reuseFailAlloc_2112_, sizeof(void*)*13 + 16, v_printStats_2095_);
lean_ctor_set_uint8(v_reuseFailAlloc_2112_, sizeof(void*)*13 + 17, v_run_2096_);
v___x_2108_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2110_; 
lean_ctor_set_uint32(v___x_2108_, sizeof(void*)*13, v___x_2103_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v___x_2108_);
v___x_2110_ = v___x_2065_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
else
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
lean_dec(v___x_2070_);
lean_del_object(v___x_2065_);
lean_dec(v_a_2063_);
lean_dec_ref(v_opts_941_);
v___x_2114_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16));
v___x_2115_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2114_);
lean_dec_ref(v___x_2115_);
goto v___jp_1008_;
}
}
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
lean_dec_ref(v_opts_941_);
v_a_2117_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2062_, 1);
v___x_2121_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2122_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2121_);
lean_dec_ref(v___x_2122_);
goto v___jp_2118_;
v___jp_2118_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = lean_io_error_to_string(v_a_2117_);
v___x_2120_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2119_);
lean_dec_ref(v___x_2120_);
goto v___jp_1005_;
}
}
}
}
else
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17));
v___x_2124_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2123_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2176_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2127_ = v___x_2124_;
v_isShared_2128_ = v_isSharedCheck_2176_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2124_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2176_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2129_ = lean_unsigned_to_nat(0u);
v___x_2130_ = lean_string_utf8_byte_size(v_a_2125_);
lean_inc(v_a_2125_);
v___x_2131_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2131_, 0, v_a_2125_);
lean_ctor_set(v___x_2131_, 1, v___x_2129_);
lean_ctor_set(v___x_2131_, 2, v___x_2130_);
v___x_2132_ = l_String_Slice_toNat_x3f(v___x_2131_);
lean_dec_ref_known(v___x_2131_, 3);
if (lean_obj_tag(v___x_2132_) == 1)
{
lean_object* v_val_2133_; lean_object* v_leanOpts_2134_; lean_object* v_forwardedArgs_2135_; uint8_t v_component_2136_; uint8_t v_printPrefix_2137_; uint8_t v_printLibDir_2138_; uint8_t v_useStdin_2139_; uint8_t v_onlyDeps_2140_; uint8_t v_onlySrcDeps_2141_; uint8_t v_depsJson_2142_; lean_object* v_opts_2143_; uint32_t v_trustLevel_2144_; uint32_t v_numThreads_2145_; lean_object* v_rootDir_x3f_2146_; lean_object* v_setupFileName_x3f_2147_; lean_object* v_oleanFileName_x3f_2148_; lean_object* v_ileanFileName_x3f_2149_; lean_object* v_cFileName_x3f_2150_; lean_object* v_bcFileName_x3f_2151_; uint8_t v_jsonOutput_2152_; lean_object* v_errorOnKinds_2153_; uint8_t v_printStats_2154_; uint8_t v_run_2155_; lean_object* v_incrSaveFileName_x3f_2156_; lean_object* v_incrLoadFileName_x3f_2157_; lean_object* v_incrHeaderSaveFileName_x3f_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2173_; 
v_val_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_val_2133_);
lean_dec_ref_known(v___x_2132_, 1);
v_leanOpts_2134_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_2135_ = lean_ctor_get(v_opts_941_, 1);
v_component_2136_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_2137_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_2138_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_2139_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_2140_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2141_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_2142_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_2143_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_2144_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_2145_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2146_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_2147_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_2148_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_2149_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_2150_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_2151_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_2152_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_2153_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_2154_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_2155_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2156_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_2157_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_2158_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2160_ = v_opts_941_;
v_isShared_2161_ = v_isSharedCheck_2173_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2158_);
lean_inc(v_incrLoadFileName_x3f_2157_);
lean_inc(v_incrSaveFileName_x3f_2156_);
lean_inc(v_errorOnKinds_2153_);
lean_inc(v_bcFileName_x3f_2151_);
lean_inc(v_cFileName_x3f_2150_);
lean_inc(v_ileanFileName_x3f_2149_);
lean_inc(v_oleanFileName_x3f_2148_);
lean_inc(v_setupFileName_x3f_2147_);
lean_inc(v_rootDir_x3f_2146_);
lean_inc(v_opts_2143_);
lean_inc(v_forwardedArgs_2135_);
lean_inc(v_leanOpts_2134_);
lean_dec(v_opts_941_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2173_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2162_ = l___private_Lean_Shell_0__Lean_timeout;
v___x_2163_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_2134_, v___x_2162_, v_val_2133_);
v___x_2164_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18));
v___x_2165_ = lean_string_append(v___x_2164_, v_a_2125_);
lean_dec(v_a_2125_);
v___x_2166_ = lean_array_push(v_forwardedArgs_2135_, v___x_2165_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 1, v___x_2166_);
lean_ctor_set(v___x_2160_, 0, v___x_2163_);
v___x_2168_ = v___x_2160_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2163_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v___x_2166_);
lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_opts_2143_);
lean_ctor_set(v_reuseFailAlloc_2172_, 3, v_rootDir_x3f_2146_);
lean_ctor_set(v_reuseFailAlloc_2172_, 4, v_setupFileName_x3f_2147_);
lean_ctor_set(v_reuseFailAlloc_2172_, 5, v_oleanFileName_x3f_2148_);
lean_ctor_set(v_reuseFailAlloc_2172_, 6, v_ileanFileName_x3f_2149_);
lean_ctor_set(v_reuseFailAlloc_2172_, 7, v_cFileName_x3f_2150_);
lean_ctor_set(v_reuseFailAlloc_2172_, 8, v_bcFileName_x3f_2151_);
lean_ctor_set(v_reuseFailAlloc_2172_, 9, v_errorOnKinds_2153_);
lean_ctor_set(v_reuseFailAlloc_2172_, 10, v_incrSaveFileName_x3f_2156_);
lean_ctor_set(v_reuseFailAlloc_2172_, 11, v_incrLoadFileName_x3f_2157_);
lean_ctor_set(v_reuseFailAlloc_2172_, 12, v_incrHeaderSaveFileName_x3f_2158_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*13 + 8, v_component_2136_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*13 + 9, v_printPrefix_2137_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*13 + 10, v_printLibDir_2138_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*13 + 11, v_useStdin_2139_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*13 + 12, v_onlyDeps_2140_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*13 + 13, v_onlySrcDeps_2141_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*13 + 14, v_depsJson_2142_);
lean_ctor_set_uint32(v_reuseFailAlloc_2172_, sizeof(void*)*13, v_trustLevel_2144_);
lean_ctor_set_uint32(v_reuseFailAlloc_2172_, sizeof(void*)*13 + 4, v_numThreads_2145_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*13 + 15, v_jsonOutput_2152_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*13 + 16, v_printStats_2154_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*13 + 17, v_run_2155_);
v___x_2168_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v___x_2170_; 
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v___x_2168_);
v___x_2170_ = v___x_2127_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
lean_dec(v___x_2132_);
lean_del_object(v___x_2127_);
lean_dec(v_a_2125_);
lean_dec_ref(v_opts_941_);
v___x_2174_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19));
v___x_2175_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2174_);
lean_dec_ref(v___x_2175_);
goto v___jp_1118_;
}
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
lean_dec_ref(v_opts_941_);
v_a_2177_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2124_, 1);
v___x_2181_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2182_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2181_);
lean_dec_ref(v___x_2182_);
goto v___jp_2178_;
v___jp_2178_:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = lean_io_error_to_string(v_a_2177_);
v___x_2180_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2179_);
lean_dec_ref(v___x_2180_);
goto v___jp_1124_;
}
}
}
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20));
v___x_2184_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2183_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2236_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2187_ = v___x_2184_;
v_isShared_2188_ = v_isSharedCheck_2236_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2184_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2236_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2189_ = lean_unsigned_to_nat(0u);
v___x_2190_ = lean_string_utf8_byte_size(v_a_2185_);
lean_inc(v_a_2185_);
v___x_2191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2191_, 0, v_a_2185_);
lean_ctor_set(v___x_2191_, 1, v___x_2189_);
lean_ctor_set(v___x_2191_, 2, v___x_2190_);
v___x_2192_ = l_String_Slice_toNat_x3f(v___x_2191_);
lean_dec_ref_known(v___x_2191_, 3);
if (lean_obj_tag(v___x_2192_) == 1)
{
lean_object* v_val_2193_; lean_object* v_leanOpts_2194_; lean_object* v_forwardedArgs_2195_; uint8_t v_component_2196_; uint8_t v_printPrefix_2197_; uint8_t v_printLibDir_2198_; uint8_t v_useStdin_2199_; uint8_t v_onlyDeps_2200_; uint8_t v_onlySrcDeps_2201_; uint8_t v_depsJson_2202_; lean_object* v_opts_2203_; uint32_t v_trustLevel_2204_; uint32_t v_numThreads_2205_; lean_object* v_rootDir_x3f_2206_; lean_object* v_setupFileName_x3f_2207_; lean_object* v_oleanFileName_x3f_2208_; lean_object* v_ileanFileName_x3f_2209_; lean_object* v_cFileName_x3f_2210_; lean_object* v_bcFileName_x3f_2211_; uint8_t v_jsonOutput_2212_; lean_object* v_errorOnKinds_2213_; uint8_t v_printStats_2214_; uint8_t v_run_2215_; lean_object* v_incrSaveFileName_x3f_2216_; lean_object* v_incrLoadFileName_x3f_2217_; lean_object* v_incrHeaderSaveFileName_x3f_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2233_; 
v_val_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_val_2193_);
lean_dec_ref_known(v___x_2192_, 1);
v_leanOpts_2194_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_2195_ = lean_ctor_get(v_opts_941_, 1);
v_component_2196_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_2197_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_2198_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_2199_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_2200_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2201_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_2202_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_2203_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_2204_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_2205_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2206_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_2207_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_2208_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_2209_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_2210_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_2211_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_2212_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_2213_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_2214_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_2215_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2216_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_2217_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_2218_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_2233_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2220_ = v_opts_941_;
v_isShared_2221_ = v_isSharedCheck_2233_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2218_);
lean_inc(v_incrLoadFileName_x3f_2217_);
lean_inc(v_incrSaveFileName_x3f_2216_);
lean_inc(v_errorOnKinds_2213_);
lean_inc(v_bcFileName_x3f_2211_);
lean_inc(v_cFileName_x3f_2210_);
lean_inc(v_ileanFileName_x3f_2209_);
lean_inc(v_oleanFileName_x3f_2208_);
lean_inc(v_setupFileName_x3f_2207_);
lean_inc(v_rootDir_x3f_2206_);
lean_inc(v_opts_2203_);
lean_inc(v_forwardedArgs_2195_);
lean_inc(v_leanOpts_2194_);
lean_dec(v_opts_941_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2233_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2228_; 
v___x_2222_ = l___private_Lean_Shell_0__Lean_maxMemory;
v___x_2223_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_2194_, v___x_2222_, v_val_2193_);
v___x_2224_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21));
v___x_2225_ = lean_string_append(v___x_2224_, v_a_2185_);
lean_dec(v_a_2185_);
v___x_2226_ = lean_array_push(v_forwardedArgs_2195_, v___x_2225_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 1, v___x_2226_);
lean_ctor_set(v___x_2220_, 0, v___x_2223_);
v___x_2228_ = v___x_2220_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2223_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v___x_2226_);
lean_ctor_set(v_reuseFailAlloc_2232_, 2, v_opts_2203_);
lean_ctor_set(v_reuseFailAlloc_2232_, 3, v_rootDir_x3f_2206_);
lean_ctor_set(v_reuseFailAlloc_2232_, 4, v_setupFileName_x3f_2207_);
lean_ctor_set(v_reuseFailAlloc_2232_, 5, v_oleanFileName_x3f_2208_);
lean_ctor_set(v_reuseFailAlloc_2232_, 6, v_ileanFileName_x3f_2209_);
lean_ctor_set(v_reuseFailAlloc_2232_, 7, v_cFileName_x3f_2210_);
lean_ctor_set(v_reuseFailAlloc_2232_, 8, v_bcFileName_x3f_2211_);
lean_ctor_set(v_reuseFailAlloc_2232_, 9, v_errorOnKinds_2213_);
lean_ctor_set(v_reuseFailAlloc_2232_, 10, v_incrSaveFileName_x3f_2216_);
lean_ctor_set(v_reuseFailAlloc_2232_, 11, v_incrLoadFileName_x3f_2217_);
lean_ctor_set(v_reuseFailAlloc_2232_, 12, v_incrHeaderSaveFileName_x3f_2218_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*13 + 8, v_component_2196_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*13 + 9, v_printPrefix_2197_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*13 + 10, v_printLibDir_2198_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*13 + 11, v_useStdin_2199_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*13 + 12, v_onlyDeps_2200_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*13 + 13, v_onlySrcDeps_2201_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*13 + 14, v_depsJson_2202_);
lean_ctor_set_uint32(v_reuseFailAlloc_2232_, sizeof(void*)*13, v_trustLevel_2204_);
lean_ctor_set_uint32(v_reuseFailAlloc_2232_, sizeof(void*)*13 + 4, v_numThreads_2205_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*13 + 15, v_jsonOutput_2212_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*13 + 16, v_printStats_2214_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*13 + 17, v_run_2215_);
v___x_2228_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
lean_object* v___x_2230_; 
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 0, v___x_2228_);
v___x_2230_ = v___x_2187_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2228_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
else
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
lean_dec(v___x_2192_);
lean_del_object(v___x_2187_);
lean_dec(v_a_2185_);
lean_dec_ref(v_opts_941_);
v___x_2234_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22));
v___x_2235_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2234_);
lean_dec_ref(v___x_2235_);
goto v___jp_999_;
}
}
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
lean_dec_ref(v_opts_941_);
v_a_2237_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2237_);
lean_dec_ref_known(v___x_2184_, 1);
v___x_2241_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2242_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2241_);
lean_dec_ref(v___x_2242_);
goto v___jp_2238_;
v___jp_2238_:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = lean_io_error_to_string(v_a_2237_);
v___x_2240_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2239_);
lean_dec_ref(v___x_2240_);
goto v___jp_996_;
}
}
}
}
else
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23));
v___x_2244_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2243_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2288_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2247_ = v___x_2244_;
v_isShared_2248_ = v_isSharedCheck_2288_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2244_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2288_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v_leanOpts_2249_; lean_object* v_forwardedArgs_2250_; uint8_t v_component_2251_; uint8_t v_printPrefix_2252_; uint8_t v_printLibDir_2253_; uint8_t v_useStdin_2254_; uint8_t v_onlyDeps_2255_; uint8_t v_onlySrcDeps_2256_; uint8_t v_depsJson_2257_; lean_object* v_opts_2258_; uint32_t v_trustLevel_2259_; uint32_t v_numThreads_2260_; lean_object* v_setupFileName_x3f_2261_; lean_object* v_oleanFileName_x3f_2262_; lean_object* v_ileanFileName_x3f_2263_; lean_object* v_cFileName_x3f_2264_; lean_object* v_bcFileName_x3f_2265_; uint8_t v_jsonOutput_2266_; lean_object* v_errorOnKinds_2267_; uint8_t v_printStats_2268_; uint8_t v_run_2269_; lean_object* v_incrSaveFileName_x3f_2270_; lean_object* v_incrLoadFileName_x3f_2271_; lean_object* v_incrHeaderSaveFileName_x3f_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2286_; 
v_leanOpts_2249_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_2250_ = lean_ctor_get(v_opts_941_, 1);
v_component_2251_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_2252_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_2253_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_2254_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_2255_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2256_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_2257_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_2258_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_2259_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_2260_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_setupFileName_x3f_2261_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_2262_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_2263_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_2264_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_2265_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_2266_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_2267_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_2268_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_2269_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2270_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_2271_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_2272_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_2286_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_2286_ == 0)
{
lean_object* v_unused_2287_; 
v_unused_2287_ = lean_ctor_get(v_opts_941_, 3);
lean_dec(v_unused_2287_);
v___x_2274_ = v_opts_941_;
v_isShared_2275_ = v_isSharedCheck_2286_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2272_);
lean_inc(v_incrLoadFileName_x3f_2271_);
lean_inc(v_incrSaveFileName_x3f_2270_);
lean_inc(v_errorOnKinds_2267_);
lean_inc(v_bcFileName_x3f_2265_);
lean_inc(v_cFileName_x3f_2264_);
lean_inc(v_ileanFileName_x3f_2263_);
lean_inc(v_oleanFileName_x3f_2262_);
lean_inc(v_setupFileName_x3f_2261_);
lean_inc(v_opts_2258_);
lean_inc(v_forwardedArgs_2250_);
lean_inc(v_leanOpts_2249_);
lean_dec(v_opts_941_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2286_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2281_; 
v___x_2276_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24));
v___x_2277_ = lean_string_append(v___x_2276_, v_a_2245_);
v___x_2278_ = lean_array_push(v_forwardedArgs_2250_, v___x_2277_);
v___x_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2279_, 0, v_a_2245_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 3, v___x_2279_);
lean_ctor_set(v___x_2274_, 1, v___x_2278_);
v___x_2281_ = v___x_2274_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_leanOpts_2249_);
lean_ctor_set(v_reuseFailAlloc_2285_, 1, v___x_2278_);
lean_ctor_set(v_reuseFailAlloc_2285_, 2, v_opts_2258_);
lean_ctor_set(v_reuseFailAlloc_2285_, 3, v___x_2279_);
lean_ctor_set(v_reuseFailAlloc_2285_, 4, v_setupFileName_x3f_2261_);
lean_ctor_set(v_reuseFailAlloc_2285_, 5, v_oleanFileName_x3f_2262_);
lean_ctor_set(v_reuseFailAlloc_2285_, 6, v_ileanFileName_x3f_2263_);
lean_ctor_set(v_reuseFailAlloc_2285_, 7, v_cFileName_x3f_2264_);
lean_ctor_set(v_reuseFailAlloc_2285_, 8, v_bcFileName_x3f_2265_);
lean_ctor_set(v_reuseFailAlloc_2285_, 9, v_errorOnKinds_2267_);
lean_ctor_set(v_reuseFailAlloc_2285_, 10, v_incrSaveFileName_x3f_2270_);
lean_ctor_set(v_reuseFailAlloc_2285_, 11, v_incrLoadFileName_x3f_2271_);
lean_ctor_set(v_reuseFailAlloc_2285_, 12, v_incrHeaderSaveFileName_x3f_2272_);
lean_ctor_set_uint8(v_reuseFailAlloc_2285_, sizeof(void*)*13 + 8, v_component_2251_);
lean_ctor_set_uint8(v_reuseFailAlloc_2285_, sizeof(void*)*13 + 9, v_printPrefix_2252_);
lean_ctor_set_uint8(v_reuseFailAlloc_2285_, sizeof(void*)*13 + 10, v_printLibDir_2253_);
lean_ctor_set_uint8(v_reuseFailAlloc_2285_, sizeof(void*)*13 + 11, v_useStdin_2254_);
lean_ctor_set_uint8(v_reuseFailAlloc_2285_, sizeof(void*)*13 + 12, v_onlyDeps_2255_);
lean_ctor_set_uint8(v_reuseFailAlloc_2285_, sizeof(void*)*13 + 13, v_onlySrcDeps_2256_);
lean_ctor_set_uint8(v_reuseFailAlloc_2285_, sizeof(void*)*13 + 14, v_depsJson_2257_);
lean_ctor_set_uint32(v_reuseFailAlloc_2285_, sizeof(void*)*13, v_trustLevel_2259_);
lean_ctor_set_uint32(v_reuseFailAlloc_2285_, sizeof(void*)*13 + 4, v_numThreads_2260_);
lean_ctor_set_uint8(v_reuseFailAlloc_2285_, sizeof(void*)*13 + 15, v_jsonOutput_2266_);
lean_ctor_set_uint8(v_reuseFailAlloc_2285_, sizeof(void*)*13 + 16, v_printStats_2268_);
lean_ctor_set_uint8(v_reuseFailAlloc_2285_, sizeof(void*)*13 + 17, v_run_2269_);
v___x_2281_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
lean_object* v___x_2283_; 
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v___x_2281_);
v___x_2283_ = v___x_2247_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2281_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
lean_dec_ref(v_opts_941_);
v_a_2289_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2289_);
lean_dec_ref_known(v___x_2244_, 1);
v___x_2293_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2294_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2293_);
lean_dec_ref(v___x_2294_);
goto v___jp_2290_;
v___jp_2290_:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = lean_io_error_to_string(v_a_2289_);
v___x_2292_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2291_);
lean_dec_ref(v___x_2292_);
goto v___jp_1130_;
}
}
}
}
else
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25));
v___x_2296_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2295_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2337_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2299_ = v___x_2296_;
v_isShared_2300_ = v_isSharedCheck_2337_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2296_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2337_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v_leanOpts_2301_; lean_object* v_forwardedArgs_2302_; uint8_t v_component_2303_; uint8_t v_printPrefix_2304_; uint8_t v_printLibDir_2305_; uint8_t v_useStdin_2306_; uint8_t v_onlyDeps_2307_; uint8_t v_onlySrcDeps_2308_; uint8_t v_depsJson_2309_; lean_object* v_opts_2310_; uint32_t v_trustLevel_2311_; uint32_t v_numThreads_2312_; lean_object* v_rootDir_x3f_2313_; lean_object* v_setupFileName_x3f_2314_; lean_object* v_oleanFileName_x3f_2315_; lean_object* v_cFileName_x3f_2316_; lean_object* v_bcFileName_x3f_2317_; uint8_t v_jsonOutput_2318_; lean_object* v_errorOnKinds_2319_; uint8_t v_printStats_2320_; uint8_t v_run_2321_; lean_object* v_incrSaveFileName_x3f_2322_; lean_object* v_incrLoadFileName_x3f_2323_; lean_object* v_incrHeaderSaveFileName_x3f_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2335_; 
v_leanOpts_2301_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_2302_ = lean_ctor_get(v_opts_941_, 1);
v_component_2303_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_2304_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_2305_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_2306_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_2307_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2308_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_2309_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_2310_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_2311_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_2312_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2313_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_2314_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_2315_ = lean_ctor_get(v_opts_941_, 5);
v_cFileName_x3f_2316_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_2317_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_2318_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_2319_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_2320_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_2321_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2322_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_2323_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_2324_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_2335_ == 0)
{
lean_object* v_unused_2336_; 
v_unused_2336_ = lean_ctor_get(v_opts_941_, 6);
lean_dec(v_unused_2336_);
v___x_2326_ = v_opts_941_;
v_isShared_2327_ = v_isSharedCheck_2335_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2324_);
lean_inc(v_incrLoadFileName_x3f_2323_);
lean_inc(v_incrSaveFileName_x3f_2322_);
lean_inc(v_errorOnKinds_2319_);
lean_inc(v_bcFileName_x3f_2317_);
lean_inc(v_cFileName_x3f_2316_);
lean_inc(v_oleanFileName_x3f_2315_);
lean_inc(v_setupFileName_x3f_2314_);
lean_inc(v_rootDir_x3f_2313_);
lean_inc(v_opts_2310_);
lean_inc(v_forwardedArgs_2302_);
lean_inc(v_leanOpts_2301_);
lean_dec(v_opts_941_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2335_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2328_; lean_object* v___x_2330_; 
v___x_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2328_, 0, v_a_2297_);
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 6, v___x_2328_);
v___x_2330_ = v___x_2326_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_leanOpts_2301_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_forwardedArgs_2302_);
lean_ctor_set(v_reuseFailAlloc_2334_, 2, v_opts_2310_);
lean_ctor_set(v_reuseFailAlloc_2334_, 3, v_rootDir_x3f_2313_);
lean_ctor_set(v_reuseFailAlloc_2334_, 4, v_setupFileName_x3f_2314_);
lean_ctor_set(v_reuseFailAlloc_2334_, 5, v_oleanFileName_x3f_2315_);
lean_ctor_set(v_reuseFailAlloc_2334_, 6, v___x_2328_);
lean_ctor_set(v_reuseFailAlloc_2334_, 7, v_cFileName_x3f_2316_);
lean_ctor_set(v_reuseFailAlloc_2334_, 8, v_bcFileName_x3f_2317_);
lean_ctor_set(v_reuseFailAlloc_2334_, 9, v_errorOnKinds_2319_);
lean_ctor_set(v_reuseFailAlloc_2334_, 10, v_incrSaveFileName_x3f_2322_);
lean_ctor_set(v_reuseFailAlloc_2334_, 11, v_incrLoadFileName_x3f_2323_);
lean_ctor_set(v_reuseFailAlloc_2334_, 12, v_incrHeaderSaveFileName_x3f_2324_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*13 + 8, v_component_2303_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*13 + 9, v_printPrefix_2304_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*13 + 10, v_printLibDir_2305_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*13 + 11, v_useStdin_2306_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*13 + 12, v_onlyDeps_2307_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*13 + 13, v_onlySrcDeps_2308_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*13 + 14, v_depsJson_2309_);
lean_ctor_set_uint32(v_reuseFailAlloc_2334_, sizeof(void*)*13, v_trustLevel_2311_);
lean_ctor_set_uint32(v_reuseFailAlloc_2334_, sizeof(void*)*13 + 4, v_numThreads_2312_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*13 + 15, v_jsonOutput_2318_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*13 + 16, v_printStats_2320_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*13 + 17, v_run_2321_);
v___x_2330_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
lean_object* v___x_2332_; 
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 0, v___x_2330_);
v___x_2332_ = v___x_2299_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
lean_dec_ref(v_opts_941_);
v_a_2338_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2296_, 1);
v___x_2342_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2343_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2342_);
lean_dec_ref(v___x_2343_);
goto v___jp_2339_;
v___jp_2339_:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = lean_io_error_to_string(v_a_2338_);
v___x_2341_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2340_);
lean_dec_ref(v___x_2341_);
goto v___jp_990_;
}
}
}
}
else
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26));
v___x_2345_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2344_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2386_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2348_ = v___x_2345_;
v_isShared_2349_ = v_isSharedCheck_2386_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2345_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2386_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v_leanOpts_2350_; lean_object* v_forwardedArgs_2351_; uint8_t v_component_2352_; uint8_t v_printPrefix_2353_; uint8_t v_printLibDir_2354_; uint8_t v_useStdin_2355_; uint8_t v_onlyDeps_2356_; uint8_t v_onlySrcDeps_2357_; uint8_t v_depsJson_2358_; lean_object* v_opts_2359_; uint32_t v_trustLevel_2360_; uint32_t v_numThreads_2361_; lean_object* v_rootDir_x3f_2362_; lean_object* v_setupFileName_x3f_2363_; lean_object* v_ileanFileName_x3f_2364_; lean_object* v_cFileName_x3f_2365_; lean_object* v_bcFileName_x3f_2366_; uint8_t v_jsonOutput_2367_; lean_object* v_errorOnKinds_2368_; uint8_t v_printStats_2369_; uint8_t v_run_2370_; lean_object* v_incrSaveFileName_x3f_2371_; lean_object* v_incrLoadFileName_x3f_2372_; lean_object* v_incrHeaderSaveFileName_x3f_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2384_; 
v_leanOpts_2350_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_2351_ = lean_ctor_get(v_opts_941_, 1);
v_component_2352_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_2353_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_2354_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_2355_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_2356_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2357_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_2358_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_2359_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_2360_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_2361_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2362_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_2363_ = lean_ctor_get(v_opts_941_, 4);
v_ileanFileName_x3f_2364_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_2365_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_2366_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_2367_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_2368_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_2369_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_2370_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2371_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_2372_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_2373_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_2384_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_2384_ == 0)
{
lean_object* v_unused_2385_; 
v_unused_2385_ = lean_ctor_get(v_opts_941_, 5);
lean_dec(v_unused_2385_);
v___x_2375_ = v_opts_941_;
v_isShared_2376_ = v_isSharedCheck_2384_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2373_);
lean_inc(v_incrLoadFileName_x3f_2372_);
lean_inc(v_incrSaveFileName_x3f_2371_);
lean_inc(v_errorOnKinds_2368_);
lean_inc(v_bcFileName_x3f_2366_);
lean_inc(v_cFileName_x3f_2365_);
lean_inc(v_ileanFileName_x3f_2364_);
lean_inc(v_setupFileName_x3f_2363_);
lean_inc(v_rootDir_x3f_2362_);
lean_inc(v_opts_2359_);
lean_inc(v_forwardedArgs_2351_);
lean_inc(v_leanOpts_2350_);
lean_dec(v_opts_941_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2384_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2377_; lean_object* v___x_2379_; 
v___x_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2377_, 0, v_a_2346_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 5, v___x_2377_);
v___x_2379_ = v___x_2375_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_leanOpts_2350_);
lean_ctor_set(v_reuseFailAlloc_2383_, 1, v_forwardedArgs_2351_);
lean_ctor_set(v_reuseFailAlloc_2383_, 2, v_opts_2359_);
lean_ctor_set(v_reuseFailAlloc_2383_, 3, v_rootDir_x3f_2362_);
lean_ctor_set(v_reuseFailAlloc_2383_, 4, v_setupFileName_x3f_2363_);
lean_ctor_set(v_reuseFailAlloc_2383_, 5, v___x_2377_);
lean_ctor_set(v_reuseFailAlloc_2383_, 6, v_ileanFileName_x3f_2364_);
lean_ctor_set(v_reuseFailAlloc_2383_, 7, v_cFileName_x3f_2365_);
lean_ctor_set(v_reuseFailAlloc_2383_, 8, v_bcFileName_x3f_2366_);
lean_ctor_set(v_reuseFailAlloc_2383_, 9, v_errorOnKinds_2368_);
lean_ctor_set(v_reuseFailAlloc_2383_, 10, v_incrSaveFileName_x3f_2371_);
lean_ctor_set(v_reuseFailAlloc_2383_, 11, v_incrLoadFileName_x3f_2372_);
lean_ctor_set(v_reuseFailAlloc_2383_, 12, v_incrHeaderSaveFileName_x3f_2373_);
lean_ctor_set_uint8(v_reuseFailAlloc_2383_, sizeof(void*)*13 + 8, v_component_2352_);
lean_ctor_set_uint8(v_reuseFailAlloc_2383_, sizeof(void*)*13 + 9, v_printPrefix_2353_);
lean_ctor_set_uint8(v_reuseFailAlloc_2383_, sizeof(void*)*13 + 10, v_printLibDir_2354_);
lean_ctor_set_uint8(v_reuseFailAlloc_2383_, sizeof(void*)*13 + 11, v_useStdin_2355_);
lean_ctor_set_uint8(v_reuseFailAlloc_2383_, sizeof(void*)*13 + 12, v_onlyDeps_2356_);
lean_ctor_set_uint8(v_reuseFailAlloc_2383_, sizeof(void*)*13 + 13, v_onlySrcDeps_2357_);
lean_ctor_set_uint8(v_reuseFailAlloc_2383_, sizeof(void*)*13 + 14, v_depsJson_2358_);
lean_ctor_set_uint32(v_reuseFailAlloc_2383_, sizeof(void*)*13, v_trustLevel_2360_);
lean_ctor_set_uint32(v_reuseFailAlloc_2383_, sizeof(void*)*13 + 4, v_numThreads_2361_);
lean_ctor_set_uint8(v_reuseFailAlloc_2383_, sizeof(void*)*13 + 15, v_jsonOutput_2367_);
lean_ctor_set_uint8(v_reuseFailAlloc_2383_, sizeof(void*)*13 + 16, v_printStats_2369_);
lean_ctor_set_uint8(v_reuseFailAlloc_2383_, sizeof(void*)*13 + 17, v_run_2370_);
v___x_2379_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
lean_object* v___x_2381_; 
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v___x_2379_);
v___x_2381_ = v___x_2348_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2379_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
lean_dec_ref(v_opts_941_);
v_a_2387_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2387_);
lean_dec_ref_known(v___x_2345_, 1);
v___x_2391_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2392_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2391_);
lean_dec_ref(v___x_2392_);
goto v___jp_2388_;
v___jp_2388_:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = lean_io_error_to_string(v_a_2387_);
v___x_2390_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2389_);
lean_dec_ref(v___x_2390_);
goto v___jp_1136_;
}
}
}
}
else
{
lean_object* v_leanOpts_2393_; lean_object* v_forwardedArgs_2394_; uint8_t v_component_2395_; uint8_t v_printPrefix_2396_; uint8_t v_printLibDir_2397_; uint8_t v_useStdin_2398_; uint8_t v_onlyDeps_2399_; uint8_t v_onlySrcDeps_2400_; uint8_t v_depsJson_2401_; lean_object* v_opts_2402_; uint32_t v_trustLevel_2403_; uint32_t v_numThreads_2404_; lean_object* v_rootDir_x3f_2405_; lean_object* v_setupFileName_x3f_2406_; lean_object* v_oleanFileName_x3f_2407_; lean_object* v_ileanFileName_x3f_2408_; lean_object* v_cFileName_x3f_2409_; lean_object* v_bcFileName_x3f_2410_; uint8_t v_jsonOutput_2411_; lean_object* v_errorOnKinds_2412_; uint8_t v_printStats_2413_; lean_object* v_incrSaveFileName_x3f_2414_; lean_object* v_incrLoadFileName_x3f_2415_; lean_object* v_incrHeaderSaveFileName_x3f_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2426_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_2393_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_2394_ = lean_ctor_get(v_opts_941_, 1);
v_component_2395_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_2396_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_2397_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_2398_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_2399_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2400_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_2401_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_2402_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_2403_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_2404_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2405_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_2406_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_2407_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_2408_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_2409_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_2410_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_2411_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_2412_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_2413_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_incrSaveFileName_x3f_2414_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_2415_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_2416_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_2426_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2418_ = v_opts_941_;
v_isShared_2419_ = v_isSharedCheck_2426_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2416_);
lean_inc(v_incrLoadFileName_x3f_2415_);
lean_inc(v_incrSaveFileName_x3f_2414_);
lean_inc(v_errorOnKinds_2412_);
lean_inc(v_bcFileName_x3f_2410_);
lean_inc(v_cFileName_x3f_2409_);
lean_inc(v_ileanFileName_x3f_2408_);
lean_inc(v_oleanFileName_x3f_2407_);
lean_inc(v_setupFileName_x3f_2406_);
lean_inc(v_rootDir_x3f_2405_);
lean_inc(v_opts_2402_);
lean_inc(v_forwardedArgs_2394_);
lean_inc(v_leanOpts_2393_);
lean_dec(v_opts_941_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2426_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2423_; 
v___x_2420_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_2421_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_2393_, v___x_2420_, v___x_1184_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2421_);
v___x_2423_ = v___x_2418_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2421_);
lean_ctor_set(v_reuseFailAlloc_2425_, 1, v_forwardedArgs_2394_);
lean_ctor_set(v_reuseFailAlloc_2425_, 2, v_opts_2402_);
lean_ctor_set(v_reuseFailAlloc_2425_, 3, v_rootDir_x3f_2405_);
lean_ctor_set(v_reuseFailAlloc_2425_, 4, v_setupFileName_x3f_2406_);
lean_ctor_set(v_reuseFailAlloc_2425_, 5, v_oleanFileName_x3f_2407_);
lean_ctor_set(v_reuseFailAlloc_2425_, 6, v_ileanFileName_x3f_2408_);
lean_ctor_set(v_reuseFailAlloc_2425_, 7, v_cFileName_x3f_2409_);
lean_ctor_set(v_reuseFailAlloc_2425_, 8, v_bcFileName_x3f_2410_);
lean_ctor_set(v_reuseFailAlloc_2425_, 9, v_errorOnKinds_2412_);
lean_ctor_set(v_reuseFailAlloc_2425_, 10, v_incrSaveFileName_x3f_2414_);
lean_ctor_set(v_reuseFailAlloc_2425_, 11, v_incrLoadFileName_x3f_2415_);
lean_ctor_set(v_reuseFailAlloc_2425_, 12, v_incrHeaderSaveFileName_x3f_2416_);
lean_ctor_set_uint8(v_reuseFailAlloc_2425_, sizeof(void*)*13 + 8, v_component_2395_);
lean_ctor_set_uint8(v_reuseFailAlloc_2425_, sizeof(void*)*13 + 9, v_printPrefix_2396_);
lean_ctor_set_uint8(v_reuseFailAlloc_2425_, sizeof(void*)*13 + 10, v_printLibDir_2397_);
lean_ctor_set_uint8(v_reuseFailAlloc_2425_, sizeof(void*)*13 + 11, v_useStdin_2398_);
lean_ctor_set_uint8(v_reuseFailAlloc_2425_, sizeof(void*)*13 + 12, v_onlyDeps_2399_);
lean_ctor_set_uint8(v_reuseFailAlloc_2425_, sizeof(void*)*13 + 13, v_onlySrcDeps_2400_);
lean_ctor_set_uint8(v_reuseFailAlloc_2425_, sizeof(void*)*13 + 14, v_depsJson_2401_);
lean_ctor_set_uint32(v_reuseFailAlloc_2425_, sizeof(void*)*13, v_trustLevel_2403_);
lean_ctor_set_uint32(v_reuseFailAlloc_2425_, sizeof(void*)*13 + 4, v_numThreads_2404_);
lean_ctor_set_uint8(v_reuseFailAlloc_2425_, sizeof(void*)*13 + 15, v_jsonOutput_2411_);
lean_ctor_set_uint8(v_reuseFailAlloc_2425_, sizeof(void*)*13 + 16, v_printStats_2413_);
v___x_2423_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
lean_object* v___x_2424_; 
lean_ctor_set_uint8(v___x_2423_, sizeof(void*)*13 + 17, v___x_1186_);
v___x_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
return v___x_2424_;
}
}
}
}
else
{
lean_object* v_leanOpts_2427_; lean_object* v_forwardedArgs_2428_; uint8_t v_component_2429_; uint8_t v_printPrefix_2430_; uint8_t v_printLibDir_2431_; uint8_t v_onlyDeps_2432_; uint8_t v_onlySrcDeps_2433_; uint8_t v_depsJson_2434_; lean_object* v_opts_2435_; uint32_t v_trustLevel_2436_; uint32_t v_numThreads_2437_; lean_object* v_rootDir_x3f_2438_; lean_object* v_setupFileName_x3f_2439_; lean_object* v_oleanFileName_x3f_2440_; lean_object* v_ileanFileName_x3f_2441_; lean_object* v_cFileName_x3f_2442_; lean_object* v_bcFileName_x3f_2443_; uint8_t v_jsonOutput_2444_; lean_object* v_errorOnKinds_2445_; uint8_t v_printStats_2446_; uint8_t v_run_2447_; lean_object* v_incrSaveFileName_x3f_2448_; lean_object* v_incrLoadFileName_x3f_2449_; lean_object* v_incrHeaderSaveFileName_x3f_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2458_; 
lean_dec(v_optArg_x3f_943_);
v_leanOpts_2427_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_2428_ = lean_ctor_get(v_opts_941_, 1);
v_component_2429_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_2430_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_2431_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_onlyDeps_2432_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2433_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_2434_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_2435_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_2436_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_2437_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2438_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_2439_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_2440_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_2441_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_2442_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_2443_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_2444_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_2445_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_2446_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_2447_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2448_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_2449_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_2450_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2452_ = v_opts_941_;
v_isShared_2453_ = v_isSharedCheck_2458_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2450_);
lean_inc(v_incrLoadFileName_x3f_2449_);
lean_inc(v_incrSaveFileName_x3f_2448_);
lean_inc(v_errorOnKinds_2445_);
lean_inc(v_bcFileName_x3f_2443_);
lean_inc(v_cFileName_x3f_2442_);
lean_inc(v_ileanFileName_x3f_2441_);
lean_inc(v_oleanFileName_x3f_2440_);
lean_inc(v_setupFileName_x3f_2439_);
lean_inc(v_rootDir_x3f_2438_);
lean_inc(v_opts_2435_);
lean_inc(v_forwardedArgs_2428_);
lean_inc(v_leanOpts_2427_);
lean_dec(v_opts_941_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2458_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_leanOpts_2427_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_forwardedArgs_2428_);
lean_ctor_set(v_reuseFailAlloc_2457_, 2, v_opts_2435_);
lean_ctor_set(v_reuseFailAlloc_2457_, 3, v_rootDir_x3f_2438_);
lean_ctor_set(v_reuseFailAlloc_2457_, 4, v_setupFileName_x3f_2439_);
lean_ctor_set(v_reuseFailAlloc_2457_, 5, v_oleanFileName_x3f_2440_);
lean_ctor_set(v_reuseFailAlloc_2457_, 6, v_ileanFileName_x3f_2441_);
lean_ctor_set(v_reuseFailAlloc_2457_, 7, v_cFileName_x3f_2442_);
lean_ctor_set(v_reuseFailAlloc_2457_, 8, v_bcFileName_x3f_2443_);
lean_ctor_set(v_reuseFailAlloc_2457_, 9, v_errorOnKinds_2445_);
lean_ctor_set(v_reuseFailAlloc_2457_, 10, v_incrSaveFileName_x3f_2448_);
lean_ctor_set(v_reuseFailAlloc_2457_, 11, v_incrLoadFileName_x3f_2449_);
lean_ctor_set(v_reuseFailAlloc_2457_, 12, v_incrHeaderSaveFileName_x3f_2450_);
lean_ctor_set_uint8(v_reuseFailAlloc_2457_, sizeof(void*)*13 + 8, v_component_2429_);
lean_ctor_set_uint8(v_reuseFailAlloc_2457_, sizeof(void*)*13 + 9, v_printPrefix_2430_);
lean_ctor_set_uint8(v_reuseFailAlloc_2457_, sizeof(void*)*13 + 10, v_printLibDir_2431_);
lean_ctor_set_uint8(v_reuseFailAlloc_2457_, sizeof(void*)*13 + 12, v_onlyDeps_2432_);
lean_ctor_set_uint8(v_reuseFailAlloc_2457_, sizeof(void*)*13 + 13, v_onlySrcDeps_2433_);
lean_ctor_set_uint8(v_reuseFailAlloc_2457_, sizeof(void*)*13 + 14, v_depsJson_2434_);
lean_ctor_set_uint32(v_reuseFailAlloc_2457_, sizeof(void*)*13, v_trustLevel_2436_);
lean_ctor_set_uint32(v_reuseFailAlloc_2457_, sizeof(void*)*13 + 4, v_numThreads_2437_);
lean_ctor_set_uint8(v_reuseFailAlloc_2457_, sizeof(void*)*13 + 15, v_jsonOutput_2444_);
lean_ctor_set_uint8(v_reuseFailAlloc_2457_, sizeof(void*)*13 + 16, v_printStats_2446_);
lean_ctor_set_uint8(v_reuseFailAlloc_2457_, sizeof(void*)*13 + 17, v_run_2447_);
v___x_2455_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
lean_object* v___x_2456_; 
lean_ctor_set_uint8(v___x_2455_, sizeof(void*)*13 + 11, v___x_1184_);
v___x_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2455_);
return v___x_2456_;
}
}
}
}
else
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27));
v___x_2460_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2459_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2522_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2463_ = v___x_2460_;
v_isShared_2464_ = v_isSharedCheck_2522_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2460_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2522_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2465_ = lean_unsigned_to_nat(0u);
v___x_2466_ = lean_string_utf8_byte_size(v_a_2461_);
lean_inc(v_a_2461_);
v___x_2467_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2467_, 0, v_a_2461_);
lean_ctor_set(v___x_2467_, 1, v___x_2465_);
lean_ctor_set(v___x_2467_, 2, v___x_2466_);
v___x_2468_ = l_String_Slice_toNat_x3f(v___x_2467_);
lean_dec_ref_known(v___x_2467_, 3);
if (lean_obj_tag(v___x_2468_) == 1)
{
lean_object* v_val_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; uint8_t v___x_2477_; 
v_val_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_val_2469_);
lean_dec_ref_known(v___x_2468_, 1);
v___x_2470_ = lean_unsigned_to_nat(4u);
v___x_2471_ = lean_unsigned_to_nat(2u);
v___x_2472_ = lean_nat_shiftr(v_val_2469_, v___x_2471_);
lean_dec(v_val_2469_);
v___x_2473_ = lean_nat_mul(v___x_2472_, v___x_2470_);
lean_dec(v___x_2472_);
v___x_2474_ = lean_unsigned_to_nat(1024u);
v___x_2475_ = lean_nat_mul(v___x_2473_, v___x_2474_);
lean_dec(v___x_2473_);
v___x_2476_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28, &l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28_once, _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28);
v___x_2477_ = lean_nat_dec_lt(v___x_2475_, v___x_2476_);
if (v___x_2477_ == 0)
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
lean_dec(v___x_2475_);
lean_del_object(v___x_2463_);
lean_dec(v_a_2461_);
lean_dec_ref(v_opts_941_);
v___x_2478_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29));
v___x_2479_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2478_);
lean_dec_ref(v___x_2479_);
goto v___jp_984_;
}
else
{
size_t v___x_2480_; lean_object* v___x_2481_; lean_object* v_leanOpts_2482_; lean_object* v_forwardedArgs_2483_; uint8_t v_component_2484_; uint8_t v_printPrefix_2485_; uint8_t v_printLibDir_2486_; uint8_t v_useStdin_2487_; uint8_t v_onlyDeps_2488_; uint8_t v_onlySrcDeps_2489_; uint8_t v_depsJson_2490_; lean_object* v_opts_2491_; uint32_t v_trustLevel_2492_; uint32_t v_numThreads_2493_; lean_object* v_rootDir_x3f_2494_; lean_object* v_setupFileName_x3f_2495_; lean_object* v_oleanFileName_x3f_2496_; lean_object* v_ileanFileName_x3f_2497_; lean_object* v_cFileName_x3f_2498_; lean_object* v_bcFileName_x3f_2499_; uint8_t v_jsonOutput_2500_; lean_object* v_errorOnKinds_2501_; uint8_t v_printStats_2502_; uint8_t v_run_2503_; lean_object* v_incrSaveFileName_x3f_2504_; lean_object* v_incrLoadFileName_x3f_2505_; lean_object* v_incrHeaderSaveFileName_x3f_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2519_; 
v___x_2480_ = lean_usize_of_nat(v___x_2475_);
lean_dec(v___x_2475_);
v___x_2481_ = lean_internal_set_thread_stack_size(v___x_2480_);
v_leanOpts_2482_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_2483_ = lean_ctor_get(v_opts_941_, 1);
v_component_2484_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_2485_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_2486_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_2487_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_2488_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2489_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_2490_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_2491_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_2492_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_2493_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2494_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_2495_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_2496_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_2497_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_2498_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_2499_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_2500_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_2501_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_2502_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_2503_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2504_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_2505_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_2506_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_2519_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2508_ = v_opts_941_;
v_isShared_2509_ = v_isSharedCheck_2519_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2506_);
lean_inc(v_incrLoadFileName_x3f_2505_);
lean_inc(v_incrSaveFileName_x3f_2504_);
lean_inc(v_errorOnKinds_2501_);
lean_inc(v_bcFileName_x3f_2499_);
lean_inc(v_cFileName_x3f_2498_);
lean_inc(v_ileanFileName_x3f_2497_);
lean_inc(v_oleanFileName_x3f_2496_);
lean_inc(v_setupFileName_x3f_2495_);
lean_inc(v_rootDir_x3f_2494_);
lean_inc(v_opts_2491_);
lean_inc(v_forwardedArgs_2483_);
lean_inc(v_leanOpts_2482_);
lean_dec(v_opts_941_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2519_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2514_; 
v___x_2510_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30));
v___x_2511_ = lean_string_append(v___x_2510_, v_a_2461_);
lean_dec(v_a_2461_);
v___x_2512_ = lean_array_push(v_forwardedArgs_2483_, v___x_2511_);
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 1, v___x_2512_);
v___x_2514_ = v___x_2508_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_leanOpts_2482_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v___x_2512_);
lean_ctor_set(v_reuseFailAlloc_2518_, 2, v_opts_2491_);
lean_ctor_set(v_reuseFailAlloc_2518_, 3, v_rootDir_x3f_2494_);
lean_ctor_set(v_reuseFailAlloc_2518_, 4, v_setupFileName_x3f_2495_);
lean_ctor_set(v_reuseFailAlloc_2518_, 5, v_oleanFileName_x3f_2496_);
lean_ctor_set(v_reuseFailAlloc_2518_, 6, v_ileanFileName_x3f_2497_);
lean_ctor_set(v_reuseFailAlloc_2518_, 7, v_cFileName_x3f_2498_);
lean_ctor_set(v_reuseFailAlloc_2518_, 8, v_bcFileName_x3f_2499_);
lean_ctor_set(v_reuseFailAlloc_2518_, 9, v_errorOnKinds_2501_);
lean_ctor_set(v_reuseFailAlloc_2518_, 10, v_incrSaveFileName_x3f_2504_);
lean_ctor_set(v_reuseFailAlloc_2518_, 11, v_incrLoadFileName_x3f_2505_);
lean_ctor_set(v_reuseFailAlloc_2518_, 12, v_incrHeaderSaveFileName_x3f_2506_);
lean_ctor_set_uint8(v_reuseFailAlloc_2518_, sizeof(void*)*13 + 8, v_component_2484_);
lean_ctor_set_uint8(v_reuseFailAlloc_2518_, sizeof(void*)*13 + 9, v_printPrefix_2485_);
lean_ctor_set_uint8(v_reuseFailAlloc_2518_, sizeof(void*)*13 + 10, v_printLibDir_2486_);
lean_ctor_set_uint8(v_reuseFailAlloc_2518_, sizeof(void*)*13 + 11, v_useStdin_2487_);
lean_ctor_set_uint8(v_reuseFailAlloc_2518_, sizeof(void*)*13 + 12, v_onlyDeps_2488_);
lean_ctor_set_uint8(v_reuseFailAlloc_2518_, sizeof(void*)*13 + 13, v_onlySrcDeps_2489_);
lean_ctor_set_uint8(v_reuseFailAlloc_2518_, sizeof(void*)*13 + 14, v_depsJson_2490_);
lean_ctor_set_uint32(v_reuseFailAlloc_2518_, sizeof(void*)*13, v_trustLevel_2492_);
lean_ctor_set_uint32(v_reuseFailAlloc_2518_, sizeof(void*)*13 + 4, v_numThreads_2493_);
lean_ctor_set_uint8(v_reuseFailAlloc_2518_, sizeof(void*)*13 + 15, v_jsonOutput_2500_);
lean_ctor_set_uint8(v_reuseFailAlloc_2518_, sizeof(void*)*13 + 16, v_printStats_2502_);
lean_ctor_set_uint8(v_reuseFailAlloc_2518_, sizeof(void*)*13 + 17, v_run_2503_);
v___x_2514_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2516_; 
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 0, v___x_2514_);
v___x_2516_ = v___x_2463_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2514_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
}
else
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
lean_dec(v___x_2468_);
lean_del_object(v___x_2463_);
lean_dec(v_a_2461_);
lean_dec_ref(v_opts_941_);
v___x_2520_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31));
v___x_2521_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2520_);
lean_dec_ref(v___x_2521_);
goto v___jp_981_;
}
}
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
lean_dec_ref(v_opts_941_);
v_a_2523_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_a_2523_);
lean_dec_ref_known(v___x_2460_, 1);
v___x_2527_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2528_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2527_);
lean_dec_ref(v___x_2528_);
goto v___jp_2524_;
v___jp_2524_:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = lean_io_error_to_string(v_a_2523_);
v___x_2526_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2525_);
lean_dec_ref(v___x_2526_);
goto v___jp_978_;
}
}
}
}
else
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32));
v___x_2530_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2529_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2571_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2533_ = v___x_2530_;
v_isShared_2534_ = v_isSharedCheck_2571_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2530_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2571_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v_leanOpts_2535_; lean_object* v_forwardedArgs_2536_; uint8_t v_component_2537_; uint8_t v_printPrefix_2538_; uint8_t v_printLibDir_2539_; uint8_t v_useStdin_2540_; uint8_t v_onlyDeps_2541_; uint8_t v_onlySrcDeps_2542_; uint8_t v_depsJson_2543_; lean_object* v_opts_2544_; uint32_t v_trustLevel_2545_; uint32_t v_numThreads_2546_; lean_object* v_rootDir_x3f_2547_; lean_object* v_setupFileName_x3f_2548_; lean_object* v_oleanFileName_x3f_2549_; lean_object* v_ileanFileName_x3f_2550_; lean_object* v_cFileName_x3f_2551_; uint8_t v_jsonOutput_2552_; lean_object* v_errorOnKinds_2553_; uint8_t v_printStats_2554_; uint8_t v_run_2555_; lean_object* v_incrSaveFileName_x3f_2556_; lean_object* v_incrLoadFileName_x3f_2557_; lean_object* v_incrHeaderSaveFileName_x3f_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2569_; 
v_leanOpts_2535_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_2536_ = lean_ctor_get(v_opts_941_, 1);
v_component_2537_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_2538_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_2539_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_2540_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_2541_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2542_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_2543_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_2544_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_2545_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_2546_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2547_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_2548_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_2549_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_2550_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_2551_ = lean_ctor_get(v_opts_941_, 7);
v_jsonOutput_2552_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_2553_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_2554_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_2555_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2556_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_2557_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_2558_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_2569_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_2569_ == 0)
{
lean_object* v_unused_2570_; 
v_unused_2570_ = lean_ctor_get(v_opts_941_, 8);
lean_dec(v_unused_2570_);
v___x_2560_ = v_opts_941_;
v_isShared_2561_ = v_isSharedCheck_2569_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2558_);
lean_inc(v_incrLoadFileName_x3f_2557_);
lean_inc(v_incrSaveFileName_x3f_2556_);
lean_inc(v_errorOnKinds_2553_);
lean_inc(v_cFileName_x3f_2551_);
lean_inc(v_ileanFileName_x3f_2550_);
lean_inc(v_oleanFileName_x3f_2549_);
lean_inc(v_setupFileName_x3f_2548_);
lean_inc(v_rootDir_x3f_2547_);
lean_inc(v_opts_2544_);
lean_inc(v_forwardedArgs_2536_);
lean_inc(v_leanOpts_2535_);
lean_dec(v_opts_941_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2569_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2562_; lean_object* v___x_2564_; 
v___x_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2562_, 0, v_a_2531_);
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 8, v___x_2562_);
v___x_2564_ = v___x_2560_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_leanOpts_2535_);
lean_ctor_set(v_reuseFailAlloc_2568_, 1, v_forwardedArgs_2536_);
lean_ctor_set(v_reuseFailAlloc_2568_, 2, v_opts_2544_);
lean_ctor_set(v_reuseFailAlloc_2568_, 3, v_rootDir_x3f_2547_);
lean_ctor_set(v_reuseFailAlloc_2568_, 4, v_setupFileName_x3f_2548_);
lean_ctor_set(v_reuseFailAlloc_2568_, 5, v_oleanFileName_x3f_2549_);
lean_ctor_set(v_reuseFailAlloc_2568_, 6, v_ileanFileName_x3f_2550_);
lean_ctor_set(v_reuseFailAlloc_2568_, 7, v_cFileName_x3f_2551_);
lean_ctor_set(v_reuseFailAlloc_2568_, 8, v___x_2562_);
lean_ctor_set(v_reuseFailAlloc_2568_, 9, v_errorOnKinds_2553_);
lean_ctor_set(v_reuseFailAlloc_2568_, 10, v_incrSaveFileName_x3f_2556_);
lean_ctor_set(v_reuseFailAlloc_2568_, 11, v_incrLoadFileName_x3f_2557_);
lean_ctor_set(v_reuseFailAlloc_2568_, 12, v_incrHeaderSaveFileName_x3f_2558_);
lean_ctor_set_uint8(v_reuseFailAlloc_2568_, sizeof(void*)*13 + 8, v_component_2537_);
lean_ctor_set_uint8(v_reuseFailAlloc_2568_, sizeof(void*)*13 + 9, v_printPrefix_2538_);
lean_ctor_set_uint8(v_reuseFailAlloc_2568_, sizeof(void*)*13 + 10, v_printLibDir_2539_);
lean_ctor_set_uint8(v_reuseFailAlloc_2568_, sizeof(void*)*13 + 11, v_useStdin_2540_);
lean_ctor_set_uint8(v_reuseFailAlloc_2568_, sizeof(void*)*13 + 12, v_onlyDeps_2541_);
lean_ctor_set_uint8(v_reuseFailAlloc_2568_, sizeof(void*)*13 + 13, v_onlySrcDeps_2542_);
lean_ctor_set_uint8(v_reuseFailAlloc_2568_, sizeof(void*)*13 + 14, v_depsJson_2543_);
lean_ctor_set_uint32(v_reuseFailAlloc_2568_, sizeof(void*)*13, v_trustLevel_2545_);
lean_ctor_set_uint32(v_reuseFailAlloc_2568_, sizeof(void*)*13 + 4, v_numThreads_2546_);
lean_ctor_set_uint8(v_reuseFailAlloc_2568_, sizeof(void*)*13 + 15, v_jsonOutput_2552_);
lean_ctor_set_uint8(v_reuseFailAlloc_2568_, sizeof(void*)*13 + 16, v_printStats_2554_);
lean_ctor_set_uint8(v_reuseFailAlloc_2568_, sizeof(void*)*13 + 17, v_run_2555_);
v___x_2564_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
lean_object* v___x_2566_; 
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 0, v___x_2564_);
v___x_2566_ = v___x_2533_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2564_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
lean_dec_ref(v_opts_941_);
v_a_2572_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_a_2572_);
lean_dec_ref_known(v___x_2530_, 1);
v___x_2576_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2577_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2576_);
lean_dec_ref(v___x_2577_);
goto v___jp_2573_;
v___jp_2573_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2574_ = lean_io_error_to_string(v_a_2572_);
v___x_2575_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2574_);
lean_dec_ref(v___x_2575_);
goto v___jp_1142_;
}
}
}
}
else
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2578_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33));
v___x_2579_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2578_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2620_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2582_ = v___x_2579_;
v_isShared_2583_ = v_isSharedCheck_2620_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2579_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2620_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v_leanOpts_2584_; lean_object* v_forwardedArgs_2585_; uint8_t v_component_2586_; uint8_t v_printPrefix_2587_; uint8_t v_printLibDir_2588_; uint8_t v_useStdin_2589_; uint8_t v_onlyDeps_2590_; uint8_t v_onlySrcDeps_2591_; uint8_t v_depsJson_2592_; lean_object* v_opts_2593_; uint32_t v_trustLevel_2594_; uint32_t v_numThreads_2595_; lean_object* v_rootDir_x3f_2596_; lean_object* v_setupFileName_x3f_2597_; lean_object* v_oleanFileName_x3f_2598_; lean_object* v_ileanFileName_x3f_2599_; lean_object* v_bcFileName_x3f_2600_; uint8_t v_jsonOutput_2601_; lean_object* v_errorOnKinds_2602_; uint8_t v_printStats_2603_; uint8_t v_run_2604_; lean_object* v_incrSaveFileName_x3f_2605_; lean_object* v_incrLoadFileName_x3f_2606_; lean_object* v_incrHeaderSaveFileName_x3f_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2618_; 
v_leanOpts_2584_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_2585_ = lean_ctor_get(v_opts_941_, 1);
v_component_2586_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_2587_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_2588_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_2589_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_2590_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2591_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_2592_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_2593_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_2594_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_numThreads_2595_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2596_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_2597_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_2598_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_2599_ = lean_ctor_get(v_opts_941_, 6);
v_bcFileName_x3f_2600_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_2601_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_2602_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_2603_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_2604_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2605_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_2606_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_2607_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_2618_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_2618_ == 0)
{
lean_object* v_unused_2619_; 
v_unused_2619_ = lean_ctor_get(v_opts_941_, 7);
lean_dec(v_unused_2619_);
v___x_2609_ = v_opts_941_;
v_isShared_2610_ = v_isSharedCheck_2618_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2607_);
lean_inc(v_incrLoadFileName_x3f_2606_);
lean_inc(v_incrSaveFileName_x3f_2605_);
lean_inc(v_errorOnKinds_2602_);
lean_inc(v_bcFileName_x3f_2600_);
lean_inc(v_ileanFileName_x3f_2599_);
lean_inc(v_oleanFileName_x3f_2598_);
lean_inc(v_setupFileName_x3f_2597_);
lean_inc(v_rootDir_x3f_2596_);
lean_inc(v_opts_2593_);
lean_inc(v_forwardedArgs_2585_);
lean_inc(v_leanOpts_2584_);
lean_dec(v_opts_941_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2618_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2611_; lean_object* v___x_2613_; 
v___x_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2611_, 0, v_a_2580_);
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 7, v___x_2611_);
v___x_2613_ = v___x_2609_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_leanOpts_2584_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v_forwardedArgs_2585_);
lean_ctor_set(v_reuseFailAlloc_2617_, 2, v_opts_2593_);
lean_ctor_set(v_reuseFailAlloc_2617_, 3, v_rootDir_x3f_2596_);
lean_ctor_set(v_reuseFailAlloc_2617_, 4, v_setupFileName_x3f_2597_);
lean_ctor_set(v_reuseFailAlloc_2617_, 5, v_oleanFileName_x3f_2598_);
lean_ctor_set(v_reuseFailAlloc_2617_, 6, v_ileanFileName_x3f_2599_);
lean_ctor_set(v_reuseFailAlloc_2617_, 7, v___x_2611_);
lean_ctor_set(v_reuseFailAlloc_2617_, 8, v_bcFileName_x3f_2600_);
lean_ctor_set(v_reuseFailAlloc_2617_, 9, v_errorOnKinds_2602_);
lean_ctor_set(v_reuseFailAlloc_2617_, 10, v_incrSaveFileName_x3f_2605_);
lean_ctor_set(v_reuseFailAlloc_2617_, 11, v_incrLoadFileName_x3f_2606_);
lean_ctor_set(v_reuseFailAlloc_2617_, 12, v_incrHeaderSaveFileName_x3f_2607_);
lean_ctor_set_uint8(v_reuseFailAlloc_2617_, sizeof(void*)*13 + 8, v_component_2586_);
lean_ctor_set_uint8(v_reuseFailAlloc_2617_, sizeof(void*)*13 + 9, v_printPrefix_2587_);
lean_ctor_set_uint8(v_reuseFailAlloc_2617_, sizeof(void*)*13 + 10, v_printLibDir_2588_);
lean_ctor_set_uint8(v_reuseFailAlloc_2617_, sizeof(void*)*13 + 11, v_useStdin_2589_);
lean_ctor_set_uint8(v_reuseFailAlloc_2617_, sizeof(void*)*13 + 12, v_onlyDeps_2590_);
lean_ctor_set_uint8(v_reuseFailAlloc_2617_, sizeof(void*)*13 + 13, v_onlySrcDeps_2591_);
lean_ctor_set_uint8(v_reuseFailAlloc_2617_, sizeof(void*)*13 + 14, v_depsJson_2592_);
lean_ctor_set_uint32(v_reuseFailAlloc_2617_, sizeof(void*)*13, v_trustLevel_2594_);
lean_ctor_set_uint32(v_reuseFailAlloc_2617_, sizeof(void*)*13 + 4, v_numThreads_2595_);
lean_ctor_set_uint8(v_reuseFailAlloc_2617_, sizeof(void*)*13 + 15, v_jsonOutput_2601_);
lean_ctor_set_uint8(v_reuseFailAlloc_2617_, sizeof(void*)*13 + 16, v_printStats_2603_);
lean_ctor_set_uint8(v_reuseFailAlloc_2617_, sizeof(void*)*13 + 17, v_run_2604_);
v___x_2613_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
lean_object* v___x_2615_; 
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 0, v___x_2613_);
v___x_2615_ = v___x_2582_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2613_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
lean_dec_ref(v_opts_941_);
v_a_2621_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2621_);
lean_dec_ref_known(v___x_2579_, 1);
v___x_2625_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2626_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2625_);
lean_dec_ref(v___x_2626_);
goto v___jp_2622_;
v___jp_2622_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = lean_io_error_to_string(v_a_2621_);
v___x_2624_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2623_);
lean_dec_ref(v___x_2624_);
goto v___jp_972_;
}
}
}
}
else
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
lean_dec(v_optArg_x3f_943_);
lean_dec_ref(v_opts_941_);
v___x_2627_ = l___private_Lean_Shell_0__Lean_featuresString;
v___x_2628_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2627_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2636_; 
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2636_ == 0)
{
lean_object* v_unused_2637_; 
v_unused_2637_ = lean_ctor_get(v___x_2628_, 0);
lean_dec(v_unused_2637_);
v___x_2630_ = v___x_2628_;
v_isShared_2631_ = v_isSharedCheck_2636_;
goto v_resetjp_2629_;
}
else
{
lean_dec(v___x_2628_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2636_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; lean_object* v___x_2634_; 
v___x_2632_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2631_ == 0)
{
lean_ctor_set_tag(v___x_2630_, 1);
lean_ctor_set(v___x_2630_, 0, v___x_2632_);
v___x_2634_ = v___x_2630_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2632_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v_a_2638_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_a_2638_);
lean_dec_ref_known(v___x_2628_, 1);
v___x_2642_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2643_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2642_);
lean_dec_ref(v___x_2643_);
goto v___jp_2639_;
v___jp_2639_:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = lean_io_error_to_string(v_a_2638_);
v___x_2641_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2640_);
lean_dec_ref(v___x_2641_);
goto v___jp_1148_;
}
}
}
}
else
{
lean_object* v___x_2644_; 
lean_dec(v_optArg_x3f_943_);
lean_dec_ref(v_opts_941_);
v___x_2644_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1172_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2652_; 
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2652_ == 0)
{
lean_object* v_unused_2653_; 
v_unused_2653_ = lean_ctor_get(v___x_2644_, 0);
lean_dec(v_unused_2653_);
v___x_2646_ = v___x_2644_;
v_isShared_2647_ = v_isSharedCheck_2652_;
goto v_resetjp_2645_;
}
else
{
lean_dec(v___x_2644_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2652_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2648_; lean_object* v___x_2650_; 
v___x_2648_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2647_ == 0)
{
lean_ctor_set_tag(v___x_2646_, 1);
lean_ctor_set(v___x_2646_, 0, v___x_2648_);
v___x_2650_ = v___x_2646_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2648_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v_a_2654_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_a_2654_);
lean_dec_ref_known(v___x_2644_, 1);
v___x_2658_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2659_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2658_);
lean_dec_ref(v___x_2659_);
goto v___jp_2655_;
v___jp_2655_:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2656_ = lean_io_error_to_string(v_a_2654_);
v___x_2657_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2656_);
lean_dec_ref(v___x_2657_);
goto v___jp_966_;
}
}
}
}
else
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
lean_dec(v_optArg_x3f_943_);
lean_dec_ref(v_opts_941_);
v___x_2660_ = l_Lean_githash;
v___x_2661_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2660_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2669_; 
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2669_ == 0)
{
lean_object* v_unused_2670_; 
v_unused_2670_ = lean_ctor_get(v___x_2661_, 0);
lean_dec(v_unused_2670_);
v___x_2663_ = v___x_2661_;
v_isShared_2664_ = v_isSharedCheck_2669_;
goto v_resetjp_2662_;
}
else
{
lean_dec(v___x_2661_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2669_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2665_; lean_object* v___x_2667_; 
v___x_2665_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2664_ == 0)
{
lean_ctor_set_tag(v___x_2663_, 1);
lean_ctor_set(v___x_2663_, 0, v___x_2665_);
v___x_2667_ = v___x_2663_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2665_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
else
{
lean_object* v_a_2671_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v_a_2671_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2671_);
lean_dec_ref_known(v___x_2661_, 1);
v___x_2675_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2676_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2675_);
lean_dec_ref(v___x_2676_);
goto v___jp_2672_;
v___jp_2672_:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2673_ = lean_io_error_to_string(v_a_2671_);
v___x_2674_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2673_);
lean_dec_ref(v___x_2674_);
goto v___jp_1154_;
}
}
}
}
else
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
lean_dec(v_optArg_x3f_943_);
lean_dec_ref(v_opts_941_);
v___x_2677_ = l___private_Lean_Shell_0__Lean_shortVersionString;
v___x_2678_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2677_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2686_; 
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2686_ == 0)
{
lean_object* v_unused_2687_; 
v_unused_2687_ = lean_ctor_get(v___x_2678_, 0);
lean_dec(v_unused_2687_);
v___x_2680_ = v___x_2678_;
v_isShared_2681_ = v_isSharedCheck_2686_;
goto v_resetjp_2679_;
}
else
{
lean_dec(v___x_2678_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2686_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2682_; lean_object* v___x_2684_; 
v___x_2682_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2681_ == 0)
{
lean_ctor_set_tag(v___x_2680_, 1);
lean_ctor_set(v___x_2680_, 0, v___x_2682_);
v___x_2684_ = v___x_2680_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2682_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v_a_2688_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2688_);
lean_dec_ref_known(v___x_2678_, 1);
v___x_2692_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2693_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2692_);
lean_dec_ref(v___x_2693_);
goto v___jp_2689_;
v___jp_2689_:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2690_ = lean_io_error_to_string(v_a_2688_);
v___x_2691_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2690_);
lean_dec_ref(v___x_2691_);
goto v___jp_960_;
}
}
}
}
else
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
lean_dec(v_optArg_x3f_943_);
lean_dec_ref(v_opts_941_);
v___x_2694_ = l___private_Lean_Shell_0__Lean_versionHeader;
v___x_2695_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2694_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2703_; 
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2703_ == 0)
{
lean_object* v_unused_2704_; 
v_unused_2704_ = lean_ctor_get(v___x_2695_, 0);
lean_dec(v_unused_2704_);
v___x_2697_ = v___x_2695_;
v_isShared_2698_ = v_isSharedCheck_2703_;
goto v_resetjp_2696_;
}
else
{
lean_dec(v___x_2695_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2703_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2699_; lean_object* v___x_2701_; 
v___x_2699_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2698_ == 0)
{
lean_ctor_set_tag(v___x_2697_, 1);
lean_ctor_set(v___x_2697_, 0, v___x_2699_);
v___x_2701_ = v___x_2697_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
else
{
lean_object* v_a_2705_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v_a_2705_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___x_2695_, 1);
v___x_2709_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2710_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2709_);
lean_dec_ref(v___x_2710_);
goto v___jp_2706_;
v___jp_2706_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2707_ = lean_io_error_to_string(v_a_2705_);
v___x_2708_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2707_);
lean_dec_ref(v___x_2708_);
goto v___jp_1160_;
}
}
}
}
else
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34));
v___x_2712_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2711_, v_optArg_x3f_943_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2766_; 
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2715_ = v___x_2712_;
v_isShared_2716_ = v_isSharedCheck_2766_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2712_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2766_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2717_ = lean_unsigned_to_nat(0u);
v___x_2718_ = lean_string_utf8_byte_size(v_a_2713_);
lean_inc(v_a_2713_);
v___x_2719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2719_, 0, v_a_2713_);
lean_ctor_set(v___x_2719_, 1, v___x_2717_);
lean_ctor_set(v___x_2719_, 2, v___x_2718_);
v___x_2720_ = l_String_Slice_toNat_x3f(v___x_2719_);
lean_dec_ref_known(v___x_2719_, 3);
if (lean_obj_tag(v___x_2720_) == 1)
{
lean_object* v_val_2721_; lean_object* v___x_2722_; uint8_t v___x_2723_; 
v_val_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_val_2721_);
lean_dec_ref_known(v___x_2720_, 1);
v___x_2722_ = lean_cstr_to_nat("4294967296");
v___x_2723_ = lean_nat_dec_lt(v_val_2721_, v___x_2722_);
if (v___x_2723_ == 0)
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
lean_dec(v_val_2721_);
lean_del_object(v___x_2715_);
lean_dec(v_a_2713_);
lean_dec_ref(v_opts_941_);
v___x_2724_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__35));
v___x_2725_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2724_);
lean_dec_ref(v___x_2725_);
goto v___jp_954_;
}
else
{
lean_object* v_leanOpts_2726_; lean_object* v_forwardedArgs_2727_; uint8_t v_component_2728_; uint8_t v_printPrefix_2729_; uint8_t v_printLibDir_2730_; uint8_t v_useStdin_2731_; uint8_t v_onlyDeps_2732_; uint8_t v_onlySrcDeps_2733_; uint8_t v_depsJson_2734_; lean_object* v_opts_2735_; uint32_t v_trustLevel_2736_; lean_object* v_rootDir_x3f_2737_; lean_object* v_setupFileName_x3f_2738_; lean_object* v_oleanFileName_x3f_2739_; lean_object* v_ileanFileName_x3f_2740_; lean_object* v_cFileName_x3f_2741_; lean_object* v_bcFileName_x3f_2742_; uint8_t v_jsonOutput_2743_; lean_object* v_errorOnKinds_2744_; uint8_t v_printStats_2745_; uint8_t v_run_2746_; lean_object* v_incrSaveFileName_x3f_2747_; lean_object* v_incrLoadFileName_x3f_2748_; lean_object* v_incrHeaderSaveFileName_x3f_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2763_; 
v_leanOpts_2726_ = lean_ctor_get(v_opts_941_, 0);
v_forwardedArgs_2727_ = lean_ctor_get(v_opts_941_, 1);
v_component_2728_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 8);
v_printPrefix_2729_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 9);
v_printLibDir_2730_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 10);
v_useStdin_2731_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 11);
v_onlyDeps_2732_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2733_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 13);
v_depsJson_2734_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 14);
v_opts_2735_ = lean_ctor_get(v_opts_941_, 2);
v_trustLevel_2736_ = lean_ctor_get_uint32(v_opts_941_, sizeof(void*)*13);
v_rootDir_x3f_2737_ = lean_ctor_get(v_opts_941_, 3);
v_setupFileName_x3f_2738_ = lean_ctor_get(v_opts_941_, 4);
v_oleanFileName_x3f_2739_ = lean_ctor_get(v_opts_941_, 5);
v_ileanFileName_x3f_2740_ = lean_ctor_get(v_opts_941_, 6);
v_cFileName_x3f_2741_ = lean_ctor_get(v_opts_941_, 7);
v_bcFileName_x3f_2742_ = lean_ctor_get(v_opts_941_, 8);
v_jsonOutput_2743_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 15);
v_errorOnKinds_2744_ = lean_ctor_get(v_opts_941_, 9);
v_printStats_2745_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 16);
v_run_2746_ = lean_ctor_get_uint8(v_opts_941_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2747_ = lean_ctor_get(v_opts_941_, 10);
v_incrLoadFileName_x3f_2748_ = lean_ctor_get(v_opts_941_, 11);
v_incrHeaderSaveFileName_x3f_2749_ = lean_ctor_get(v_opts_941_, 12);
v_isSharedCheck_2763_ = !lean_is_exclusive(v_opts_941_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2751_ = v_opts_941_;
v_isShared_2752_ = v_isSharedCheck_2763_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2749_);
lean_inc(v_incrLoadFileName_x3f_2748_);
lean_inc(v_incrSaveFileName_x3f_2747_);
lean_inc(v_errorOnKinds_2744_);
lean_inc(v_bcFileName_x3f_2742_);
lean_inc(v_cFileName_x3f_2741_);
lean_inc(v_ileanFileName_x3f_2740_);
lean_inc(v_oleanFileName_x3f_2739_);
lean_inc(v_setupFileName_x3f_2738_);
lean_inc(v_rootDir_x3f_2737_);
lean_inc(v_opts_2735_);
lean_inc(v_forwardedArgs_2727_);
lean_inc(v_leanOpts_2726_);
lean_dec(v_opts_941_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2763_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
uint32_t v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2758_; 
v___x_2753_ = lean_uint32_of_nat(v_val_2721_);
lean_dec(v_val_2721_);
v___x_2754_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__36));
v___x_2755_ = lean_string_append(v___x_2754_, v_a_2713_);
lean_dec(v_a_2713_);
v___x_2756_ = lean_array_push(v_forwardedArgs_2727_, v___x_2755_);
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 1, v___x_2756_);
v___x_2758_ = v___x_2751_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_leanOpts_2726_);
lean_ctor_set(v_reuseFailAlloc_2762_, 1, v___x_2756_);
lean_ctor_set(v_reuseFailAlloc_2762_, 2, v_opts_2735_);
lean_ctor_set(v_reuseFailAlloc_2762_, 3, v_rootDir_x3f_2737_);
lean_ctor_set(v_reuseFailAlloc_2762_, 4, v_setupFileName_x3f_2738_);
lean_ctor_set(v_reuseFailAlloc_2762_, 5, v_oleanFileName_x3f_2739_);
lean_ctor_set(v_reuseFailAlloc_2762_, 6, v_ileanFileName_x3f_2740_);
lean_ctor_set(v_reuseFailAlloc_2762_, 7, v_cFileName_x3f_2741_);
lean_ctor_set(v_reuseFailAlloc_2762_, 8, v_bcFileName_x3f_2742_);
lean_ctor_set(v_reuseFailAlloc_2762_, 9, v_errorOnKinds_2744_);
lean_ctor_set(v_reuseFailAlloc_2762_, 10, v_incrSaveFileName_x3f_2747_);
lean_ctor_set(v_reuseFailAlloc_2762_, 11, v_incrLoadFileName_x3f_2748_);
lean_ctor_set(v_reuseFailAlloc_2762_, 12, v_incrHeaderSaveFileName_x3f_2749_);
lean_ctor_set_uint8(v_reuseFailAlloc_2762_, sizeof(void*)*13 + 8, v_component_2728_);
lean_ctor_set_uint8(v_reuseFailAlloc_2762_, sizeof(void*)*13 + 9, v_printPrefix_2729_);
lean_ctor_set_uint8(v_reuseFailAlloc_2762_, sizeof(void*)*13 + 10, v_printLibDir_2730_);
lean_ctor_set_uint8(v_reuseFailAlloc_2762_, sizeof(void*)*13 + 11, v_useStdin_2731_);
lean_ctor_set_uint8(v_reuseFailAlloc_2762_, sizeof(void*)*13 + 12, v_onlyDeps_2732_);
lean_ctor_set_uint8(v_reuseFailAlloc_2762_, sizeof(void*)*13 + 13, v_onlySrcDeps_2733_);
lean_ctor_set_uint8(v_reuseFailAlloc_2762_, sizeof(void*)*13 + 14, v_depsJson_2734_);
lean_ctor_set_uint32(v_reuseFailAlloc_2762_, sizeof(void*)*13, v_trustLevel_2736_);
lean_ctor_set_uint8(v_reuseFailAlloc_2762_, sizeof(void*)*13 + 15, v_jsonOutput_2743_);
lean_ctor_set_uint8(v_reuseFailAlloc_2762_, sizeof(void*)*13 + 16, v_printStats_2745_);
lean_ctor_set_uint8(v_reuseFailAlloc_2762_, sizeof(void*)*13 + 17, v_run_2746_);
v___x_2758_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
lean_object* v___x_2760_; 
lean_ctor_set_uint32(v___x_2758_, sizeof(void*)*13 + 4, v___x_2753_);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 0, v___x_2758_);
v___x_2760_ = v___x_2715_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v___x_2758_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
}
else
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
lean_dec(v___x_2720_);
lean_del_object(v___x_2715_);
lean_dec(v_a_2713_);
lean_dec_ref(v_opts_941_);
v___x_2764_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__37));
v___x_2765_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2764_);
lean_dec_ref(v___x_2765_);
goto v___jp_951_;
}
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
lean_dec_ref(v_opts_941_);
v_a_2767_ = lean_ctor_get(v___x_2712_, 0);
lean_inc(v_a_2767_);
lean_dec_ref_known(v___x_2712_, 1);
v___x_2771_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2772_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2771_);
lean_dec_ref(v___x_2772_);
goto v___jp_2768_;
v___jp_2768_:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2769_ = lean_io_error_to_string(v_a_2767_);
v___x_2770_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2769_);
lean_dec_ref(v___x_2770_);
goto v___jp_948_;
}
}
}
}
else
{
lean_object* v___x_2773_; lean_object* v___x_2774_; 
lean_dec(v_optArg_x3f_943_);
v___x_2773_ = lean_internal_set_exit_on_panic(v___x_1164_);
v___x_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2774_, 0, v_opts_941_);
return v___x_2774_;
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
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
return v___x_1046_;
}
v___jp_1047_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1049_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1048_);
lean_dec_ref(v___x_1049_);
goto v___jp_1044_;
}
v___jp_1050_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
return v___x_1052_;
}
v___jp_1053_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1055_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1054_);
lean_dec_ref(v___x_1055_);
goto v___jp_1050_;
}
v___jp_1056_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_io_error_to_string(v___y_1057_);
v___x_1059_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1058_);
lean_dec_ref(v___x_1059_);
goto v___jp_1053_;
}
v___jp_1060_:
{
uint8_t v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = 1;
v___x_1062_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1061_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1070_; 
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1070_ == 0)
{
lean_object* v_unused_1071_; 
v_unused_1071_ = lean_ctor_get(v___x_1062_, 0);
lean_dec(v_unused_1071_);
v___x_1064_ = v___x_1062_;
v_isShared_1065_ = v_isSharedCheck_1070_;
goto v_resetjp_1063_;
}
else
{
lean_dec(v___x_1062_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1070_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1066_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_1065_ == 0)
{
lean_ctor_set_tag(v___x_1064_, 1);
lean_ctor_set(v___x_1064_, 0, v___x_1066_);
v___x_1068_ = v___x_1064_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_a_1072_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1062_, 1);
v___x_1073_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1074_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1073_);
lean_dec_ref(v___x_1074_);
v___y_1057_ = v_a_1072_;
goto v___jp_1056_;
}
}
v___jp_1075_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__0));
v___x_1077_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1076_);
lean_dec_ref(v___x_1077_);
goto v___jp_1060_;
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
v___x_1100_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1101_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1100_);
lean_dec_ref(v___x_1101_);
goto v___jp_1096_;
}
v___jp_1102_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_io_error_to_string(v___y_1103_);
v___x_1105_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1104_);
lean_dec_ref(v___x_1105_);
goto v___jp_1099_;
}
v___jp_1106_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
return v___x_1108_;
}
v___jp_1109_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1111_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1110_);
lean_dec_ref(v___x_1111_);
goto v___jp_1106_;
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
v___x_1122_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
return v___x_1123_;
}
v___jp_1124_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1126_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1125_);
lean_dec_ref(v___x_1126_);
goto v___jp_1121_;
}
v___jp_1127_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
return v___x_1129_;
}
v___jp_1130_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1132_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1131_);
lean_dec_ref(v___x_1132_);
goto v___jp_1127_;
}
v___jp_1133_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
return v___x_1135_;
}
v___jp_1136_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1138_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1137_);
lean_dec_ref(v___x_1138_);
goto v___jp_1133_;
}
v___jp_1139_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
return v___x_1141_;
}
v___jp_1142_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1144_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1143_);
lean_dec_ref(v___x_1144_);
goto v___jp_1139_;
}
v___jp_1145_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
return v___x_1147_;
}
v___jp_1148_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1150_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1149_);
lean_dec_ref(v___x_1150_);
goto v___jp_1145_;
}
v___jp_1151_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
return v___x_1153_;
}
v___jp_1154_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1156_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1155_);
lean_dec_ref(v___x_1156_);
goto v___jp_1151_;
}
v___jp_1157_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
return v___x_1159_;
}
v___jp_1160_:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1162_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1161_);
lean_dec_ref(v___x_1162_);
goto v___jp_1157_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed(lean_object* v_opts_2775_, lean_object* v_opt_2776_, lean_object* v_optArg_x3f_2777_, lean_object* v_a_2778_){
_start:
{
uint32_t v_opt_boxed_2779_; lean_object* v_res_2780_; 
v_opt_boxed_2779_ = lean_unbox_uint32(v_opt_2776_);
lean_dec(v_opt_2776_);
v_res_2780_ = lean_shell_options_process(v_opts_2775_, v_opt_boxed_2779_, v_optArg_x3f_2777_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(lean_object* v_opts_2781_, lean_object* v_opt_2782_){
_start:
{
lean_object* v_name_2783_; lean_object* v_defValue_2784_; lean_object* v_map_2785_; lean_object* v___x_2786_; 
v_name_2783_ = lean_ctor_get(v_opt_2782_, 0);
v_defValue_2784_ = lean_ctor_get(v_opt_2782_, 1);
v_map_2785_ = lean_ctor_get(v_opts_2781_, 0);
v___x_2786_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2785_, v_name_2783_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_inc(v_defValue_2784_);
return v_defValue_2784_;
}
else
{
lean_object* v_val_2787_; 
v_val_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_val_2787_);
lean_dec_ref_known(v___x_2786_, 1);
if (lean_obj_tag(v_val_2787_) == 3)
{
lean_object* v_v_2788_; 
v_v_2788_ = lean_ctor_get(v_val_2787_, 0);
lean_inc(v_v_2788_);
lean_dec_ref_known(v_val_2787_, 1);
return v_v_2788_;
}
else
{
lean_dec(v_val_2787_);
lean_inc(v_defValue_2784_);
return v_defValue_2784_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___boxed(lean_object* v_opts_2789_, lean_object* v_opt_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_opts_2789_, v_opt_2790_);
lean_dec_ref(v_opt_2790_);
lean_dec_ref(v_opts_2789_);
return v_res_2791_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2794_ = lean_string_utf8_byte_size(v___x_2793_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(lean_object* v_s_2795_){
_start:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; uint8_t v___x_2799_; 
v___x_2796_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2797_ = lean_string_utf8_byte_size(v_s_2795_);
v___x_2798_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1);
v___x_2799_ = lean_nat_dec_le(v___x_2798_, v___x_2797_);
if (v___x_2799_ == 0)
{
lean_object* v___x_2800_; 
lean_dec_ref(v_s_2795_);
v___x_2800_ = lean_box(0);
return v___x_2800_;
}
else
{
lean_object* v___x_2801_; uint8_t v___x_2802_; 
v___x_2801_ = lean_unsigned_to_nat(0u);
v___x_2802_ = lean_string_memcmp(v_s_2795_, v___x_2796_, v___x_2801_, v___x_2801_, v___x_2798_);
if (v___x_2802_ == 0)
{
lean_object* v___x_2803_; 
lean_dec_ref(v_s_2795_);
v___x_2803_ = lean_box(0);
return v___x_2803_;
}
else
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
lean_inc_ref(v_s_2795_);
v___x_2804_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2804_, 0, v_s_2795_);
lean_ctor_set(v___x_2804_, 1, v___x_2801_);
lean_ctor_set(v___x_2804_, 2, v___x_2797_);
v___x_2805_ = l_String_Slice_pos_x21(v___x_2804_, v___x_2798_);
lean_dec_ref_known(v___x_2804_, 3);
v___x_2806_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2806_, 0, v_s_2795_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
lean_ctor_set(v___x_2806_, 2, v___x_2797_);
v___x_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
return v___x_2807_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(lean_object* v_s_2808_, lean_object* v_pat_2809_){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v_s_2808_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___boxed(lean_object* v_s_2811_, lean_object* v_pat_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(v_s_2811_, v_pat_2812_);
lean_dec_ref(v_pat_2812_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object* v_x_2814_, lean_object* v_x_2815_, lean_object* v_v_2816_){
_start:
{
lean_inc_ref(v_v_2816_);
return v_v_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object* v_x_2817_, lean_object* v_x_2818_, lean_object* v_v_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l___private_Lean_Shell_0__Lean_shellMain___lam__0(v_x_2817_, v_x_2818_, v_v_2819_);
lean_dec_ref(v_v_2819_);
lean_dec_ref(v_x_2818_);
lean_dec(v_x_2817_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1(lean_object* v___x_2824_, lean_object* v___x_2825_, lean_object* v_mainModuleName_2826_, lean_object* v_a_2827_, uint8_t v___x_2828_, lean_object* v_fileName_2829_, lean_object* v___x_2830_, lean_object* v___x_2831_, lean_object* v___x_2832_, lean_object* v___x_2833_, lean_object* v___x_2834_, lean_object* v___x_2835_, lean_object* v___x_2836_, lean_object* v___x_2837_, uint8_t v_run_2838_, lean_object* v___x_2839_){
_start:
{
lean_object* v_a_2842_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v_env_2850_; lean_object* v___x_2851_; uint8_t v___x_2852_; lean_object* v_fileName_2854_; lean_object* v_fileMap_2855_; lean_object* v_currRecDepth_2856_; lean_object* v_ref_2857_; lean_object* v_currNamespace_2858_; lean_object* v_openDecls_2859_; lean_object* v_initHeartbeats_2860_; lean_object* v_maxHeartbeats_2861_; lean_object* v_quotContext_2862_; lean_object* v_currMacroScope_2863_; lean_object* v_cancelTk_x3f_2864_; uint8_t v_suppressElabErrors_2865_; lean_object* v_inheritedTraceOptions_2866_; lean_object* v___y_2867_; uint8_t v___y_2899_; uint8_t v___x_2920_; 
v___x_2845_ = lean_io_get_num_heartbeats();
v___x_2846_ = lean_st_mk_ref(v___x_2824_);
v___x_2847_ = l_Lean_inheritedTraceOptions;
v___x_2848_ = lean_st_ref_get(v___x_2847_);
v___x_2849_ = lean_st_ref_get(v___x_2846_);
v_env_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc_ref(v_env_2850_);
lean_dec(v___x_2849_);
v___x_2851_ = l_Lean_diagnostics;
v___x_2852_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v___x_2825_, v___x_2851_);
v___x_2920_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2850_);
lean_dec_ref(v_env_2850_);
if (v___x_2920_ == 0)
{
if (v___x_2852_ == 0)
{
uint8_t v___x_2921_; 
v___x_2921_ = 1;
v___y_2899_ = v___x_2921_;
goto v___jp_2898_;
}
else
{
v___y_2899_ = v___x_2920_;
goto v___jp_2898_;
}
}
else
{
v___y_2899_ = v___x_2852_;
goto v___jp_2898_;
}
v___jp_2841_:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = lean_mk_io_user_error(v_a_2842_);
v___x_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
return v___x_2844_;
}
v___jp_2853_:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2868_ = l_Lean_maxRecDepth;
v___x_2869_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_2825_, v___x_2868_);
v___x_2870_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2870_, 0, v_fileName_2854_);
lean_ctor_set(v___x_2870_, 1, v_fileMap_2855_);
lean_ctor_set(v___x_2870_, 2, v___x_2825_);
lean_ctor_set(v___x_2870_, 3, v_currRecDepth_2856_);
lean_ctor_set(v___x_2870_, 4, v___x_2869_);
lean_ctor_set(v___x_2870_, 5, v_ref_2857_);
lean_ctor_set(v___x_2870_, 6, v_currNamespace_2858_);
lean_ctor_set(v___x_2870_, 7, v_openDecls_2859_);
lean_ctor_set(v___x_2870_, 8, v_initHeartbeats_2860_);
lean_ctor_set(v___x_2870_, 9, v_maxHeartbeats_2861_);
lean_ctor_set(v___x_2870_, 10, v_quotContext_2862_);
lean_ctor_set(v___x_2870_, 11, v_currMacroScope_2863_);
lean_ctor_set(v___x_2870_, 12, v_cancelTk_x3f_2864_);
lean_ctor_set(v___x_2870_, 13, v_inheritedTraceOptions_2866_);
lean_ctor_set_uint8(v___x_2870_, sizeof(void*)*14, v___x_2852_);
lean_ctor_set_uint8(v___x_2870_, sizeof(void*)*14 + 1, v_suppressElabErrors_2865_);
v___x_2871_ = l_Lean_Compiler_LCNF_emitC(v_mainModuleName_2826_, v___x_2870_, v___y_2867_);
lean_dec(v___y_2867_);
lean_dec_ref_known(v___x_2870_, 14);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2871_, 1);
v___x_2873_ = lean_st_ref_get(v___x_2846_);
lean_dec(v___x_2846_);
lean_dec(v___x_2873_);
v___x_2874_ = lean_string_to_utf8(v_a_2872_);
lean_dec(v_a_2872_);
v___x_2875_ = lean_io_prim_handle_write(v_a_2827_, v___x_2874_);
lean_dec_ref(v___x_2874_);
return v___x_2875_;
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2897_; 
lean_dec(v___x_2846_);
v_a_2876_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2878_ = v___x_2871_;
v_isShared_2879_ = v_isSharedCheck_2897_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2871_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2897_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
if (lean_obj_tag(v_a_2876_) == 0)
{
lean_object* v_msg_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2884_; 
v_msg_2880_ = lean_ctor_get(v_a_2876_, 1);
lean_inc_ref(v_msg_2880_);
lean_dec_ref_known(v_a_2876_, 2);
v___x_2881_ = l_Lean_MessageData_toString(v_msg_2880_);
v___x_2882_ = lean_mk_io_user_error(v___x_2881_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2882_);
v___x_2884_ = v___x_2878_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2882_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
else
{
lean_object* v_id_2886_; lean_object* v___x_2887_; 
lean_del_object(v___x_2878_);
v_id_2886_ = lean_ctor_get(v_a_2876_, 0);
lean_inc(v_id_2886_);
lean_dec_ref_known(v_a_2876_, 2);
v___x_2887_ = l_Lean_InternalExceptionId_getName(v_id_2886_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
lean_dec(v_id_2886_);
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref_known(v___x_2887_, 1);
v___x_2889_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__0));
v___x_2890_ = l_Lean_Name_toString(v_a_2888_, v___x_2828_);
v___x_2891_ = lean_string_append(v___x_2889_, v___x_2890_);
lean_dec_ref(v___x_2890_);
v_a_2842_ = v___x_2891_;
goto v___jp_2841_;
}
else
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
lean_dec_ref_known(v___x_2887_, 1);
v___x_2892_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__1));
v___x_2893_ = l_Nat_reprFast(v_id_2886_);
v___x_2894_ = lean_string_append(v___x_2892_, v___x_2893_);
lean_dec_ref(v___x_2893_);
v___x_2895_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__2));
v___x_2896_ = lean_string_append(v___x_2894_, v___x_2895_);
v_a_2842_ = v___x_2896_;
goto v___jp_2841_;
}
}
}
}
}
v___jp_2898_:
{
uint8_t v___x_2900_; 
v___x_2900_ = lean_bool_not(v___y_2899_);
if (v___x_2900_ == 0)
{
lean_dec_ref(v___x_2839_);
lean_inc(v___x_2846_);
lean_inc(v___x_2833_);
v_fileName_2854_ = v_fileName_2829_;
v_fileMap_2855_ = v___x_2830_;
v_currRecDepth_2856_ = v___x_2831_;
v_ref_2857_ = v___x_2832_;
v_currNamespace_2858_ = v___x_2833_;
v_openDecls_2859_ = v___x_2834_;
v_initHeartbeats_2860_ = v___x_2845_;
v_maxHeartbeats_2861_ = v___x_2835_;
v_quotContext_2862_ = v___x_2833_;
v_currMacroScope_2863_ = v___x_2836_;
v_cancelTk_x3f_2864_ = v___x_2837_;
v_suppressElabErrors_2865_ = v_run_2838_;
v_inheritedTraceOptions_2866_ = v___x_2848_;
v___y_2867_ = v___x_2846_;
goto v___jp_2853_;
}
else
{
lean_object* v___x_2901_; lean_object* v_env_2902_; lean_object* v_nextMacroScope_2903_; lean_object* v_ngen_2904_; lean_object* v_auxDeclNGen_2905_; lean_object* v_traceState_2906_; lean_object* v_messages_2907_; lean_object* v_infoState_2908_; lean_object* v_snapshotTasks_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2918_; 
v___x_2901_ = lean_st_ref_take(v___x_2846_);
v_env_2902_ = lean_ctor_get(v___x_2901_, 0);
v_nextMacroScope_2903_ = lean_ctor_get(v___x_2901_, 1);
v_ngen_2904_ = lean_ctor_get(v___x_2901_, 2);
v_auxDeclNGen_2905_ = lean_ctor_get(v___x_2901_, 3);
v_traceState_2906_ = lean_ctor_get(v___x_2901_, 4);
v_messages_2907_ = lean_ctor_get(v___x_2901_, 6);
v_infoState_2908_ = lean_ctor_get(v___x_2901_, 7);
v_snapshotTasks_2909_ = lean_ctor_get(v___x_2901_, 8);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2918_ == 0)
{
lean_object* v_unused_2919_; 
v_unused_2919_ = lean_ctor_get(v___x_2901_, 5);
lean_dec(v_unused_2919_);
v___x_2911_ = v___x_2901_;
v_isShared_2912_ = v_isSharedCheck_2918_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_snapshotTasks_2909_);
lean_inc(v_infoState_2908_);
lean_inc(v_messages_2907_);
lean_inc(v_traceState_2906_);
lean_inc(v_auxDeclNGen_2905_);
lean_inc(v_ngen_2904_);
lean_inc(v_nextMacroScope_2903_);
lean_inc(v_env_2902_);
lean_dec(v___x_2901_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2918_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2913_; lean_object* v___x_2915_; 
v___x_2913_ = l_Lean_Kernel_enableDiag(v_env_2902_, v___x_2852_);
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 5, v___x_2839_);
lean_ctor_set(v___x_2911_, 0, v___x_2913_);
v___x_2915_ = v___x_2911_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___x_2913_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v_nextMacroScope_2903_);
lean_ctor_set(v_reuseFailAlloc_2917_, 2, v_ngen_2904_);
lean_ctor_set(v_reuseFailAlloc_2917_, 3, v_auxDeclNGen_2905_);
lean_ctor_set(v_reuseFailAlloc_2917_, 4, v_traceState_2906_);
lean_ctor_set(v_reuseFailAlloc_2917_, 5, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2917_, 6, v_messages_2907_);
lean_ctor_set(v_reuseFailAlloc_2917_, 7, v_infoState_2908_);
lean_ctor_set(v_reuseFailAlloc_2917_, 8, v_snapshotTasks_2909_);
v___x_2915_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
lean_object* v___x_2916_; 
v___x_2916_ = lean_st_ref_set(v___x_2846_, v___x_2915_);
lean_inc(v___x_2846_);
lean_inc(v___x_2833_);
v_fileName_2854_ = v_fileName_2829_;
v_fileMap_2855_ = v___x_2830_;
v_currRecDepth_2856_ = v___x_2831_;
v_ref_2857_ = v___x_2832_;
v_currNamespace_2858_ = v___x_2833_;
v_openDecls_2859_ = v___x_2834_;
v_initHeartbeats_2860_ = v___x_2845_;
v_maxHeartbeats_2861_ = v___x_2835_;
v_quotContext_2862_ = v___x_2833_;
v_currMacroScope_2863_ = v___x_2836_;
v_cancelTk_x3f_2864_ = v___x_2837_;
v_suppressElabErrors_2865_ = v_run_2838_;
v_inheritedTraceOptions_2866_ = v___x_2848_;
v___y_2867_ = v___x_2846_;
goto v___jp_2853_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed(lean_object** _args){
lean_object* v___x_2922_ = _args[0];
lean_object* v___x_2923_ = _args[1];
lean_object* v_mainModuleName_2924_ = _args[2];
lean_object* v_a_2925_ = _args[3];
lean_object* v___x_2926_ = _args[4];
lean_object* v_fileName_2927_ = _args[5];
lean_object* v___x_2928_ = _args[6];
lean_object* v___x_2929_ = _args[7];
lean_object* v___x_2930_ = _args[8];
lean_object* v___x_2931_ = _args[9];
lean_object* v___x_2932_ = _args[10];
lean_object* v___x_2933_ = _args[11];
lean_object* v___x_2934_ = _args[12];
lean_object* v___x_2935_ = _args[13];
lean_object* v_run_2936_ = _args[14];
lean_object* v___x_2937_ = _args[15];
lean_object* v___y_2938_ = _args[16];
_start:
{
uint8_t v___x_21886__boxed_2939_; uint8_t v_run_boxed_2940_; lean_object* v_res_2941_; 
v___x_21886__boxed_2939_ = lean_unbox(v___x_2926_);
v_run_boxed_2940_ = lean_unbox(v_run_2936_);
v_res_2941_ = l___private_Lean_Shell_0__Lean_shellMain___lam__1(v___x_2922_, v___x_2923_, v_mainModuleName_2924_, v_a_2925_, v___x_21886__boxed_2939_, v_fileName_2927_, v___x_2928_, v___x_2929_, v___x_2930_, v___x_2931_, v___x_2932_, v___x_2933_, v___x_2934_, v___x_2935_, v_run_boxed_2940_, v___x_2937_);
lean_dec(v_a_2925_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(lean_object* v_val_2942_, lean_object* v_a_2943_, lean_object* v_b_2944_){
_start:
{
lean_object* v_str_2945_; lean_object* v_startInclusive_2946_; lean_object* v_endExclusive_2947_; lean_object* v___x_2948_; uint8_t v___x_2949_; 
v_str_2945_ = lean_ctor_get(v_val_2942_, 0);
v_startInclusive_2946_ = lean_ctor_get(v_val_2942_, 1);
v_endExclusive_2947_ = lean_ctor_get(v_val_2942_, 2);
v___x_2948_ = lean_nat_sub(v_endExclusive_2947_, v_startInclusive_2946_);
v___x_2949_ = lean_nat_dec_eq(v_a_2943_, v___x_2948_);
lean_dec(v___x_2948_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; uint32_t v___x_2951_; uint32_t v___x_2952_; uint8_t v___x_2953_; 
v___x_2950_ = lean_nat_add(v_startInclusive_2946_, v_a_2943_);
v___x_2951_ = lean_string_utf8_get_fast(v_str_2945_, v___x_2950_);
v___x_2952_ = 10;
v___x_2953_ = lean_uint32_dec_eq(v___x_2951_, v___x_2952_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
lean_dec(v_a_2943_);
v___x_2954_ = lean_box(0);
v___x_2955_ = lean_string_utf8_next_fast(v_str_2945_, v___x_2950_);
lean_dec(v___x_2950_);
v___x_2956_ = lean_nat_sub(v___x_2955_, v_startInclusive_2946_);
v_a_2943_ = v___x_2956_;
v_b_2944_ = v___x_2954_;
goto _start;
}
else
{
lean_object* v___x_2958_; 
lean_dec(v___x_2950_);
v___x_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2958_, 0, v_a_2943_);
return v___x_2958_;
}
}
else
{
lean_dec(v_a_2943_);
lean_inc(v_b_2944_);
return v_b_2944_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg___boxed(lean_object* v_val_2959_, lean_object* v_a_2960_, lean_object* v_b_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_2959_, v_a_2960_, v_b_2961_);
lean_dec(v_b_2961_);
lean_dec_ref(v_val_2959_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(lean_object* v_s_2963_){
_start:
{
uint32_t v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2965_ = 10;
v___x_2966_ = lean_string_push(v_s_2963_, v___x_2965_);
v___x_2967_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4___boxed(lean_object* v_s_2968_, lean_object* v_a_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_s_2968_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object* v_s_2971_){
_start:
{
uint32_t v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2973_ = 10;
v___x_2974_ = lean_string_push(v_s_2971_, v___x_2973_);
v___x_2975_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2974_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___boxed(lean_object* v_s_2976_, lean_object* v_a_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v_s_2976_);
return v_res_2978_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shellMain___closed__1(void){
_start:
{
lean_object* v___x_2980_; uint8_t v___x_2981_; 
v___x_2980_ = lean_box(0);
v___x_2981_ = lean_internal_has_address_sanitizer(v___x_2980_);
return v___x_2981_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__2(void){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = lean_box(0);
v___x_2983_ = lean_internal_get_option_overrides(v___x_2982_);
return v___x_2983_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__6(void){
_start:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2988_ = l_Lean_Options_empty;
v___x_2989_ = l_Lean_Core_getMaxHeartbeats(v___x_2988_);
return v___x_2989_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__7(void){
_start:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2990_ = lean_unsigned_to_nat(1u);
v___x_2991_ = l_Lean_firstFrontendMacroScope;
v___x_2992_ = lean_nat_add(v___x_2991_, v___x_2990_);
return v___x_2992_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__12(void){
_start:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3003_ = lean_unsigned_to_nat(32u);
v___x_3004_ = lean_mk_empty_array_with_capacity(v___x_3003_);
v___x_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3004_);
return v___x_3005_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13(void){
_start:
{
size_t v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3006_ = ((size_t)5ULL);
v___x_3007_ = lean_unsigned_to_nat(0u);
v___x_3008_ = lean_unsigned_to_nat(32u);
v___x_3009_ = lean_mk_empty_array_with_capacity(v___x_3008_);
v___x_3010_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__12, &l___private_Lean_Shell_0__Lean_shellMain___closed__12_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__12);
v___x_3011_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
lean_ctor_set(v___x_3011_, 1, v___x_3009_);
lean_ctor_set(v___x_3011_, 2, v___x_3007_);
lean_ctor_set(v___x_3011_, 3, v___x_3007_);
lean_ctor_set_usize(v___x_3011_, 4, v___x_3006_);
return v___x_3011_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14(void){
_start:
{
lean_object* v___x_3012_; uint64_t v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__13, &l___private_Lean_Shell_0__Lean_shellMain___closed__13_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13);
v___x_3013_ = 0ULL;
v___x_3014_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3014_, 0, v___x_3012_);
lean_ctor_set_uint64(v___x_3014_, sizeof(void*)*1, v___x_3013_);
return v___x_3014_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__15(void){
_start:
{
lean_object* v___x_3015_; 
v___x_3015_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3015_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16(void){
_start:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3016_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__15, &l___private_Lean_Shell_0__Lean_shellMain___closed__15_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__15);
v___x_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
return v___x_3017_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__17(void){
_start:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__16, &l___private_Lean_Shell_0__Lean_shellMain___closed__16_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16);
v___x_3019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
return v___x_3019_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__18(void){
_start:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3020_ = l_Lean_NameSet_empty;
v___x_3021_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__13, &l___private_Lean_Shell_0__Lean_shellMain___closed__13_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13);
v___x_3022_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3021_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
lean_ctor_set(v___x_3022_, 2, v___x_3020_);
return v___x_3022_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__19(void){
_start:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; uint8_t v___x_3025_; lean_object* v___x_3026_; 
v___x_3023_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__13, &l___private_Lean_Shell_0__Lean_shellMain___closed__13_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13);
v___x_3024_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__16, &l___private_Lean_Shell_0__Lean_shellMain___closed__16_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16);
v___x_3025_ = 1;
v___x_3026_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3026_, 0, v___x_3024_);
lean_ctor_set(v___x_3026_, 1, v___x_3024_);
lean_ctor_set(v___x_3026_, 2, v___x_3023_);
lean_ctor_set_uint8(v___x_3026_, sizeof(void*)*3, v___x_3025_);
return v___x_3026_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__24(void){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__23));
v___x_3033_ = lean_string_utf8_byte_size(v___x_3032_);
return v___x_3033_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__25(void){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3034_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__24, &l___private_Lean_Shell_0__Lean_shellMain___closed__24_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__24);
v___x_3035_ = lean_unsigned_to_nat(0u);
v___x_3036_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__23));
v___x_3037_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
lean_ctor_set(v___x_3037_, 1, v___x_3035_);
lean_ctor_set(v___x_3037_, 2, v___x_3034_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* lean_shell_main(lean_object* v_args_3041_, lean_object* v_opts_3042_){
_start:
{
lean_object* v_fns_3051_; uint8_t v_printPrefix_3070_; 
v_printPrefix_3070_ = lean_ctor_get_uint8(v_opts_3042_, sizeof(void*)*13 + 9);
if (v_printPrefix_3070_ == 0)
{
uint8_t v_printLibDir_3071_; 
v_printLibDir_3071_ = lean_ctor_get_uint8(v_opts_3042_, sizeof(void*)*13 + 10);
if (v_printLibDir_3071_ == 0)
{
lean_object* v_leanOpts_3072_; lean_object* v_forwardedArgs_3073_; uint8_t v_component_3074_; uint8_t v_useStdin_3075_; uint8_t v_onlyDeps_3076_; uint8_t v_onlySrcDeps_3077_; uint8_t v_depsJson_3078_; uint32_t v_trustLevel_3079_; lean_object* v_rootDir_x3f_3080_; lean_object* v_setupFileName_x3f_3081_; lean_object* v_oleanFileName_x3f_3082_; lean_object* v_ileanFileName_x3f_3083_; lean_object* v_cFileName_x3f_3084_; lean_object* v_bcFileName_x3f_3085_; uint8_t v_jsonOutput_3086_; lean_object* v_errorOnKinds_3087_; uint8_t v_printStats_3088_; uint8_t v_run_3089_; lean_object* v_incrSaveFileName_x3f_3090_; lean_object* v_incrLoadFileName_x3f_3091_; lean_object* v_incrHeaderSaveFileName_x3f_3092_; lean_object* v___f_3093_; lean_object* v___y_3095_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; uint8_t v___x_3137_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v_mainModuleName_3144_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v_contents_3245_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v_str_3275_; lean_object* v_startInclusive_3276_; lean_object* v_endExclusive_3277_; lean_object* v___y_3278_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v_fileName_3377_; lean_object* v___y_3382_; lean_object* v___y_3383_; uint8_t v___y_3384_; lean_object* v_fst_3444_; lean_object* v_snd_3445_; lean_object* v___x_3480_; lean_object* v_maxMemory_3481_; lean_object* v___x_3482_; uint8_t v___x_3483_; uint8_t v___x_3484_; 
v_leanOpts_3072_ = lean_ctor_get(v_opts_3042_, 0);
lean_inc_ref(v_leanOpts_3072_);
v_forwardedArgs_3073_ = lean_ctor_get(v_opts_3042_, 1);
lean_inc_ref(v_forwardedArgs_3073_);
v_component_3074_ = lean_ctor_get_uint8(v_opts_3042_, sizeof(void*)*13 + 8);
v_useStdin_3075_ = lean_ctor_get_uint8(v_opts_3042_, sizeof(void*)*13 + 11);
v_onlyDeps_3076_ = lean_ctor_get_uint8(v_opts_3042_, sizeof(void*)*13 + 12);
v_onlySrcDeps_3077_ = lean_ctor_get_uint8(v_opts_3042_, sizeof(void*)*13 + 13);
v_depsJson_3078_ = lean_ctor_get_uint8(v_opts_3042_, sizeof(void*)*13 + 14);
v_trustLevel_3079_ = lean_ctor_get_uint32(v_opts_3042_, sizeof(void*)*13);
v_rootDir_x3f_3080_ = lean_ctor_get(v_opts_3042_, 3);
lean_inc(v_rootDir_x3f_3080_);
v_setupFileName_x3f_3081_ = lean_ctor_get(v_opts_3042_, 4);
lean_inc(v_setupFileName_x3f_3081_);
v_oleanFileName_x3f_3082_ = lean_ctor_get(v_opts_3042_, 5);
lean_inc(v_oleanFileName_x3f_3082_);
v_ileanFileName_x3f_3083_ = lean_ctor_get(v_opts_3042_, 6);
lean_inc(v_ileanFileName_x3f_3083_);
v_cFileName_x3f_3084_ = lean_ctor_get(v_opts_3042_, 7);
lean_inc(v_cFileName_x3f_3084_);
v_bcFileName_x3f_3085_ = lean_ctor_get(v_opts_3042_, 8);
lean_inc(v_bcFileName_x3f_3085_);
v_jsonOutput_3086_ = lean_ctor_get_uint8(v_opts_3042_, sizeof(void*)*13 + 15);
v_errorOnKinds_3087_ = lean_ctor_get(v_opts_3042_, 9);
lean_inc_ref(v_errorOnKinds_3087_);
v_printStats_3088_ = lean_ctor_get_uint8(v_opts_3042_, sizeof(void*)*13 + 16);
v_run_3089_ = lean_ctor_get_uint8(v_opts_3042_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_3090_ = lean_ctor_get(v_opts_3042_, 10);
lean_inc(v_incrSaveFileName_x3f_3090_);
v_incrLoadFileName_x3f_3091_ = lean_ctor_get(v_opts_3042_, 11);
lean_inc(v_incrLoadFileName_x3f_3091_);
v_incrHeaderSaveFileName_x3f_3092_ = lean_ctor_get(v_opts_3042_, 12);
lean_inc(v_incrHeaderSaveFileName_x3f_3092_);
lean_dec_ref(v_opts_3042_);
v___f_3093_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__0));
v___x_3109_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__2, &l___private_Lean_Shell_0__Lean_shellMain___closed__2_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__2);
v___x_3110_ = l_Lean_Options_mergeBy(v___f_3093_, v_leanOpts_3072_, v___x_3109_);
v___x_3137_ = 1;
v___x_3480_ = l___private_Lean_Shell_0__Lean_maxMemory;
v_maxMemory_3481_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_3110_, v___x_3480_);
v___x_3482_ = lean_unsigned_to_nat(0u);
v___x_3483_ = lean_nat_dec_eq(v_maxMemory_3481_, v___x_3482_);
v___x_3484_ = lean_bool_not(v___x_3483_);
if (v___x_3484_ == 0)
{
lean_dec(v_maxMemory_3481_);
goto v___jp_3470_;
}
else
{
size_t v___x_3485_; size_t v___x_3486_; size_t v___x_3487_; size_t v___x_3488_; lean_object* v___x_3489_; 
v___x_3485_ = lean_usize_of_nat(v_maxMemory_3481_);
lean_dec(v_maxMemory_3481_);
v___x_3486_ = ((size_t)10ULL);
v___x_3487_ = lean_usize_shift_left(v___x_3485_, v___x_3486_);
v___x_3488_ = lean_usize_shift_left(v___x_3487_, v___x_3486_);
v___x_3489_ = lean_internal_set_max_memory(v___x_3488_);
goto v___jp_3470_;
}
v___jp_3094_:
{
lean_object* v___x_3096_; uint8_t v___x_3097_; 
v___x_3096_ = lean_display_cumulative_profiling_times();
v___x_3097_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__1, &l___private_Lean_Shell_0__Lean_shellMain___closed__1_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__1);
if (v___x_3097_ == 0)
{
if (lean_obj_tag(v___y_3095_) == 0)
{
if (v___x_3097_ == 0)
{
uint8_t v___x_3098_; lean_object* v___x_3099_; 
v___x_3098_ = 1;
v___x_3099_ = lean_io_exit(v___x_3098_);
return v___x_3099_;
}
else
{
goto v___jp_3047_;
}
}
else
{
lean_dec_ref_known(v___y_3095_, 1);
goto v___jp_3047_;
}
}
else
{
if (lean_obj_tag(v___y_3095_) == 0)
{
goto v___jp_3044_;
}
else
{
lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3107_; 
v_isSharedCheck_3107_ = !lean_is_exclusive(v___y_3095_);
if (v_isSharedCheck_3107_ == 0)
{
lean_object* v_unused_3108_; 
v_unused_3108_ = lean_ctor_get(v___y_3095_, 0);
lean_dec(v_unused_3108_);
v___x_3101_ = v___y_3095_;
v_isShared_3102_ = v_isSharedCheck_3107_;
goto v_resetjp_3100_;
}
else
{
lean_dec(v___y_3095_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3107_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
if (v___x_3097_ == 0)
{
lean_del_object(v___x_3101_);
goto v___jp_3044_;
}
else
{
lean_object* v___x_3103_; lean_object* v___x_3105_; 
v___x_3103_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3102_ == 0)
{
lean_ctor_set_tag(v___x_3101_, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3103_);
v___x_3105_ = v___x_3101_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v___x_3103_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
}
}
}
v___jp_3111_:
{
if (lean_obj_tag(v_bcFileName_x3f_3085_) == 1)
{
lean_object* v_val_3115_; lean_object* v___x_3116_; 
v_val_3115_ = lean_ctor_get(v_bcFileName_x3f_3085_, 0);
lean_inc(v_val_3115_);
lean_dec_ref_known(v_bcFileName_x3f_3085_, 1);
v___x_3116_ = lean_init_llvm();
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
lean_dec_ref_known(v___x_3116_, 1);
v___x_3117_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__3));
v___x_3118_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_emitLLVM___boxed), 4, 3);
lean_closure_set(v___x_3118_, 0, v___y_3112_);
lean_closure_set(v___x_3118_, 1, v___y_3113_);
lean_closure_set(v___x_3118_, 2, v_val_3115_);
v___x_3119_ = lean_box(0);
v___x_3120_ = l_Lean_profileitIOUnsafe___redArg(v___x_3117_, v___x_3110_, v___x_3118_, v___x_3119_);
lean_dec_ref(v___x_3110_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_dec_ref_known(v___x_3120_, 1);
v___y_3095_ = v___y_3114_;
goto v___jp_3094_;
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_dec(v___y_3114_);
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3120_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3120_);
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
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_dec(v_val_3115_);
lean_dec(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec_ref(v___x_3110_);
v_a_3129_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3116_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3116_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
else
{
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec_ref(v___x_3110_);
lean_dec(v_bcFileName_x3f_3085_);
v___y_3095_ = v___y_3114_;
goto v___jp_3094_;
}
}
v___jp_3138_:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3145_ = lean_unsigned_to_nat(0u);
v___x_3146_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__4));
lean_inc(v_mainModuleName_3144_);
lean_inc_ref(v___x_3110_);
v___x_3147_ = l_Lean_Elab_runFrontend(v___y_3141_, v___x_3110_, v___y_3143_, v_mainModuleName_3144_, v_trustLevel_3079_, v_oleanFileName_x3f_3082_, v_ileanFileName_x3f_3083_, v_jsonOutput_3086_, v_errorOnKinds_3087_, v___x_3146_, v_printStats_3088_, v___y_3140_, v_incrSaveFileName_x3f_3090_, v_incrLoadFileName_x3f_3091_, v_incrHeaderSaveFileName_x3f_3092_);
lean_dec_ref(v_errorOnKinds_3087_);
lean_dec(v_ileanFileName_x3f_3083_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3215_; 
v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3150_ = v___x_3147_;
v_isShared_3151_ = v_isSharedCheck_3215_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3147_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3215_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
if (lean_obj_tag(v_a_3148_) == 1)
{
if (v_run_3089_ == 0)
{
lean_del_object(v___x_3150_);
lean_dec(v___y_3142_);
if (lean_obj_tag(v_cFileName_x3f_3084_) == 1)
{
lean_object* v_val_3152_; lean_object* v_val_3153_; uint8_t v___x_3154_; lean_object* v___x_3155_; 
v_val_3152_ = lean_ctor_get(v_a_3148_, 0);
lean_inc(v_val_3152_);
v_val_3153_ = lean_ctor_get(v_cFileName_x3f_3084_, 0);
lean_inc(v_val_3153_);
lean_dec_ref_known(v_cFileName_x3f_3084_, 1);
v___x_3154_ = 1;
v___x_3155_ = lean_io_prim_handle_mk(v_val_3153_, v___x_3154_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_object* v_a_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___f_3176_; lean_object* v___x_3177_; 
lean_dec(v_val_3153_);
v_a_3156_ = lean_ctor_get(v___x_3155_, 0);
lean_inc(v_a_3156_);
lean_dec_ref_known(v___x_3155_, 1);
v___x_3157_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__5));
v___x_3158_ = l_Lean_instInhabitedFileMap_default;
v___x_3159_ = l_Lean_Options_empty;
v___x_3160_ = lean_box(0);
v___x_3161_ = lean_box(0);
v___x_3162_ = lean_box(0);
v___x_3163_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__6, &l___private_Lean_Shell_0__Lean_shellMain___closed__6_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__6);
v___x_3164_ = l_Lean_firstFrontendMacroScope;
v___x_3165_ = lean_box(0);
v___x_3166_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__7, &l___private_Lean_Shell_0__Lean_shellMain___closed__7_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__7);
v___x_3167_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__10));
v___x_3168_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__11));
v___x_3169_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__14, &l___private_Lean_Shell_0__Lean_shellMain___closed__14_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14);
v___x_3170_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__17, &l___private_Lean_Shell_0__Lean_shellMain___closed__17_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__17);
v___x_3171_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__18, &l___private_Lean_Shell_0__Lean_shellMain___closed__18_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__18);
v___x_3172_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__19, &l___private_Lean_Shell_0__Lean_shellMain___closed__19_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__19);
lean_inc(v_val_3152_);
v___x_3173_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3173_, 0, v_val_3152_);
lean_ctor_set(v___x_3173_, 1, v___x_3166_);
lean_ctor_set(v___x_3173_, 2, v___x_3167_);
lean_ctor_set(v___x_3173_, 3, v___x_3168_);
lean_ctor_set(v___x_3173_, 4, v___x_3169_);
lean_ctor_set(v___x_3173_, 5, v___x_3170_);
lean_ctor_set(v___x_3173_, 6, v___x_3171_);
lean_ctor_set(v___x_3173_, 7, v___x_3172_);
lean_ctor_set(v___x_3173_, 8, v___x_3146_);
v___x_3174_ = lean_box(v___x_3137_);
v___x_3175_ = lean_box(v_run_3089_);
lean_inc(v_mainModuleName_3144_);
v___f_3176_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed), 17, 16);
lean_closure_set(v___f_3176_, 0, v___x_3173_);
lean_closure_set(v___f_3176_, 1, v___x_3159_);
lean_closure_set(v___f_3176_, 2, v_mainModuleName_3144_);
lean_closure_set(v___f_3176_, 3, v_a_3156_);
lean_closure_set(v___f_3176_, 4, v___x_3174_);
lean_closure_set(v___f_3176_, 5, v___y_3139_);
lean_closure_set(v___f_3176_, 6, v___x_3158_);
lean_closure_set(v___f_3176_, 7, v___x_3145_);
lean_closure_set(v___f_3176_, 8, v___x_3160_);
lean_closure_set(v___f_3176_, 9, v___x_3161_);
lean_closure_set(v___f_3176_, 10, v___x_3162_);
lean_closure_set(v___f_3176_, 11, v___x_3163_);
lean_closure_set(v___f_3176_, 12, v___x_3164_);
lean_closure_set(v___f_3176_, 13, v___x_3165_);
lean_closure_set(v___f_3176_, 14, v___x_3175_);
lean_closure_set(v___f_3176_, 15, v___x_3170_);
v___x_3177_ = l_Lean_profileitIOUnsafe___redArg(v___x_3157_, v___x_3110_, v___f_3176_, v___x_3161_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_dec_ref_known(v___x_3177_, 1);
v___y_3112_ = v_val_3152_;
v___y_3113_ = v_mainModuleName_3144_;
v___y_3114_ = v_a_3148_;
goto v___jp_3111_;
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
lean_dec(v_val_3152_);
lean_dec_ref_known(v_a_3148_, 1);
lean_dec(v_mainModuleName_3144_);
lean_dec_ref(v___x_3110_);
lean_dec(v_bcFileName_x3f_3085_);
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3177_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3177_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3183_; 
if (v_isShared_3181_ == 0)
{
v___x_3183_ = v___x_3180_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
}
else
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
lean_dec_ref_known(v___x_3155_, 1);
lean_dec(v_val_3152_);
lean_dec_ref_known(v_a_3148_, 1);
lean_dec(v_mainModuleName_3144_);
lean_dec_ref(v___y_3139_);
lean_dec_ref(v___x_3110_);
lean_dec(v_bcFileName_x3f_3085_);
v___x_3186_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__20));
v___x_3187_ = lean_string_append(v___x_3186_, v_val_3153_);
lean_dec(v_val_3153_);
v___x_3188_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__1));
v___x_3189_ = lean_string_append(v___x_3187_, v___x_3188_);
v___x_3190_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3189_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3198_; 
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3198_ == 0)
{
lean_object* v_unused_3199_; 
v_unused_3199_ = lean_ctor_get(v___x_3190_, 0);
lean_dec(v_unused_3199_);
v___x_3192_ = v___x_3190_;
v_isShared_3193_ = v_isSharedCheck_3198_;
goto v_resetjp_3191_;
}
else
{
lean_dec(v___x_3190_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3198_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3194_; lean_object* v___x_3196_; 
v___x_3194_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 0, v___x_3194_);
v___x_3196_ = v___x_3192_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___x_3194_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
v_a_3200_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3190_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3190_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
}
else
{
lean_object* v_val_3208_; 
lean_dec_ref(v___y_3139_);
lean_dec(v_cFileName_x3f_3084_);
v_val_3208_ = lean_ctor_get(v_a_3148_, 0);
lean_inc(v_val_3208_);
v___y_3112_ = v_val_3208_;
v___y_3113_ = v_mainModuleName_3144_;
v___y_3114_ = v_a_3148_;
goto v___jp_3111_;
}
}
else
{
lean_object* v_val_3209_; uint32_t v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3213_; 
lean_dec(v_mainModuleName_3144_);
lean_dec_ref(v___y_3139_);
lean_dec(v_bcFileName_x3f_3085_);
lean_dec(v_cFileName_x3f_3084_);
v_val_3209_ = lean_ctor_get(v_a_3148_, 0);
lean_inc(v_val_3209_);
lean_dec_ref_known(v_a_3148_, 1);
v___x_3210_ = lean_eval_main(v_val_3209_, v___x_3110_, v___y_3142_);
lean_dec(v___y_3142_);
lean_dec_ref(v___x_3110_);
lean_dec(v_val_3209_);
v___x_3211_ = lean_box_uint32(v___x_3210_);
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 0, v___x_3211_);
v___x_3213_ = v___x_3150_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3211_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
else
{
lean_del_object(v___x_3150_);
lean_dec(v_mainModuleName_3144_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3139_);
lean_dec_ref(v___x_3110_);
lean_dec(v_bcFileName_x3f_3085_);
lean_dec(v_cFileName_x3f_3084_);
v___y_3095_ = v_a_3148_;
goto v___jp_3094_;
}
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_dec(v_mainModuleName_3144_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3139_);
lean_dec_ref(v___x_3110_);
lean_dec(v_bcFileName_x3f_3085_);
lean_dec(v_cFileName_x3f_3084_);
v_a_3216_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3147_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3147_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
v___jp_3224_:
{
if (lean_obj_tag(v___y_3230_) == 0)
{
lean_object* v_a_3231_; 
v_a_3231_ = lean_ctor_get(v___y_3230_, 0);
lean_inc(v_a_3231_);
lean_dec_ref_known(v___y_3230_, 1);
v___y_3139_ = v___y_3225_;
v___y_3140_ = v___y_3226_;
v___y_3141_ = v___y_3227_;
v___y_3142_ = v___y_3228_;
v___y_3143_ = v___y_3229_;
v_mainModuleName_3144_ = v_a_3231_;
goto v___jp_3138_;
}
else
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3239_; 
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec_ref(v___x_3110_);
lean_dec(v_incrHeaderSaveFileName_x3f_3092_);
lean_dec(v_incrLoadFileName_x3f_3091_);
lean_dec(v_incrSaveFileName_x3f_3090_);
lean_dec_ref(v_errorOnKinds_3087_);
lean_dec(v_bcFileName_x3f_3085_);
lean_dec(v_cFileName_x3f_3084_);
lean_dec(v_ileanFileName_x3f_3083_);
lean_dec(v_oleanFileName_x3f_3082_);
v_a_3232_ = lean_ctor_get(v___y_3230_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___y_3230_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3234_ = v___y_3230_;
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___y_3230_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
v___jp_3240_:
{
if (lean_obj_tag(v_setupFileName_x3f_3081_) == 0)
{
lean_object* v___x_3246_; 
v___x_3246_ = lean_box(0);
if (lean_obj_tag(v___y_3244_) == 1)
{
lean_object* v_val_3247_; lean_object* v___x_3248_; 
v_val_3247_ = lean_ctor_get(v___y_3244_, 0);
lean_inc(v_val_3247_);
lean_dec_ref_known(v___y_3244_, 1);
v___x_3248_ = l_Lean_moduleNameOfFileName(v_val_3247_, v_rootDir_x3f_3080_);
if (lean_obj_tag(v___x_3248_) == 0)
{
v___y_3225_ = v___y_3241_;
v___y_3226_ = v___x_3246_;
v___y_3227_ = v_contents_3245_;
v___y_3228_ = v___y_3242_;
v___y_3229_ = v___y_3243_;
v___y_3230_ = v___x_3248_;
goto v___jp_3224_;
}
else
{
if (lean_obj_tag(v_oleanFileName_x3f_3082_) == 0)
{
if (lean_obj_tag(v_cFileName_x3f_3084_) == 0)
{
lean_object* v___x_3249_; 
lean_dec_ref_known(v___x_3248_, 1);
v___x_3249_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__22));
v___y_3139_ = v___y_3241_;
v___y_3140_ = v___x_3246_;
v___y_3141_ = v_contents_3245_;
v___y_3142_ = v___y_3242_;
v___y_3143_ = v___y_3243_;
v_mainModuleName_3144_ = v___x_3249_;
goto v___jp_3138_;
}
else
{
v___y_3225_ = v___y_3241_;
v___y_3226_ = v___x_3246_;
v___y_3227_ = v_contents_3245_;
v___y_3228_ = v___y_3242_;
v___y_3229_ = v___y_3243_;
v___y_3230_ = v___x_3248_;
goto v___jp_3224_;
}
}
else
{
v___y_3225_ = v___y_3241_;
v___y_3226_ = v___x_3246_;
v___y_3227_ = v_contents_3245_;
v___y_3228_ = v___y_3242_;
v___y_3229_ = v___y_3243_;
v___y_3230_ = v___x_3248_;
goto v___jp_3224_;
}
}
}
else
{
lean_object* v___x_3250_; 
lean_dec(v___y_3244_);
lean_dec(v_rootDir_x3f_3080_);
v___x_3250_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__22));
v___y_3139_ = v___y_3241_;
v___y_3140_ = v___x_3246_;
v___y_3141_ = v_contents_3245_;
v___y_3142_ = v___y_3242_;
v___y_3143_ = v___y_3243_;
v_mainModuleName_3144_ = v___x_3250_;
goto v___jp_3138_;
}
}
else
{
lean_object* v_val_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3269_; 
lean_dec(v___y_3244_);
lean_dec(v_rootDir_x3f_3080_);
v_val_3251_ = lean_ctor_get(v_setupFileName_x3f_3081_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v_setupFileName_x3f_3081_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3253_ = v_setupFileName_x3f_3081_;
v_isShared_3254_ = v_isSharedCheck_3269_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_val_3251_);
lean_dec(v_setupFileName_x3f_3081_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3269_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3255_; 
v___x_3255_ = l_Lean_ModuleSetup_load(v_val_3251_);
lean_dec(v_val_3251_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v_a_3256_; lean_object* v_name_3257_; lean_object* v___x_3259_; 
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
lean_inc(v_a_3256_);
lean_dec_ref_known(v___x_3255_, 1);
v_name_3257_ = lean_ctor_get(v_a_3256_, 0);
lean_inc(v_name_3257_);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 0, v_a_3256_);
v___x_3259_ = v___x_3253_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3256_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
v___y_3139_ = v___y_3241_;
v___y_3140_ = v___x_3259_;
v___y_3141_ = v_contents_3245_;
v___y_3142_ = v___y_3242_;
v___y_3143_ = v___y_3243_;
v_mainModuleName_3144_ = v_name_3257_;
goto v___jp_3138_;
}
}
else
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
lean_del_object(v___x_3253_);
lean_dec_ref(v_contents_3245_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec_ref(v___x_3110_);
lean_dec(v_incrHeaderSaveFileName_x3f_3092_);
lean_dec(v_incrLoadFileName_x3f_3091_);
lean_dec(v_incrSaveFileName_x3f_3090_);
lean_dec_ref(v_errorOnKinds_3087_);
lean_dec(v_bcFileName_x3f_3085_);
lean_dec(v_cFileName_x3f_3084_);
lean_dec(v_ileanFileName_x3f_3083_);
lean_dec(v_oleanFileName_x3f_3082_);
v_a_3261_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3263_ = v___x_3255_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3255_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3266_; 
if (v_isShared_3264_ == 0)
{
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3261_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
}
}
}
v___jp_3270_:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; uint8_t v___x_3283_; 
v___x_3279_ = lean_nat_add(v_startInclusive_3276_, v___y_3278_);
lean_dec(v___y_3278_);
lean_inc(v___x_3279_);
lean_inc_ref(v_str_3275_);
v___x_3280_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3280_, 0, v_str_3275_);
lean_ctor_set(v___x_3280_, 1, v_startInclusive_3276_);
lean_ctor_set(v___x_3280_, 2, v___x_3279_);
v___x_3281_ = l_String_Slice_trimAscii(v___x_3280_);
v___x_3282_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__25, &l___private_Lean_Shell_0__Lean_shellMain___closed__25_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__25);
v___x_3283_ = l_String_Slice_beq(v___x_3281_, v___x_3282_);
if (v___x_3283_ == 0)
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
lean_dec(v___x_3279_);
lean_dec(v_endExclusive_3277_);
lean_dec_ref(v_str_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec_ref(v___x_3110_);
lean_dec(v_incrHeaderSaveFileName_x3f_3092_);
lean_dec(v_incrLoadFileName_x3f_3091_);
lean_dec(v_incrSaveFileName_x3f_3090_);
lean_dec_ref(v_errorOnKinds_3087_);
lean_dec(v_bcFileName_x3f_3085_);
lean_dec(v_cFileName_x3f_3084_);
lean_dec(v_ileanFileName_x3f_3083_);
lean_dec(v_oleanFileName_x3f_3082_);
lean_dec(v_setupFileName_x3f_3081_);
lean_dec(v_rootDir_x3f_3080_);
v___x_3284_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__26));
v___x_3285_ = l_String_Slice_toString(v___x_3281_);
lean_dec_ref(v___x_3281_);
v___x_3286_ = lean_string_append(v___x_3284_, v___x_3285_);
lean_dec_ref(v___x_3285_);
v___x_3287_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
v___x_3288_ = lean_string_append(v___x_3286_, v___x_3287_);
v___x_3289_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3288_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3297_; 
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3297_ == 0)
{
lean_object* v_unused_3298_; 
v_unused_3298_ = lean_ctor_get(v___x_3289_, 0);
lean_dec(v_unused_3298_);
v___x_3291_ = v___x_3289_;
v_isShared_3292_ = v_isSharedCheck_3297_;
goto v_resetjp_3290_;
}
else
{
lean_dec(v___x_3289_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3297_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v___x_3295_; 
v___x_3293_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 0, v___x_3293_);
v___x_3295_ = v___x_3291_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3293_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
else
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3306_; 
v_a_3299_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3301_ = v___x_3289_;
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3289_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3304_; 
if (v_isShared_3302_ == 0)
{
v___x_3304_ = v___x_3301_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_a_3299_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
}
else
{
lean_object* v___x_3307_; 
lean_dec_ref(v___x_3281_);
v___x_3307_ = lean_string_utf8_extract(v_str_3275_, v___x_3279_, v_endExclusive_3277_);
lean_dec(v_endExclusive_3277_);
lean_dec(v___x_3279_);
lean_dec_ref(v_str_3275_);
v___y_3241_ = v___y_3271_;
v___y_3242_ = v___y_3272_;
v___y_3243_ = v___y_3273_;
v___y_3244_ = v___y_3274_;
v_contents_3245_ = v___x_3307_;
goto v___jp_3240_;
}
}
v___jp_3308_:
{
if (lean_obj_tag(v___y_3312_) == 0)
{
lean_object* v_a_3313_; lean_object* v___x_3314_; 
v_a_3313_ = lean_ctor_get(v___y_3312_, 0);
lean_inc(v_a_3313_);
lean_dec_ref_known(v___y_3312_, 1);
v___x_3314_ = lean_decode_lossy_utf8(v_a_3313_);
lean_dec(v_a_3313_);
if (v_onlyDeps_3076_ == 0)
{
if (v_onlySrcDeps_3077_ == 0)
{
lean_object* v___x_3315_; 
lean_inc_ref(v___x_3314_);
v___x_3315_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v___x_3314_);
if (lean_obj_tag(v___x_3315_) == 1)
{
lean_object* v_val_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
lean_dec_ref(v___x_3314_);
v_val_3316_ = lean_ctor_get(v___x_3315_, 0);
lean_inc(v_val_3316_);
lean_dec_ref_known(v___x_3315_, 1);
v___x_3317_ = lean_unsigned_to_nat(0u);
v___x_3318_ = lean_box(0);
v___x_3319_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3316_, v___x_3317_, v___x_3318_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_str_3320_; lean_object* v_startInclusive_3321_; lean_object* v_endExclusive_3322_; lean_object* v___x_3323_; 
v_str_3320_ = lean_ctor_get(v_val_3316_, 0);
lean_inc_ref(v_str_3320_);
v_startInclusive_3321_ = lean_ctor_get(v_val_3316_, 1);
lean_inc(v_startInclusive_3321_);
v_endExclusive_3322_ = lean_ctor_get(v_val_3316_, 2);
lean_inc(v_endExclusive_3322_);
lean_dec(v_val_3316_);
v___x_3323_ = lean_nat_sub(v_endExclusive_3322_, v_startInclusive_3321_);
lean_inc_ref(v___y_3310_);
v___y_3271_ = v___y_3310_;
v___y_3272_ = v___y_3311_;
v___y_3273_ = v___y_3310_;
v___y_3274_ = v___y_3309_;
v_str_3275_ = v_str_3320_;
v_startInclusive_3276_ = v_startInclusive_3321_;
v_endExclusive_3277_ = v_endExclusive_3322_;
v___y_3278_ = v___x_3323_;
goto v___jp_3270_;
}
else
{
lean_object* v_val_3324_; lean_object* v_str_3325_; lean_object* v_startInclusive_3326_; lean_object* v_endExclusive_3327_; 
v_val_3324_ = lean_ctor_get(v___x_3319_, 0);
lean_inc(v_val_3324_);
lean_dec_ref_known(v___x_3319_, 1);
v_str_3325_ = lean_ctor_get(v_val_3316_, 0);
lean_inc_ref(v_str_3325_);
v_startInclusive_3326_ = lean_ctor_get(v_val_3316_, 1);
lean_inc(v_startInclusive_3326_);
v_endExclusive_3327_ = lean_ctor_get(v_val_3316_, 2);
lean_inc(v_endExclusive_3327_);
lean_dec(v_val_3316_);
lean_inc_ref(v___y_3310_);
v___y_3271_ = v___y_3310_;
v___y_3272_ = v___y_3311_;
v___y_3273_ = v___y_3310_;
v___y_3274_ = v___y_3309_;
v_str_3275_ = v_str_3325_;
v_startInclusive_3276_ = v_startInclusive_3326_;
v_endExclusive_3277_ = v_endExclusive_3327_;
v___y_3278_ = v_val_3324_;
goto v___jp_3270_;
}
}
else
{
lean_dec(v___x_3315_);
lean_inc_ref(v___y_3310_);
v___y_3241_ = v___y_3310_;
v___y_3242_ = v___y_3311_;
v___y_3243_ = v___y_3310_;
v___y_3244_ = v___y_3309_;
v_contents_3245_ = v___x_3314_;
goto v___jp_3240_;
}
}
else
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
lean_dec(v___y_3311_);
lean_dec(v___y_3309_);
lean_dec_ref(v___x_3110_);
lean_dec(v_incrHeaderSaveFileName_x3f_3092_);
lean_dec(v_incrLoadFileName_x3f_3091_);
lean_dec(v_incrSaveFileName_x3f_3090_);
lean_dec_ref(v_errorOnKinds_3087_);
lean_dec(v_bcFileName_x3f_3085_);
lean_dec(v_cFileName_x3f_3084_);
lean_dec(v_ileanFileName_x3f_3083_);
lean_dec(v_oleanFileName_x3f_3082_);
lean_dec(v_setupFileName_x3f_3081_);
lean_dec(v_rootDir_x3f_3080_);
v___x_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3328_, 0, v___y_3310_);
v___x_3329_ = l_Lean_Elab_printImportSrcs(v___x_3314_, v___x_3328_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3337_; 
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3337_ == 0)
{
lean_object* v_unused_3338_; 
v_unused_3338_ = lean_ctor_get(v___x_3329_, 0);
lean_dec(v_unused_3338_);
v___x_3331_ = v___x_3329_;
v_isShared_3332_ = v_isSharedCheck_3337_;
goto v_resetjp_3330_;
}
else
{
lean_dec(v___x_3329_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3337_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3333_; lean_object* v___x_3335_; 
v___x_3333_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 0, v___x_3333_);
v___x_3335_ = v___x_3331_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3333_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
else
{
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3346_; 
v_a_3339_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3341_ = v___x_3329_;
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3329_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3344_; 
if (v_isShared_3342_ == 0)
{
v___x_3344_ = v___x_3341_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3339_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
}
else
{
lean_object* v___x_3347_; lean_object* v___x_3348_; 
lean_dec(v___y_3311_);
lean_dec(v___y_3309_);
lean_dec_ref(v___x_3110_);
lean_dec(v_incrHeaderSaveFileName_x3f_3092_);
lean_dec(v_incrLoadFileName_x3f_3091_);
lean_dec(v_incrSaveFileName_x3f_3090_);
lean_dec_ref(v_errorOnKinds_3087_);
lean_dec(v_bcFileName_x3f_3085_);
lean_dec(v_cFileName_x3f_3084_);
lean_dec(v_ileanFileName_x3f_3083_);
lean_dec(v_oleanFileName_x3f_3082_);
lean_dec(v_setupFileName_x3f_3081_);
lean_dec(v_rootDir_x3f_3080_);
v___x_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3347_, 0, v___y_3310_);
v___x_3348_ = l_Lean_Elab_printImports(v___x_3314_, v___x_3347_);
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
v___x_3352_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
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
}
else
{
lean_object* v_a_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3373_; 
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec_ref(v___x_3110_);
lean_dec(v_incrHeaderSaveFileName_x3f_3092_);
lean_dec(v_incrLoadFileName_x3f_3091_);
lean_dec(v_incrSaveFileName_x3f_3090_);
lean_dec_ref(v_errorOnKinds_3087_);
lean_dec(v_bcFileName_x3f_3085_);
lean_dec(v_cFileName_x3f_3084_);
lean_dec(v_ileanFileName_x3f_3083_);
lean_dec(v_oleanFileName_x3f_3082_);
lean_dec(v_setupFileName_x3f_3081_);
lean_dec(v_rootDir_x3f_3080_);
v_a_3366_ = lean_ctor_get(v___y_3312_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___y_3312_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3368_ = v___y_3312_;
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___y_3312_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3371_; 
if (v_isShared_3369_ == 0)
{
v___x_3371_ = v___x_3368_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_a_3366_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
v___jp_3374_:
{
if (v_useStdin_3075_ == 0)
{
lean_object* v___x_3378_; 
v___x_3378_ = l_IO_FS_readBinFile(v_fileName_3377_);
v___y_3309_ = v___y_3376_;
v___y_3310_ = v_fileName_3377_;
v___y_3311_ = v___y_3375_;
v___y_3312_ = v___x_3378_;
goto v___jp_3308_;
}
else
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3379_ = lean_get_stdin();
v___x_3380_ = l_IO_FS_Stream_readBinToEnd(v___x_3379_);
v___y_3309_ = v___y_3376_;
v___y_3310_ = v_fileName_3377_;
v___y_3311_ = v___y_3375_;
v___y_3312_ = v___x_3380_;
goto v___jp_3308_;
}
}
v___jp_3381_:
{
if (v___y_3384_ == 0)
{
if (lean_obj_tag(v___y_3383_) == 1)
{
lean_object* v_val_3385_; 
v_val_3385_ = lean_ctor_get(v___y_3383_, 0);
lean_inc(v_val_3385_);
v___y_3375_ = v___y_3382_;
v___y_3376_ = v___y_3383_;
v_fileName_3377_ = v_val_3385_;
goto v___jp_3374_;
}
else
{
if (v_useStdin_3075_ == 0)
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
lean_dec(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec_ref(v___x_3110_);
lean_dec(v_incrHeaderSaveFileName_x3f_3092_);
lean_dec(v_incrLoadFileName_x3f_3091_);
lean_dec(v_incrSaveFileName_x3f_3090_);
lean_dec_ref(v_errorOnKinds_3087_);
lean_dec(v_bcFileName_x3f_3085_);
lean_dec(v_cFileName_x3f_3084_);
lean_dec(v_ileanFileName_x3f_3083_);
lean_dec(v_oleanFileName_x3f_3082_);
lean_dec(v_setupFileName_x3f_3081_);
lean_dec(v_rootDir_x3f_3080_);
v___x_3386_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__27));
v___x_3387_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3386_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v___x_3388_; 
lean_dec_ref_known(v___x_3387_, 1);
v___x_3388_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_3137_);
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
v___x_3392_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
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
else
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
v_a_3406_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___x_3387_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3387_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3409_ == 0)
{
v___x_3411_ = v___x_3408_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3406_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
}
else
{
lean_object* v___x_3414_; 
v___x_3414_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__28));
v___y_3375_ = v___y_3382_;
v___y_3376_ = v___y_3383_;
v_fileName_3377_ = v___x_3414_;
goto v___jp_3374_;
}
}
}
else
{
lean_object* v___x_3415_; lean_object* v___x_3416_; 
lean_dec(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec_ref(v___x_3110_);
lean_dec(v_incrHeaderSaveFileName_x3f_3092_);
lean_dec(v_incrLoadFileName_x3f_3091_);
lean_dec(v_incrSaveFileName_x3f_3090_);
lean_dec_ref(v_errorOnKinds_3087_);
lean_dec(v_bcFileName_x3f_3085_);
lean_dec(v_cFileName_x3f_3084_);
lean_dec(v_ileanFileName_x3f_3083_);
lean_dec(v_oleanFileName_x3f_3082_);
lean_dec(v_setupFileName_x3f_3081_);
lean_dec(v_rootDir_x3f_3080_);
v___x_3415_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__27));
v___x_3416_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3415_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v___x_3417_; 
lean_dec_ref_known(v___x_3416_, 1);
v___x_3417_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_3137_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3425_; 
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3425_ == 0)
{
lean_object* v_unused_3426_; 
v_unused_3426_ = lean_ctor_get(v___x_3417_, 0);
lean_dec(v_unused_3426_);
v___x_3419_ = v___x_3417_;
v_isShared_3420_ = v_isSharedCheck_3425_;
goto v_resetjp_3418_;
}
else
{
lean_dec(v___x_3417_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3425_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3421_; lean_object* v___x_3423_; 
v___x_3421_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v___x_3421_);
v___x_3423_ = v___x_3419_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3421_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
else
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
v_a_3427_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3417_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3417_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
else
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
v_a_3435_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3437_ = v___x_3416_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3416_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
}
}
v___jp_3443_:
{
uint8_t v___x_3446_; 
v___x_3446_ = lean_bool_not(v_run_3089_);
if (v___x_3446_ == 0)
{
v___y_3382_ = v_snd_3445_;
v___y_3383_ = v_fst_3444_;
v___y_3384_ = v___x_3446_;
goto v___jp_3381_;
}
else
{
uint8_t v___x_3447_; uint8_t v___x_3448_; 
v___x_3447_ = l_List_isEmpty___redArg(v_snd_3445_);
v___x_3448_ = lean_bool_not(v___x_3447_);
v___y_3382_ = v_snd_3445_;
v___y_3383_ = v_fst_3444_;
v___y_3384_ = v___x_3448_;
goto v___jp_3381_;
}
}
v___jp_3449_:
{
if (lean_obj_tag(v_args_3041_) == 0)
{
lean_object* v___x_3450_; 
v___x_3450_ = lean_box(0);
v_fst_3444_ = v___x_3450_;
v_snd_3445_ = v_args_3041_;
goto v___jp_3443_;
}
else
{
lean_object* v_head_3451_; lean_object* v_tail_3452_; lean_object* v___x_3453_; 
v_head_3451_ = lean_ctor_get(v_args_3041_, 0);
lean_inc(v_head_3451_);
v_tail_3452_ = lean_ctor_get(v_args_3041_, 1);
lean_inc(v_tail_3452_);
lean_dec_ref_known(v_args_3041_, 2);
v___x_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3453_, 0, v_head_3451_);
v_fst_3444_ = v___x_3453_;
v_snd_3445_ = v_tail_3452_;
goto v___jp_3443_;
}
}
v___jp_3454_:
{
switch(v_component_3074_)
{
case 0:
{
lean_dec_ref(v_forwardedArgs_3073_);
if (v_onlyDeps_3076_ == 0)
{
goto v___jp_3449_;
}
else
{
if (v_depsJson_3078_ == 0)
{
goto v___jp_3449_;
}
else
{
lean_dec_ref(v___x_3110_);
lean_dec(v_incrHeaderSaveFileName_x3f_3092_);
lean_dec(v_incrLoadFileName_x3f_3091_);
lean_dec(v_incrSaveFileName_x3f_3090_);
lean_dec_ref(v_errorOnKinds_3087_);
lean_dec(v_bcFileName_x3f_3085_);
lean_dec(v_cFileName_x3f_3084_);
lean_dec(v_ileanFileName_x3f_3083_);
lean_dec(v_oleanFileName_x3f_3082_);
lean_dec(v_setupFileName_x3f_3081_);
lean_dec(v_rootDir_x3f_3080_);
if (v_useStdin_3075_ == 0)
{
lean_object* v___x_3455_; 
v___x_3455_ = lean_array_mk(v_args_3041_);
v_fns_3051_ = v___x_3455_;
goto v___jp_3050_;
}
else
{
lean_object* v___x_3456_; lean_object* v___x_3457_; 
lean_dec(v_args_3041_);
v___x_3456_ = lean_get_stdin();
v___x_3457_ = l_IO_FS_Stream_lines(v___x_3456_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_a_3458_);
lean_dec_ref_known(v___x_3457_, 1);
v_fns_3051_ = v_a_3458_;
goto v___jp_3050_;
}
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
v_a_3459_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3457_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3457_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; 
lean_dec_ref(v___x_3110_);
lean_dec(v_incrHeaderSaveFileName_x3f_3092_);
lean_dec(v_incrLoadFileName_x3f_3091_);
lean_dec(v_incrSaveFileName_x3f_3090_);
lean_dec_ref(v_errorOnKinds_3087_);
lean_dec(v_bcFileName_x3f_3085_);
lean_dec(v_cFileName_x3f_3084_);
lean_dec(v_ileanFileName_x3f_3083_);
lean_dec(v_oleanFileName_x3f_3082_);
lean_dec(v_setupFileName_x3f_3081_);
lean_dec(v_rootDir_x3f_3080_);
lean_dec(v_args_3041_);
v___x_3467_ = lean_array_to_list(v_forwardedArgs_3073_);
v___x_3468_ = l_Lean_Server_Watchdog_watchdogMain(v___x_3467_);
return v___x_3468_;
}
default: 
{
lean_object* v___x_3469_; 
lean_dec(v_incrHeaderSaveFileName_x3f_3092_);
lean_dec(v_incrLoadFileName_x3f_3091_);
lean_dec(v_incrSaveFileName_x3f_3090_);
lean_dec_ref(v_errorOnKinds_3087_);
lean_dec(v_bcFileName_x3f_3085_);
lean_dec(v_cFileName_x3f_3084_);
lean_dec(v_ileanFileName_x3f_3083_);
lean_dec(v_oleanFileName_x3f_3082_);
lean_dec(v_setupFileName_x3f_3081_);
lean_dec(v_rootDir_x3f_3080_);
lean_dec_ref(v_forwardedArgs_3073_);
lean_dec(v_args_3041_);
v___x_3469_ = l_Lean_Server_FileWorker_workerMain(v___x_3110_);
return v___x_3469_;
}
}
}
v___jp_3470_:
{
lean_object* v___x_3471_; lean_object* v_timeout_3472_; lean_object* v___x_3473_; uint8_t v___x_3474_; uint8_t v___x_3475_; 
v___x_3471_ = l___private_Lean_Shell_0__Lean_timeout;
v_timeout_3472_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_3110_, v___x_3471_);
v___x_3473_ = lean_unsigned_to_nat(0u);
v___x_3474_ = lean_nat_dec_eq(v_timeout_3472_, v___x_3473_);
v___x_3475_ = lean_bool_not(v___x_3474_);
if (v___x_3475_ == 0)
{
lean_dec(v_timeout_3472_);
goto v___jp_3454_;
}
else
{
size_t v___x_3476_; size_t v___x_3477_; size_t v___x_3478_; lean_object* v___x_3479_; 
v___x_3476_ = lean_usize_of_nat(v_timeout_3472_);
lean_dec(v_timeout_3472_);
v___x_3477_ = ((size_t)1000ULL);
v___x_3478_ = lean_usize_mul(v___x_3476_, v___x_3477_);
v___x_3479_ = lean_internal_set_max_heartbeat(v___x_3478_);
goto v___jp_3454_;
}
}
}
else
{
lean_object* v___x_3490_; 
lean_dec_ref(v_opts_3042_);
lean_dec(v_args_3041_);
v___x_3490_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v_a_3491_; lean_object* v___x_3492_; 
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
lean_inc(v_a_3491_);
lean_dec_ref_known(v___x_3490_, 1);
v___x_3492_ = l_Lean_getLibDir(v_a_3491_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v___x_3494_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_a_3493_);
lean_dec_ref_known(v___x_3492_, 1);
v___x_3494_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3493_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3502_; 
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3502_ == 0)
{
lean_object* v_unused_3503_; 
v_unused_3503_ = lean_ctor_get(v___x_3494_, 0);
lean_dec(v_unused_3503_);
v___x_3496_ = v___x_3494_;
v_isShared_3497_ = v_isSharedCheck_3502_;
goto v_resetjp_3495_;
}
else
{
lean_dec(v___x_3494_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3502_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3498_; lean_object* v___x_3500_; 
v___x_3498_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 0, v___x_3498_);
v___x_3500_ = v___x_3496_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3498_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
v_a_3504_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_3494_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3494_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3509_; 
if (v_isShared_3507_ == 0)
{
v___x_3509_ = v___x_3506_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
else
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
v_a_3512_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3492_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3492_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3517_; 
if (v_isShared_3515_ == 0)
{
v___x_3517_ = v___x_3514_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3512_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
v_a_3520_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3490_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3490_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
}
else
{
lean_object* v___x_3528_; 
lean_dec_ref(v_opts_3042_);
lean_dec(v_args_3041_);
v___x_3528_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; lean_object* v___x_3530_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3529_);
lean_dec_ref_known(v___x_3528_, 1);
v___x_3530_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3529_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3538_; 
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3538_ == 0)
{
lean_object* v_unused_3539_; 
v_unused_3539_ = lean_ctor_get(v___x_3530_, 0);
lean_dec(v_unused_3539_);
v___x_3532_ = v___x_3530_;
v_isShared_3533_ = v_isSharedCheck_3538_;
goto v_resetjp_3531_;
}
else
{
lean_dec(v___x_3530_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3538_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3534_; lean_object* v___x_3536_; 
v___x_3534_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3533_ == 0)
{
lean_ctor_set(v___x_3532_, 0, v___x_3534_);
v___x_3536_ = v___x_3532_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3534_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
v_a_3540_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3530_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3530_);
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
v_a_3548_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3528_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3528_);
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
v___jp_3044_:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3045_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3045_);
return v___x_3046_;
}
v___jp_3047_:
{
uint8_t v___x_3048_; lean_object* v___x_3049_; 
v___x_3048_ = 0;
v___x_3049_ = lean_io_exit(v___x_3048_);
return v___x_3049_;
}
v___jp_3050_:
{
lean_object* v___x_3052_; 
v___x_3052_ = l_Lean_printImportsJson(v_fns_3051_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3060_; 
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3060_ == 0)
{
lean_object* v_unused_3061_; 
v_unused_3061_ = lean_ctor_get(v___x_3052_, 0);
lean_dec(v_unused_3061_);
v___x_3054_ = v___x_3052_;
v_isShared_3055_ = v_isSharedCheck_3060_;
goto v_resetjp_3053_;
}
else
{
lean_dec(v___x_3052_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3060_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3056_; lean_object* v___x_3058_; 
v___x_3056_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 0, v___x_3056_);
v___x_3058_ = v___x_3054_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v___x_3056_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
else
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
v_a_3062_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3064_ = v___x_3052_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3052_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3067_; 
if (v_isShared_3065_ == 0)
{
v___x_3067_ = v___x_3064_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_a_3062_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object* v_args_3556_, lean_object* v_opts_3557_, lean_object* v_a_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = lean_shell_main(v_args_3556_, v_opts_3557_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(lean_object* v_val_3560_, lean_object* v_inst_3561_, lean_object* v_R_3562_, lean_object* v_a_3563_, lean_object* v_b_3564_, lean_object* v_c_3565_){
_start:
{
lean_object* v___x_3566_; 
v___x_3566_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3560_, v_a_3563_, v_b_3564_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___boxed(lean_object* v_val_3567_, lean_object* v_inst_3568_, lean_object* v_R_3569_, lean_object* v_a_3570_, lean_object* v_b_3571_, lean_object* v_c_3572_){
_start:
{
lean_object* v_res_3573_; 
v_res_3573_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(v_val_3567_, v_inst_3568_, v_R_3569_, v_a_3570_, v_b_3571_, v_c_3572_);
lean_dec(v_b_3571_);
lean_dec_ref(v_val_3567_);
return v_res_3573_;
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
