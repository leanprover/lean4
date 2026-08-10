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
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* v_startInclusive_609_; lean_object* v_endExclusive_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v_startInclusive_609_ = lean_ctor_get(v___x_605_, 1);
v_endExclusive_610_ = lean_ctor_get(v___x_605_, 2);
v___x_611_ = lean_nat_sub(v_endExclusive_610_, v_startInclusive_609_);
v___x_612_ = lean_nat_dec_eq(v_a_607_, v___x_611_);
lean_dec(v___x_611_);
if (v___x_612_ == 0)
{
uint32_t v___x_613_; uint32_t v___x_614_; uint8_t v___x_615_; 
v___x_613_ = lean_string_utf8_get_fast(v_arg_606_, v_a_607_);
v___x_614_ = 61;
v___x_615_ = lean_uint32_dec_eq(v___x_613_, v___x_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_box(0);
v___x_617_ = lean_string_utf8_next_fast(v_arg_606_, v_a_607_);
lean_dec(v_a_607_);
v_a_607_ = v___x_617_;
v_b_608_ = v___x_616_;
goto _start;
}
else
{
lean_object* v___x_619_; 
v___x_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_619_, 0, v_a_607_);
return v___x_619_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg___boxed(lean_object* v___x_620_, lean_object* v_arg_621_, lean_object* v_a_622_, lean_object* v_b_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_620_, v_arg_621_, v_a_622_, v_b_623_);
lean_dec(v_b_623_);
lean_dec_ref(v_arg_621_);
lean_dec_ref(v___x_620_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_setConfigOption(lean_object* v_opts_628_, lean_object* v_arg_629_){
_start:
{
lean_object* v___y_632_; lean_object* v_searcher_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_searcher_663_ = lean_unsigned_to_nat(0u);
v___x_664_ = lean_string_utf8_byte_size(v_arg_629_);
lean_inc_ref(v_arg_629_);
v___x_665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_665_, 0, v_arg_629_);
lean_ctor_set(v___x_665_, 1, v_searcher_663_);
lean_ctor_set(v___x_665_, 2, v___x_664_);
v___x_666_ = lean_box(0);
v___x_667_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_665_, v_arg_629_, v_searcher_663_, v___x_666_);
lean_dec_ref_known(v___x_665_, 3);
if (lean_obj_tag(v___x_667_) == 0)
{
v___y_632_ = v___x_664_;
goto v___jp_631_;
}
else
{
lean_object* v_val_668_; 
v_val_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_val_668_);
lean_dec_ref_known(v___x_667_, 1);
v___y_632_ = v_val_668_;
goto v___jp_631_;
}
v___jp_631_:
{
lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_633_ = lean_string_utf8_byte_size(v_arg_629_);
v___x_634_ = lean_nat_dec_eq(v___y_632_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_652_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_652_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_652_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_652_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v_name_643_; lean_object* v_val_644_; lean_object* v___x_645_; 
v___x_640_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_632_);
lean_inc_ref(v_arg_629_);
v___x_641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_641_, 0, v_arg_629_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
lean_ctor_set(v___x_641_, 2, v___y_632_);
v___x_642_ = lean_string_utf8_next_fast(v_arg_629_, v___y_632_);
lean_dec(v___y_632_);
v_name_643_ = l_String_Slice_toName(v___x_641_);
lean_dec_ref_known(v___x_641_, 3);
v_val_644_ = lean_string_utf8_extract_fast(v_arg_629_, v___x_642_, v___x_633_);
lean_dec_ref(v_arg_629_);
v___x_645_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_636_, v_name_643_);
lean_dec(v_a_636_);
if (lean_obj_tag(v___x_645_) == 1)
{
lean_object* v_val_646_; lean_object* v___x_647_; 
lean_del_object(v___x_638_);
v_val_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_val_646_);
lean_dec_ref_known(v___x_645_, 1);
v___x_647_ = l_Lean_Language_Lean_setOption(v_opts_628_, v_val_646_, v_name_643_, v_val_644_);
return v___x_647_;
}
else
{
lean_object* v___x_648_; lean_object* v___x_650_; 
lean_dec(v___x_645_);
v___x_648_ = l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0(v_opts_628_, v_name_643_, v_val_644_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_648_);
v___x_650_ = v___x_638_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec(v___y_632_);
lean_dec_ref(v_arg_629_);
lean_dec_ref(v_opts_628_);
v_a_653_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_635_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_635_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
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
lean_object* v___x_661_; lean_object* v___x_662_; 
lean_dec(v___y_632_);
lean_dec_ref(v_arg_629_);
lean_dec_ref(v_opts_628_);
v___x_661_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_setConfigOption___closed__1));
v___x_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
return v___x_662_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_setConfigOption___boxed(lean_object* v_opts_669_, lean_object* v_arg_670_, lean_object* v_a_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_opts_669_, v_arg_670_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(lean_object* v___x_673_, lean_object* v_arg_674_, lean_object* v_inst_675_, lean_object* v_R_676_, lean_object* v_a_677_, lean_object* v_b_678_, lean_object* v_c_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_673_, v_arg_674_, v_a_677_, v_b_678_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___boxed(lean_object* v___x_681_, lean_object* v_arg_682_, lean_object* v_inst_683_, lean_object* v_R_684_, lean_object* v_a_685_, lean_object* v_b_686_, lean_object* v_c_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(v___x_681_, v_arg_682_, v_inst_683_, v_R_684_, v_a_685_, v_b_686_, v_c_687_);
lean_dec(v_b_686_);
lean_dec_ref(v_arg_682_);
lean_dec_ref(v___x_681_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(lean_object* v_msg_690_){
_start:
{
lean_object* v___f_692_; lean_object* v___x_693_; 
v___f_692_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_693_ = l_IO_eprint___redArg(v___f_692_, v_msg_690_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_693_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_693_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
else
{
lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_709_; 
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; 
v_unused_710_ = lean_ctor_get(v___x_693_, 0);
lean_dec(v_unused_710_);
v___x_703_ = v___x_693_;
v_isShared_704_ = v_isSharedCheck_709_;
goto v_resetjp_702_;
}
else
{
lean_dec(v___x_693_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_709_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v___x_707_; 
v___x_705_ = lean_box(0);
if (v_isShared_704_ == 0)
{
lean_ctor_set_tag(v___x_703_, 0);
lean_ctor_set(v___x_703_, 0, v___x_705_);
v___x_707_ = v___x_703_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___boxed(lean_object* v_msg_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(v_msg_711_);
return v_res_713_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_716_; lean_object* v___x_717_; 
v___x_716_ = 1;
v___x_717_ = lean_box_uint32(v___x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(lean_object* v_x_718_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = lean_apply_1(v_x_718_, lean_box(0));
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_727_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_727_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_741_; lean_object* v___f_742_; lean_object* v___x_743_; 
v_a_736_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___x_727_, 1);
v___x_741_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___f_742_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_743_ = l_IO_eprint___redArg(v___f_742_, v___x_741_);
lean_dec_ref(v___x_743_);
goto v___jp_737_;
v___jp_737_:
{
lean_object* v___x_738_; lean_object* v___f_739_; lean_object* v___x_740_; 
v___x_738_ = lean_io_error_to_string(v_a_736_);
v___f_739_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_740_ = l_IO_eprint___redArg(v___f_739_, v___x_738_);
lean_dec_ref(v___x_740_);
goto v___jp_723_;
}
}
v___jp_720_:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
v___jp_723_:
{
lean_object* v___x_724_; lean_object* v___f_725_; lean_object* v___x_726_; 
v___x_724_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___f_725_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_726_ = l_IO_eprint___redArg(v___f_725_, v___x_724_);
lean_dec_ref(v___x_726_);
goto v___jp_720_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed(lean_object* v_x_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(v_x_744_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(lean_object* v_00_u03b1_747_, lean_object* v_x_748_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = lean_apply_1(v_x_748_, lean_box(0));
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_757_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_757_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_771_; lean_object* v___f_772_; lean_object* v___x_773_; 
v_a_766_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_757_, 1);
v___x_771_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___f_772_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_773_ = l_IO_eprint___redArg(v___f_772_, v___x_771_);
lean_dec_ref(v___x_773_);
goto v___jp_767_;
v___jp_767_:
{
lean_object* v___x_768_; lean_object* v___f_769_; lean_object* v___x_770_; 
v___x_768_ = lean_io_error_to_string(v_a_766_);
v___f_769_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_770_ = l_IO_eprint___redArg(v___f_769_, v___x_768_);
lean_dec_ref(v___x_770_);
goto v___jp_753_;
}
}
v___jp_750_:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
return v___x_752_;
}
v___jp_753_:
{
lean_object* v___x_754_; lean_object* v___f_755_; lean_object* v___x_756_; 
v___x_754_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___f_755_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_756_ = l_IO_eprint___redArg(v___f_755_, v___x_754_);
lean_dec_ref(v___x_756_);
goto v___jp_750_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___boxed(lean_object* v_00_u03b1_774_, lean_object* v_x_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(v_00_u03b1_774_, v_x_775_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(lean_object* v_opt_780_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___f_789_; lean_object* v___x_790_; 
v___x_785_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__0));
v___x_786_ = lean_string_append(v___x_785_, v_opt_780_);
v___x_787_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
v___x_788_ = lean_string_append(v___x_786_, v___x_787_);
v___f_789_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_790_ = l_IO_eprint___redArg(v___f_789_, v___x_788_);
lean_dec_ref(v___x_790_);
goto v___jp_782_;
v___jp_782_:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___boxed(lean_object* v_opt_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(v_opt_791_);
lean_dec_ref(v_opt_791_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(lean_object* v_opt_796_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___f_805_; lean_object* v___x_806_; 
v___x_801_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__0));
v___x_802_ = lean_string_append(v___x_801_, v_opt_796_);
v___x_803_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__1));
v___x_804_ = lean_string_append(v___x_802_, v___x_803_);
v___f_805_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_806_ = l_IO_eprint___redArg(v___f_805_, v___x_804_);
lean_dec_ref(v___x_806_);
goto v___jp_798_;
v___jp_798_:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
return v___x_800_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___boxed(lean_object* v_opt_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(v_opt_807_);
lean_dec_ref(v_opt_807_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(lean_object* v_s_810_){
_start:
{
lean_object* v___x_812_; lean_object* v_putStr_813_; lean_object* v___x_814_; 
v___x_812_ = lean_get_stderr();
v_putStr_813_ = lean_ctor_get(v___x_812_, 4);
lean_inc_ref(v_putStr_813_);
lean_dec_ref(v___x_812_);
v___x_814_ = lean_apply_2(v_putStr_813_, v_s_810_, lean_box(0));
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0___boxed(lean_object* v_s_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v_s_815_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(lean_object* v_s_818_){
_start:
{
lean_object* v___x_820_; lean_object* v_putStr_821_; lean_object* v___x_822_; 
v___x_820_ = lean_get_stdout();
v_putStr_821_ = lean_ctor_get(v___x_820_, 4);
lean_inc_ref(v_putStr_821_);
lean_dec_ref(v___x_820_);
v___x_822_ = lean_apply_2(v_putStr_821_, v_s_818_, lean_box(0));
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5___boxed(lean_object* v_s_823_, lean_object* v_a_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v_s_823_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(lean_object* v_s_826_){
_start:
{
uint32_t v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = 10;
v___x_829_ = lean_string_push(v_s_826_, v___x_828_);
v___x_830_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3___boxed(lean_object* v_s_831_, lean_object* v_a_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v_s_831_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(lean_object* v_o_834_, lean_object* v_k_835_, uint8_t v_v_836_){
_start:
{
lean_object* v_map_837_; uint8_t v_hasTrace_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_852_; 
v_map_837_ = lean_ctor_get(v_o_834_, 0);
v_hasTrace_838_ = lean_ctor_get_uint8(v_o_834_, sizeof(void*)*1);
v_isSharedCheck_852_ = !lean_is_exclusive(v_o_834_);
if (v_isSharedCheck_852_ == 0)
{
v___x_840_ = v_o_834_;
v_isShared_841_ = v_isSharedCheck_852_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_map_837_);
lean_dec(v_o_834_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_852_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_842_, 0, v_v_836_);
lean_inc(v_k_835_);
v___x_843_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_835_, v___x_842_, v_map_837_);
if (v_hasTrace_838_ == 0)
{
lean_object* v___x_844_; uint8_t v___x_845_; lean_object* v___x_847_; 
v___x_844_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_845_ = l_Lean_Name_isPrefixOf(v___x_844_, v_k_835_);
lean_dec(v_k_835_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_843_);
v___x_847_ = v___x_840_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_843_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_ctor_set_uint8(v___x_847_, sizeof(void*)*1, v___x_845_);
return v___x_847_;
}
}
else
{
lean_object* v___x_850_; 
lean_dec(v_k_835_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_843_);
v___x_850_ = v___x_840_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_843_);
lean_ctor_set_uint8(v_reuseFailAlloc_851_, sizeof(void*)*1, v_hasTrace_838_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1___boxed(lean_object* v_o_853_, lean_object* v_k_854_, lean_object* v_v_855_){
_start:
{
uint8_t v_v_boxed_856_; lean_object* v_res_857_; 
v_v_boxed_856_ = lean_unbox(v_v_855_);
v_res_857_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(v_o_853_, v_k_854_, v_v_boxed_856_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(lean_object* v_opts_858_, lean_object* v_opt_859_, uint8_t v_val_860_){
_start:
{
lean_object* v_name_861_; lean_object* v___x_862_; 
v_name_861_ = lean_ctor_get(v_opt_859_, 0);
lean_inc(v_name_861_);
lean_dec_ref(v_opt_859_);
v___x_862_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(v_opts_858_, v_name_861_, v_val_860_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1___boxed(lean_object* v_opts_863_, lean_object* v_opt_864_, lean_object* v_val_865_){
_start:
{
uint8_t v_val_boxed_866_; lean_object* v_res_867_; 
v_val_boxed_866_ = lean_unbox(v_val_865_);
v_res_867_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_opts_863_, v_opt_864_, v_val_boxed_866_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__3(lean_object* v_o_868_, lean_object* v_k_869_, lean_object* v_v_870_){
_start:
{
lean_object* v_map_871_; uint8_t v_hasTrace_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_886_; 
v_map_871_ = lean_ctor_get(v_o_868_, 0);
v_hasTrace_872_ = lean_ctor_get_uint8(v_o_868_, sizeof(void*)*1);
v_isSharedCheck_886_ = !lean_is_exclusive(v_o_868_);
if (v_isSharedCheck_886_ == 0)
{
v___x_874_ = v_o_868_;
v_isShared_875_ = v_isSharedCheck_886_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_map_871_);
lean_dec(v_o_868_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_886_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_876_, 0, v_v_870_);
lean_inc(v_k_869_);
v___x_877_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_869_, v___x_876_, v_map_871_);
if (v_hasTrace_872_ == 0)
{
lean_object* v___x_878_; uint8_t v___x_879_; lean_object* v___x_881_; 
v___x_878_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_879_ = l_Lean_Name_isPrefixOf(v___x_878_, v_k_869_);
lean_dec(v_k_869_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_877_);
v___x_881_ = v___x_874_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_877_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_ctor_set_uint8(v___x_881_, sizeof(void*)*1, v___x_879_);
return v___x_881_;
}
}
else
{
lean_object* v___x_884_; 
lean_dec(v_k_869_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_877_);
v___x_884_ = v___x_874_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_877_);
lean_ctor_set_uint8(v_reuseFailAlloc_885_, sizeof(void*)*1, v_hasTrace_872_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(lean_object* v_opts_887_, lean_object* v_opt_888_, lean_object* v_val_889_){
_start:
{
lean_object* v_name_890_; lean_object* v___x_891_; 
v_name_890_ = lean_ctor_get(v_opt_888_, 0);
lean_inc(v_name_890_);
lean_dec_ref(v_opt_888_);
v___x_891_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__3(v_opts_887_, v_name_890_, v_val_889_);
return v___x_891_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_920_ = l_System_Platform_numBits;
v___x_921_ = lean_unsigned_to_nat(2u);
v___x_922_ = lean_nat_pow(v___x_921_, v___x_920_);
return v___x_922_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1(void){
_start:
{
uint32_t v___x_932_; lean_object* v___x_933_; 
v___x_932_ = 0;
v___x_933_ = lean_box_uint32(v___x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* lean_shell_options_process(lean_object* v_opts_934_, uint32_t v_opt_935_, lean_object* v_optArg_x3f_936_){
_start:
{
lean_object* v___y_1050_; lean_object* v___y_1096_; uint32_t v___x_1156_; uint8_t v___x_1157_; 
v___x_1156_ = 101;
v___x_1157_ = lean_uint32_dec_eq(v_opt_935_, v___x_1156_);
if (v___x_1157_ == 0)
{
uint32_t v___x_1158_; uint8_t v___x_1159_; 
v___x_1158_ = 106;
v___x_1159_ = lean_uint32_dec_eq(v_opt_935_, v___x_1158_);
if (v___x_1159_ == 0)
{
uint32_t v___x_1160_; uint8_t v___x_1161_; 
v___x_1160_ = 118;
v___x_1161_ = lean_uint32_dec_eq(v_opt_935_, v___x_1160_);
if (v___x_1161_ == 0)
{
uint32_t v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = 86;
v___x_1163_ = lean_uint32_dec_eq(v_opt_935_, v___x_1162_);
if (v___x_1163_ == 0)
{
uint32_t v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = 103;
v___x_1165_ = lean_uint32_dec_eq(v_opt_935_, v___x_1164_);
if (v___x_1165_ == 0)
{
uint32_t v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = 104;
v___x_1167_ = lean_uint32_dec_eq(v_opt_935_, v___x_1166_);
if (v___x_1167_ == 0)
{
uint32_t v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = 102;
v___x_1169_ = lean_uint32_dec_eq(v_opt_935_, v___x_1168_);
if (v___x_1169_ == 0)
{
uint32_t v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = 99;
v___x_1171_ = lean_uint32_dec_eq(v_opt_935_, v___x_1170_);
if (v___x_1171_ == 0)
{
uint32_t v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = 98;
v___x_1173_ = lean_uint32_dec_eq(v_opt_935_, v___x_1172_);
if (v___x_1173_ == 0)
{
uint32_t v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = 115;
v___x_1175_ = lean_uint32_dec_eq(v_opt_935_, v___x_1174_);
if (v___x_1175_ == 0)
{
uint32_t v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = 73;
v___x_1177_ = lean_uint32_dec_eq(v_opt_935_, v___x_1176_);
if (v___x_1177_ == 0)
{
uint32_t v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = 114;
v___x_1179_ = lean_uint32_dec_eq(v_opt_935_, v___x_1178_);
if (v___x_1179_ == 0)
{
uint32_t v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = 111;
v___x_1181_ = lean_uint32_dec_eq(v_opt_935_, v___x_1180_);
if (v___x_1181_ == 0)
{
uint32_t v___x_1182_; uint8_t v___x_1183_; 
v___x_1182_ = 105;
v___x_1183_ = lean_uint32_dec_eq(v_opt_935_, v___x_1182_);
if (v___x_1183_ == 0)
{
uint32_t v___x_1184_; uint8_t v___x_1185_; 
v___x_1184_ = 82;
v___x_1185_ = lean_uint32_dec_eq(v_opt_935_, v___x_1184_);
if (v___x_1185_ == 0)
{
uint32_t v___x_1186_; uint8_t v___x_1187_; 
v___x_1186_ = 77;
v___x_1187_ = lean_uint32_dec_eq(v_opt_935_, v___x_1186_);
if (v___x_1187_ == 0)
{
uint32_t v___x_1188_; uint8_t v___x_1189_; 
v___x_1188_ = 84;
v___x_1189_ = lean_uint32_dec_eq(v_opt_935_, v___x_1188_);
if (v___x_1189_ == 0)
{
uint32_t v___x_1190_; uint8_t v___x_1191_; 
v___x_1190_ = 116;
v___x_1191_ = lean_uint32_dec_eq(v_opt_935_, v___x_1190_);
if (v___x_1191_ == 0)
{
uint32_t v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = 113;
v___x_1193_ = lean_uint32_dec_eq(v_opt_935_, v___x_1192_);
if (v___x_1193_ == 0)
{
uint32_t v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = 100;
v___x_1195_ = lean_uint32_dec_eq(v_opt_935_, v___x_1194_);
if (v___x_1195_ == 0)
{
uint32_t v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = 79;
v___x_1197_ = lean_uint32_dec_eq(v_opt_935_, v___x_1196_);
if (v___x_1197_ == 0)
{
uint32_t v___x_1198_; uint8_t v___x_1199_; 
v___x_1198_ = 78;
v___x_1199_ = lean_uint32_dec_eq(v_opt_935_, v___x_1198_);
if (v___x_1199_ == 0)
{
uint32_t v___x_1200_; uint8_t v___x_1201_; 
v___x_1200_ = 74;
v___x_1201_ = lean_uint32_dec_eq(v_opt_935_, v___x_1200_);
if (v___x_1201_ == 0)
{
uint32_t v___x_1202_; uint8_t v___x_1203_; 
v___x_1202_ = 97;
v___x_1203_ = lean_uint32_dec_eq(v_opt_935_, v___x_1202_);
if (v___x_1203_ == 0)
{
uint32_t v___x_1204_; uint8_t v___x_1205_; 
v___x_1204_ = 120;
v___x_1205_ = lean_uint32_dec_eq(v_opt_935_, v___x_1204_);
if (v___x_1205_ == 0)
{
uint32_t v___x_1206_; uint8_t v___x_1207_; 
v___x_1206_ = 76;
v___x_1207_ = lean_uint32_dec_eq(v_opt_935_, v___x_1206_);
if (v___x_1207_ == 0)
{
uint32_t v___x_1208_; uint8_t v___x_1209_; 
v___x_1208_ = 68;
v___x_1209_ = lean_uint32_dec_eq(v_opt_935_, v___x_1208_);
if (v___x_1209_ == 0)
{
uint32_t v___x_1210_; uint8_t v___x_1211_; 
v___x_1210_ = 83;
v___x_1211_ = lean_uint32_dec_eq(v_opt_935_, v___x_1210_);
if (v___x_1211_ == 0)
{
uint32_t v___x_1212_; uint8_t v___x_1213_; 
v___x_1212_ = 87;
v___x_1213_ = lean_uint32_dec_eq(v_opt_935_, v___x_1212_);
if (v___x_1213_ == 0)
{
uint32_t v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = 80;
v___x_1215_ = lean_uint32_dec_eq(v_opt_935_, v___x_1214_);
if (v___x_1215_ == 0)
{
uint32_t v___x_1216_; uint8_t v___x_1217_; 
v___x_1216_ = 66;
v___x_1217_ = lean_uint32_dec_eq(v_opt_935_, v___x_1216_);
if (v___x_1217_ == 0)
{
uint32_t v___x_1218_; uint8_t v___x_1219_; 
v___x_1218_ = 112;
v___x_1219_ = lean_uint32_dec_eq(v_opt_935_, v___x_1218_);
if (v___x_1219_ == 0)
{
uint32_t v___x_1220_; uint8_t v___x_1221_; 
v___x_1220_ = 108;
v___x_1221_ = lean_uint32_dec_eq(v_opt_935_, v___x_1220_);
if (v___x_1221_ == 0)
{
uint32_t v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = 117;
v___x_1223_ = lean_uint32_dec_eq(v_opt_935_, v___x_1222_);
if (v___x_1223_ == 0)
{
uint32_t v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = 69;
v___x_1225_ = lean_uint32_dec_eq(v_opt_935_, v___x_1224_);
if (v___x_1225_ == 0)
{
uint32_t v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = 89;
v___x_1227_ = lean_uint32_dec_eq(v_opt_935_, v___x_1226_);
if (v___x_1227_ == 0)
{
uint32_t v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = 90;
v___x_1229_ = lean_uint32_dec_eq(v_opt_935_, v___x_1228_);
if (v___x_1229_ == 0)
{
uint32_t v___x_1230_; uint8_t v___x_1231_; 
v___x_1230_ = 72;
v___x_1231_ = lean_uint32_dec_eq(v_opt_935_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_dec(v_optArg_x3f_936_);
lean_dec_ref(v_opts_934_);
goto v___jp_1068_;
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1));
v___x_1233_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1232_, v_optArg_x3f_936_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1274_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1236_ = v___x_1233_;
v_isShared_1237_ = v_isSharedCheck_1274_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1233_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1274_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v_leanOpts_1238_; lean_object* v_forwardedArgs_1239_; uint8_t v_component_1240_; uint8_t v_printPrefix_1241_; uint8_t v_printLibDir_1242_; uint8_t v_useStdin_1243_; uint8_t v_onlyDeps_1244_; uint8_t v_onlySrcDeps_1245_; uint8_t v_depsJson_1246_; lean_object* v_opts_1247_; uint32_t v_trustLevel_1248_; uint32_t v_numThreads_1249_; lean_object* v_rootDir_x3f_1250_; lean_object* v_setupFileName_x3f_1251_; lean_object* v_oleanFileName_x3f_1252_; lean_object* v_ileanFileName_x3f_1253_; lean_object* v_cFileName_x3f_1254_; lean_object* v_bcFileName_x3f_1255_; uint8_t v_jsonOutput_1256_; lean_object* v_errorOnKinds_1257_; uint8_t v_printStats_1258_; uint8_t v_run_1259_; lean_object* v_incrSaveFileName_x3f_1260_; lean_object* v_incrLoadFileName_x3f_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1272_; 
v_leanOpts_1238_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_1239_ = lean_ctor_get(v_opts_934_, 1);
v_component_1240_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_1241_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_1242_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_1243_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_1244_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1245_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_1246_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_1247_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_1248_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_1249_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1250_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_1251_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_1252_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_1253_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_1254_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_1255_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_1256_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_1257_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_1258_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_1259_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1260_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_1261_ = lean_ctor_get(v_opts_934_, 11);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_1272_ == 0)
{
lean_object* v_unused_1273_; 
v_unused_1273_ = lean_ctor_get(v_opts_934_, 12);
lean_dec(v_unused_1273_);
v___x_1263_ = v_opts_934_;
v_isShared_1264_ = v_isSharedCheck_1272_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_incrLoadFileName_x3f_1261_);
lean_inc(v_incrSaveFileName_x3f_1260_);
lean_inc(v_errorOnKinds_1257_);
lean_inc(v_bcFileName_x3f_1255_);
lean_inc(v_cFileName_x3f_1254_);
lean_inc(v_ileanFileName_x3f_1253_);
lean_inc(v_oleanFileName_x3f_1252_);
lean_inc(v_setupFileName_x3f_1251_);
lean_inc(v_rootDir_x3f_1250_);
lean_inc(v_opts_1247_);
lean_inc(v_forwardedArgs_1239_);
lean_inc(v_leanOpts_1238_);
lean_dec(v_opts_934_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1272_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1265_, 0, v_a_1234_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 12, v___x_1265_);
v___x_1267_ = v___x_1263_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_leanOpts_1238_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_forwardedArgs_1239_);
lean_ctor_set(v_reuseFailAlloc_1271_, 2, v_opts_1247_);
lean_ctor_set(v_reuseFailAlloc_1271_, 3, v_rootDir_x3f_1250_);
lean_ctor_set(v_reuseFailAlloc_1271_, 4, v_setupFileName_x3f_1251_);
lean_ctor_set(v_reuseFailAlloc_1271_, 5, v_oleanFileName_x3f_1252_);
lean_ctor_set(v_reuseFailAlloc_1271_, 6, v_ileanFileName_x3f_1253_);
lean_ctor_set(v_reuseFailAlloc_1271_, 7, v_cFileName_x3f_1254_);
lean_ctor_set(v_reuseFailAlloc_1271_, 8, v_bcFileName_x3f_1255_);
lean_ctor_set(v_reuseFailAlloc_1271_, 9, v_errorOnKinds_1257_);
lean_ctor_set(v_reuseFailAlloc_1271_, 10, v_incrSaveFileName_x3f_1260_);
lean_ctor_set(v_reuseFailAlloc_1271_, 11, v_incrLoadFileName_x3f_1261_);
lean_ctor_set(v_reuseFailAlloc_1271_, 12, v___x_1265_);
lean_ctor_set_uint8(v_reuseFailAlloc_1271_, sizeof(void*)*13 + 8, v_component_1240_);
lean_ctor_set_uint8(v_reuseFailAlloc_1271_, sizeof(void*)*13 + 9, v_printPrefix_1241_);
lean_ctor_set_uint8(v_reuseFailAlloc_1271_, sizeof(void*)*13 + 10, v_printLibDir_1242_);
lean_ctor_set_uint8(v_reuseFailAlloc_1271_, sizeof(void*)*13 + 11, v_useStdin_1243_);
lean_ctor_set_uint8(v_reuseFailAlloc_1271_, sizeof(void*)*13 + 12, v_onlyDeps_1244_);
lean_ctor_set_uint8(v_reuseFailAlloc_1271_, sizeof(void*)*13 + 13, v_onlySrcDeps_1245_);
lean_ctor_set_uint8(v_reuseFailAlloc_1271_, sizeof(void*)*13 + 14, v_depsJson_1246_);
lean_ctor_set_uint32(v_reuseFailAlloc_1271_, sizeof(void*)*13, v_trustLevel_1248_);
lean_ctor_set_uint32(v_reuseFailAlloc_1271_, sizeof(void*)*13 + 4, v_numThreads_1249_);
lean_ctor_set_uint8(v_reuseFailAlloc_1271_, sizeof(void*)*13 + 15, v_jsonOutput_1256_);
lean_ctor_set_uint8(v_reuseFailAlloc_1271_, sizeof(void*)*13 + 16, v_printStats_1258_);
lean_ctor_set_uint8(v_reuseFailAlloc_1271_, sizeof(void*)*13 + 17, v_run_1259_);
v___x_1267_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_object* v___x_1269_; 
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v___x_1267_);
v___x_1269_ = v___x_1236_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_dec_ref(v_opts_934_);
v_a_1275_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1233_, 1);
v___x_1279_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1280_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1279_);
lean_dec_ref(v___x_1280_);
goto v___jp_1276_;
v___jp_1276_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = lean_io_error_to_string(v_a_1275_);
v___x_1278_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1277_);
lean_dec_ref(v___x_1278_);
goto v___jp_1040_;
}
}
}
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2));
v___x_1282_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1281_, v_optArg_x3f_936_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1323_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1323_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1323_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v_leanOpts_1287_; lean_object* v_forwardedArgs_1288_; uint8_t v_component_1289_; uint8_t v_printPrefix_1290_; uint8_t v_printLibDir_1291_; uint8_t v_useStdin_1292_; uint8_t v_onlyDeps_1293_; uint8_t v_onlySrcDeps_1294_; uint8_t v_depsJson_1295_; lean_object* v_opts_1296_; uint32_t v_trustLevel_1297_; uint32_t v_numThreads_1298_; lean_object* v_rootDir_x3f_1299_; lean_object* v_setupFileName_x3f_1300_; lean_object* v_oleanFileName_x3f_1301_; lean_object* v_ileanFileName_x3f_1302_; lean_object* v_cFileName_x3f_1303_; lean_object* v_bcFileName_x3f_1304_; uint8_t v_jsonOutput_1305_; lean_object* v_errorOnKinds_1306_; uint8_t v_printStats_1307_; uint8_t v_run_1308_; lean_object* v_incrSaveFileName_x3f_1309_; lean_object* v_incrHeaderSaveFileName_x3f_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1321_; 
v_leanOpts_1287_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_1288_ = lean_ctor_get(v_opts_934_, 1);
v_component_1289_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_1290_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_1291_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_1292_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_1293_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1294_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_1295_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_1296_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_1297_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_1298_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1299_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_1300_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_1301_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_1302_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_1303_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_1304_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_1305_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_1306_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_1307_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_1308_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1309_ = lean_ctor_get(v_opts_934_, 10);
v_incrHeaderSaveFileName_x3f_1310_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_1321_ == 0)
{
lean_object* v_unused_1322_; 
v_unused_1322_ = lean_ctor_get(v_opts_934_, 11);
lean_dec(v_unused_1322_);
v___x_1312_ = v_opts_934_;
v_isShared_1313_ = v_isSharedCheck_1321_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1310_);
lean_inc(v_incrSaveFileName_x3f_1309_);
lean_inc(v_errorOnKinds_1306_);
lean_inc(v_bcFileName_x3f_1304_);
lean_inc(v_cFileName_x3f_1303_);
lean_inc(v_ileanFileName_x3f_1302_);
lean_inc(v_oleanFileName_x3f_1301_);
lean_inc(v_setupFileName_x3f_1300_);
lean_inc(v_rootDir_x3f_1299_);
lean_inc(v_opts_1296_);
lean_inc(v_forwardedArgs_1288_);
lean_inc(v_leanOpts_1287_);
lean_dec(v_opts_934_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1321_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1314_, 0, v_a_1283_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 11, v___x_1314_);
v___x_1316_ = v___x_1312_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_leanOpts_1287_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v_forwardedArgs_1288_);
lean_ctor_set(v_reuseFailAlloc_1320_, 2, v_opts_1296_);
lean_ctor_set(v_reuseFailAlloc_1320_, 3, v_rootDir_x3f_1299_);
lean_ctor_set(v_reuseFailAlloc_1320_, 4, v_setupFileName_x3f_1300_);
lean_ctor_set(v_reuseFailAlloc_1320_, 5, v_oleanFileName_x3f_1301_);
lean_ctor_set(v_reuseFailAlloc_1320_, 6, v_ileanFileName_x3f_1302_);
lean_ctor_set(v_reuseFailAlloc_1320_, 7, v_cFileName_x3f_1303_);
lean_ctor_set(v_reuseFailAlloc_1320_, 8, v_bcFileName_x3f_1304_);
lean_ctor_set(v_reuseFailAlloc_1320_, 9, v_errorOnKinds_1306_);
lean_ctor_set(v_reuseFailAlloc_1320_, 10, v_incrSaveFileName_x3f_1309_);
lean_ctor_set(v_reuseFailAlloc_1320_, 11, v___x_1314_);
lean_ctor_set(v_reuseFailAlloc_1320_, 12, v_incrHeaderSaveFileName_x3f_1310_);
lean_ctor_set_uint8(v_reuseFailAlloc_1320_, sizeof(void*)*13 + 8, v_component_1289_);
lean_ctor_set_uint8(v_reuseFailAlloc_1320_, sizeof(void*)*13 + 9, v_printPrefix_1290_);
lean_ctor_set_uint8(v_reuseFailAlloc_1320_, sizeof(void*)*13 + 10, v_printLibDir_1291_);
lean_ctor_set_uint8(v_reuseFailAlloc_1320_, sizeof(void*)*13 + 11, v_useStdin_1292_);
lean_ctor_set_uint8(v_reuseFailAlloc_1320_, sizeof(void*)*13 + 12, v_onlyDeps_1293_);
lean_ctor_set_uint8(v_reuseFailAlloc_1320_, sizeof(void*)*13 + 13, v_onlySrcDeps_1294_);
lean_ctor_set_uint8(v_reuseFailAlloc_1320_, sizeof(void*)*13 + 14, v_depsJson_1295_);
lean_ctor_set_uint32(v_reuseFailAlloc_1320_, sizeof(void*)*13, v_trustLevel_1297_);
lean_ctor_set_uint32(v_reuseFailAlloc_1320_, sizeof(void*)*13 + 4, v_numThreads_1298_);
lean_ctor_set_uint8(v_reuseFailAlloc_1320_, sizeof(void*)*13 + 15, v_jsonOutput_1305_);
lean_ctor_set_uint8(v_reuseFailAlloc_1320_, sizeof(void*)*13 + 16, v_printStats_1307_);
lean_ctor_set_uint8(v_reuseFailAlloc_1320_, sizeof(void*)*13 + 17, v_run_1308_);
v___x_1316_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1318_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1316_);
v___x_1318_ = v___x_1285_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
lean_dec_ref(v_opts_934_);
v_a_1324_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1324_);
lean_dec_ref_known(v___x_1282_, 1);
v___x_1328_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1329_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1328_);
lean_dec_ref(v___x_1329_);
goto v___jp_1325_;
v___jp_1325_:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = lean_io_error_to_string(v_a_1324_);
v___x_1327_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1326_);
lean_dec_ref(v___x_1327_);
goto v___jp_1074_;
}
}
}
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3));
v___x_1331_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1330_, v_optArg_x3f_936_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1372_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1334_ = v___x_1331_;
v_isShared_1335_ = v_isSharedCheck_1372_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1372_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v_leanOpts_1336_; lean_object* v_forwardedArgs_1337_; uint8_t v_component_1338_; uint8_t v_printPrefix_1339_; uint8_t v_printLibDir_1340_; uint8_t v_useStdin_1341_; uint8_t v_onlyDeps_1342_; uint8_t v_onlySrcDeps_1343_; uint8_t v_depsJson_1344_; lean_object* v_opts_1345_; uint32_t v_trustLevel_1346_; uint32_t v_numThreads_1347_; lean_object* v_rootDir_x3f_1348_; lean_object* v_setupFileName_x3f_1349_; lean_object* v_oleanFileName_x3f_1350_; lean_object* v_ileanFileName_x3f_1351_; lean_object* v_cFileName_x3f_1352_; lean_object* v_bcFileName_x3f_1353_; uint8_t v_jsonOutput_1354_; lean_object* v_errorOnKinds_1355_; uint8_t v_printStats_1356_; uint8_t v_run_1357_; lean_object* v_incrLoadFileName_x3f_1358_; lean_object* v_incrHeaderSaveFileName_x3f_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1370_; 
v_leanOpts_1336_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_1337_ = lean_ctor_get(v_opts_934_, 1);
v_component_1338_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_1339_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_1340_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_1341_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_1342_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1343_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_1344_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_1345_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_1346_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_1347_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1348_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_1349_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_1350_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_1351_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_1352_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_1353_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_1354_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_1355_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_1356_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_1357_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrLoadFileName_x3f_1358_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_1359_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_1370_ == 0)
{
lean_object* v_unused_1371_; 
v_unused_1371_ = lean_ctor_get(v_opts_934_, 10);
lean_dec(v_unused_1371_);
v___x_1361_ = v_opts_934_;
v_isShared_1362_ = v_isSharedCheck_1370_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1359_);
lean_inc(v_incrLoadFileName_x3f_1358_);
lean_inc(v_errorOnKinds_1355_);
lean_inc(v_bcFileName_x3f_1353_);
lean_inc(v_cFileName_x3f_1352_);
lean_inc(v_ileanFileName_x3f_1351_);
lean_inc(v_oleanFileName_x3f_1350_);
lean_inc(v_setupFileName_x3f_1349_);
lean_inc(v_rootDir_x3f_1348_);
lean_inc(v_opts_1345_);
lean_inc(v_forwardedArgs_1337_);
lean_inc(v_leanOpts_1336_);
lean_dec(v_opts_934_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1370_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1363_, 0, v_a_1332_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 10, v___x_1363_);
v___x_1365_ = v___x_1361_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_leanOpts_1336_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_forwardedArgs_1337_);
lean_ctor_set(v_reuseFailAlloc_1369_, 2, v_opts_1345_);
lean_ctor_set(v_reuseFailAlloc_1369_, 3, v_rootDir_x3f_1348_);
lean_ctor_set(v_reuseFailAlloc_1369_, 4, v_setupFileName_x3f_1349_);
lean_ctor_set(v_reuseFailAlloc_1369_, 5, v_oleanFileName_x3f_1350_);
lean_ctor_set(v_reuseFailAlloc_1369_, 6, v_ileanFileName_x3f_1351_);
lean_ctor_set(v_reuseFailAlloc_1369_, 7, v_cFileName_x3f_1352_);
lean_ctor_set(v_reuseFailAlloc_1369_, 8, v_bcFileName_x3f_1353_);
lean_ctor_set(v_reuseFailAlloc_1369_, 9, v_errorOnKinds_1355_);
lean_ctor_set(v_reuseFailAlloc_1369_, 10, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1369_, 11, v_incrLoadFileName_x3f_1358_);
lean_ctor_set(v_reuseFailAlloc_1369_, 12, v_incrHeaderSaveFileName_x3f_1359_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, sizeof(void*)*13 + 8, v_component_1338_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, sizeof(void*)*13 + 9, v_printPrefix_1339_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, sizeof(void*)*13 + 10, v_printLibDir_1340_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, sizeof(void*)*13 + 11, v_useStdin_1341_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, sizeof(void*)*13 + 12, v_onlyDeps_1342_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, sizeof(void*)*13 + 13, v_onlySrcDeps_1343_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, sizeof(void*)*13 + 14, v_depsJson_1344_);
lean_ctor_set_uint32(v_reuseFailAlloc_1369_, sizeof(void*)*13, v_trustLevel_1346_);
lean_ctor_set_uint32(v_reuseFailAlloc_1369_, sizeof(void*)*13 + 4, v_numThreads_1347_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, sizeof(void*)*13 + 15, v_jsonOutput_1354_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, sizeof(void*)*13 + 16, v_printStats_1356_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, sizeof(void*)*13 + 17, v_run_1357_);
v___x_1365_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1367_; 
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1365_);
v___x_1367_ = v___x_1334_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
lean_dec_ref(v_opts_934_);
v_a_1373_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_a_1373_);
lean_dec_ref_known(v___x_1331_, 1);
v___x_1377_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1378_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1377_);
lean_dec_ref(v___x_1378_);
goto v___jp_1374_;
v___jp_1374_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = lean_io_error_to_string(v_a_1373_);
v___x_1376_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1375_);
lean_dec_ref(v___x_1376_);
goto v___jp_1034_;
}
}
}
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4));
v___x_1380_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1379_, v_optArg_x3f_936_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1422_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1383_ = v___x_1380_;
v_isShared_1384_ = v_isSharedCheck_1422_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1380_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1422_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v_leanOpts_1385_; lean_object* v_forwardedArgs_1386_; uint8_t v_component_1387_; uint8_t v_printPrefix_1388_; uint8_t v_printLibDir_1389_; uint8_t v_useStdin_1390_; uint8_t v_onlyDeps_1391_; uint8_t v_onlySrcDeps_1392_; uint8_t v_depsJson_1393_; lean_object* v_opts_1394_; uint32_t v_trustLevel_1395_; uint32_t v_numThreads_1396_; lean_object* v_rootDir_x3f_1397_; lean_object* v_setupFileName_x3f_1398_; lean_object* v_oleanFileName_x3f_1399_; lean_object* v_ileanFileName_x3f_1400_; lean_object* v_cFileName_x3f_1401_; lean_object* v_bcFileName_x3f_1402_; uint8_t v_jsonOutput_1403_; lean_object* v_errorOnKinds_1404_; uint8_t v_printStats_1405_; uint8_t v_run_1406_; lean_object* v_incrSaveFileName_x3f_1407_; lean_object* v_incrLoadFileName_x3f_1408_; lean_object* v_incrHeaderSaveFileName_x3f_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1421_; 
v_leanOpts_1385_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_1386_ = lean_ctor_get(v_opts_934_, 1);
v_component_1387_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_1388_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_1389_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_1390_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_1391_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1392_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_1393_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_1394_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_1395_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_1396_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1397_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_1398_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_1399_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_1400_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_1401_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_1402_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_1403_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_1404_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_1405_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_1406_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1407_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_1408_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_1409_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1411_ = v_opts_934_;
v_isShared_1412_ = v_isSharedCheck_1421_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1409_);
lean_inc(v_incrLoadFileName_x3f_1408_);
lean_inc(v_incrSaveFileName_x3f_1407_);
lean_inc(v_errorOnKinds_1404_);
lean_inc(v_bcFileName_x3f_1402_);
lean_inc(v_cFileName_x3f_1401_);
lean_inc(v_ileanFileName_x3f_1400_);
lean_inc(v_oleanFileName_x3f_1399_);
lean_inc(v_setupFileName_x3f_1398_);
lean_inc(v_rootDir_x3f_1397_);
lean_inc(v_opts_1394_);
lean_inc(v_forwardedArgs_1386_);
lean_inc(v_leanOpts_1385_);
lean_dec(v_opts_934_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1421_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1413_ = l_String_toName(v_a_1381_);
v___x_1414_ = lean_array_push(v_errorOnKinds_1404_, v___x_1413_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 9, v___x_1414_);
v___x_1416_ = v___x_1411_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_leanOpts_1385_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_forwardedArgs_1386_);
lean_ctor_set(v_reuseFailAlloc_1420_, 2, v_opts_1394_);
lean_ctor_set(v_reuseFailAlloc_1420_, 3, v_rootDir_x3f_1397_);
lean_ctor_set(v_reuseFailAlloc_1420_, 4, v_setupFileName_x3f_1398_);
lean_ctor_set(v_reuseFailAlloc_1420_, 5, v_oleanFileName_x3f_1399_);
lean_ctor_set(v_reuseFailAlloc_1420_, 6, v_ileanFileName_x3f_1400_);
lean_ctor_set(v_reuseFailAlloc_1420_, 7, v_cFileName_x3f_1401_);
lean_ctor_set(v_reuseFailAlloc_1420_, 8, v_bcFileName_x3f_1402_);
lean_ctor_set(v_reuseFailAlloc_1420_, 9, v___x_1414_);
lean_ctor_set(v_reuseFailAlloc_1420_, 10, v_incrSaveFileName_x3f_1407_);
lean_ctor_set(v_reuseFailAlloc_1420_, 11, v_incrLoadFileName_x3f_1408_);
lean_ctor_set(v_reuseFailAlloc_1420_, 12, v_incrHeaderSaveFileName_x3f_1409_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*13 + 8, v_component_1387_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*13 + 9, v_printPrefix_1388_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*13 + 10, v_printLibDir_1389_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*13 + 11, v_useStdin_1390_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*13 + 12, v_onlyDeps_1391_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*13 + 13, v_onlySrcDeps_1392_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*13 + 14, v_depsJson_1393_);
lean_ctor_set_uint32(v_reuseFailAlloc_1420_, sizeof(void*)*13, v_trustLevel_1395_);
lean_ctor_set_uint32(v_reuseFailAlloc_1420_, sizeof(void*)*13 + 4, v_numThreads_1396_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*13 + 15, v_jsonOutput_1403_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*13 + 16, v_printStats_1405_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*13 + 17, v_run_1406_);
v___x_1416_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1418_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1416_);
v___x_1418_ = v___x_1383_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
lean_dec_ref(v_opts_934_);
v_a_1423_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1380_, 1);
v___x_1427_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1428_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1427_);
lean_dec_ref(v___x_1428_);
goto v___jp_1424_;
v___jp_1424_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = lean_io_error_to_string(v_a_1423_);
v___x_1426_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1425_);
lean_dec_ref(v___x_1426_);
goto v___jp_1080_;
}
}
}
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5));
v___x_1430_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1429_, v_optArg_x3f_936_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1471_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1433_ = v___x_1430_;
v_isShared_1434_ = v_isSharedCheck_1471_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1430_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1471_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v_leanOpts_1435_; lean_object* v_forwardedArgs_1436_; uint8_t v_component_1437_; uint8_t v_printPrefix_1438_; uint8_t v_printLibDir_1439_; uint8_t v_useStdin_1440_; uint8_t v_onlyDeps_1441_; uint8_t v_onlySrcDeps_1442_; uint8_t v_depsJson_1443_; lean_object* v_opts_1444_; uint32_t v_trustLevel_1445_; uint32_t v_numThreads_1446_; lean_object* v_rootDir_x3f_1447_; lean_object* v_oleanFileName_x3f_1448_; lean_object* v_ileanFileName_x3f_1449_; lean_object* v_cFileName_x3f_1450_; lean_object* v_bcFileName_x3f_1451_; uint8_t v_jsonOutput_1452_; lean_object* v_errorOnKinds_1453_; uint8_t v_printStats_1454_; uint8_t v_run_1455_; lean_object* v_incrSaveFileName_x3f_1456_; lean_object* v_incrLoadFileName_x3f_1457_; lean_object* v_incrHeaderSaveFileName_x3f_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1469_; 
v_leanOpts_1435_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_1436_ = lean_ctor_get(v_opts_934_, 1);
v_component_1437_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_1438_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_1439_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_1440_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_1441_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1442_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_1443_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_1444_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_1445_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_1446_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1447_ = lean_ctor_get(v_opts_934_, 3);
v_oleanFileName_x3f_1448_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_1449_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_1450_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_1451_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_1452_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_1453_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_1454_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_1455_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1456_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_1457_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_1458_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; 
v_unused_1470_ = lean_ctor_get(v_opts_934_, 4);
lean_dec(v_unused_1470_);
v___x_1460_ = v_opts_934_;
v_isShared_1461_ = v_isSharedCheck_1469_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1458_);
lean_inc(v_incrLoadFileName_x3f_1457_);
lean_inc(v_incrSaveFileName_x3f_1456_);
lean_inc(v_errorOnKinds_1453_);
lean_inc(v_bcFileName_x3f_1451_);
lean_inc(v_cFileName_x3f_1450_);
lean_inc(v_ileanFileName_x3f_1449_);
lean_inc(v_oleanFileName_x3f_1448_);
lean_inc(v_rootDir_x3f_1447_);
lean_inc(v_opts_1444_);
lean_inc(v_forwardedArgs_1436_);
lean_inc(v_leanOpts_1435_);
lean_dec(v_opts_934_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1469_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v___x_1464_; 
v___x_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1462_, 0, v_a_1431_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 4, v___x_1462_);
v___x_1464_ = v___x_1460_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_leanOpts_1435_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_forwardedArgs_1436_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_opts_1444_);
lean_ctor_set(v_reuseFailAlloc_1468_, 3, v_rootDir_x3f_1447_);
lean_ctor_set(v_reuseFailAlloc_1468_, 4, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1468_, 5, v_oleanFileName_x3f_1448_);
lean_ctor_set(v_reuseFailAlloc_1468_, 6, v_ileanFileName_x3f_1449_);
lean_ctor_set(v_reuseFailAlloc_1468_, 7, v_cFileName_x3f_1450_);
lean_ctor_set(v_reuseFailAlloc_1468_, 8, v_bcFileName_x3f_1451_);
lean_ctor_set(v_reuseFailAlloc_1468_, 9, v_errorOnKinds_1453_);
lean_ctor_set(v_reuseFailAlloc_1468_, 10, v_incrSaveFileName_x3f_1456_);
lean_ctor_set(v_reuseFailAlloc_1468_, 11, v_incrLoadFileName_x3f_1457_);
lean_ctor_set(v_reuseFailAlloc_1468_, 12, v_incrHeaderSaveFileName_x3f_1458_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*13 + 8, v_component_1437_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*13 + 9, v_printPrefix_1438_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*13 + 10, v_printLibDir_1439_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*13 + 11, v_useStdin_1440_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*13 + 12, v_onlyDeps_1441_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*13 + 13, v_onlySrcDeps_1442_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*13 + 14, v_depsJson_1443_);
lean_ctor_set_uint32(v_reuseFailAlloc_1468_, sizeof(void*)*13, v_trustLevel_1445_);
lean_ctor_set_uint32(v_reuseFailAlloc_1468_, sizeof(void*)*13 + 4, v_numThreads_1446_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*13 + 15, v_jsonOutput_1452_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*13 + 16, v_printStats_1454_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*13 + 17, v_run_1455_);
v___x_1464_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
lean_object* v___x_1466_; 
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 0, v___x_1464_);
v___x_1466_ = v___x_1433_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1464_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
lean_dec_ref(v_opts_934_);
v_a_1472_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1472_);
lean_dec_ref_known(v___x_1430_, 1);
v___x_1476_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1477_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1476_);
lean_dec_ref(v___x_1477_);
goto v___jp_1473_;
v___jp_1473_:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = lean_io_error_to_string(v_a_1472_);
v___x_1475_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1474_);
lean_dec_ref(v___x_1475_);
goto v___jp_1028_;
}
}
}
}
else
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1478_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6));
v___x_1479_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1478_, v_optArg_x3f_936_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1481_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc_n(v_a_1480_, 2);
lean_dec_ref_known(v___x_1479_, 1);
v___x_1481_ = lean_load_dynlib(v_a_1480_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1523_; 
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1523_ == 0)
{
lean_object* v_unused_1524_; 
v_unused_1524_ = lean_ctor_get(v___x_1481_, 0);
lean_dec(v_unused_1524_);
v___x_1483_ = v___x_1481_;
v_isShared_1484_ = v_isSharedCheck_1523_;
goto v_resetjp_1482_;
}
else
{
lean_dec(v___x_1481_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1523_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v_leanOpts_1485_; lean_object* v_forwardedArgs_1486_; uint8_t v_component_1487_; uint8_t v_printPrefix_1488_; uint8_t v_printLibDir_1489_; uint8_t v_useStdin_1490_; uint8_t v_onlyDeps_1491_; uint8_t v_onlySrcDeps_1492_; uint8_t v_depsJson_1493_; lean_object* v_opts_1494_; uint32_t v_trustLevel_1495_; uint32_t v_numThreads_1496_; lean_object* v_rootDir_x3f_1497_; lean_object* v_setupFileName_x3f_1498_; lean_object* v_oleanFileName_x3f_1499_; lean_object* v_ileanFileName_x3f_1500_; lean_object* v_cFileName_x3f_1501_; lean_object* v_bcFileName_x3f_1502_; uint8_t v_jsonOutput_1503_; lean_object* v_errorOnKinds_1504_; uint8_t v_printStats_1505_; uint8_t v_run_1506_; lean_object* v_incrSaveFileName_x3f_1507_; lean_object* v_incrLoadFileName_x3f_1508_; lean_object* v_incrHeaderSaveFileName_x3f_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1522_; 
v_leanOpts_1485_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_1486_ = lean_ctor_get(v_opts_934_, 1);
v_component_1487_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_1488_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_1489_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_1490_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_1491_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1492_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_1493_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_1494_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_1495_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_1496_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1497_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_1498_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_1499_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_1500_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_1501_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_1502_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_1503_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_1504_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_1505_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_1506_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1507_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_1508_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_1509_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_1522_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1511_ = v_opts_934_;
v_isShared_1512_ = v_isSharedCheck_1522_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1509_);
lean_inc(v_incrLoadFileName_x3f_1508_);
lean_inc(v_incrSaveFileName_x3f_1507_);
lean_inc(v_errorOnKinds_1504_);
lean_inc(v_bcFileName_x3f_1502_);
lean_inc(v_cFileName_x3f_1501_);
lean_inc(v_ileanFileName_x3f_1500_);
lean_inc(v_oleanFileName_x3f_1499_);
lean_inc(v_setupFileName_x3f_1498_);
lean_inc(v_rootDir_x3f_1497_);
lean_inc(v_opts_1494_);
lean_inc(v_forwardedArgs_1486_);
lean_inc(v_leanOpts_1485_);
lean_dec(v_opts_934_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1522_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1517_; 
v___x_1513_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7));
v___x_1514_ = lean_string_append(v___x_1513_, v_a_1480_);
lean_dec(v_a_1480_);
v___x_1515_ = lean_array_push(v_forwardedArgs_1486_, v___x_1514_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 1, v___x_1515_);
v___x_1517_ = v___x_1511_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_leanOpts_1485_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v___x_1515_);
lean_ctor_set(v_reuseFailAlloc_1521_, 2, v_opts_1494_);
lean_ctor_set(v_reuseFailAlloc_1521_, 3, v_rootDir_x3f_1497_);
lean_ctor_set(v_reuseFailAlloc_1521_, 4, v_setupFileName_x3f_1498_);
lean_ctor_set(v_reuseFailAlloc_1521_, 5, v_oleanFileName_x3f_1499_);
lean_ctor_set(v_reuseFailAlloc_1521_, 6, v_ileanFileName_x3f_1500_);
lean_ctor_set(v_reuseFailAlloc_1521_, 7, v_cFileName_x3f_1501_);
lean_ctor_set(v_reuseFailAlloc_1521_, 8, v_bcFileName_x3f_1502_);
lean_ctor_set(v_reuseFailAlloc_1521_, 9, v_errorOnKinds_1504_);
lean_ctor_set(v_reuseFailAlloc_1521_, 10, v_incrSaveFileName_x3f_1507_);
lean_ctor_set(v_reuseFailAlloc_1521_, 11, v_incrLoadFileName_x3f_1508_);
lean_ctor_set(v_reuseFailAlloc_1521_, 12, v_incrHeaderSaveFileName_x3f_1509_);
lean_ctor_set_uint8(v_reuseFailAlloc_1521_, sizeof(void*)*13 + 8, v_component_1487_);
lean_ctor_set_uint8(v_reuseFailAlloc_1521_, sizeof(void*)*13 + 9, v_printPrefix_1488_);
lean_ctor_set_uint8(v_reuseFailAlloc_1521_, sizeof(void*)*13 + 10, v_printLibDir_1489_);
lean_ctor_set_uint8(v_reuseFailAlloc_1521_, sizeof(void*)*13 + 11, v_useStdin_1490_);
lean_ctor_set_uint8(v_reuseFailAlloc_1521_, sizeof(void*)*13 + 12, v_onlyDeps_1491_);
lean_ctor_set_uint8(v_reuseFailAlloc_1521_, sizeof(void*)*13 + 13, v_onlySrcDeps_1492_);
lean_ctor_set_uint8(v_reuseFailAlloc_1521_, sizeof(void*)*13 + 14, v_depsJson_1493_);
lean_ctor_set_uint32(v_reuseFailAlloc_1521_, sizeof(void*)*13, v_trustLevel_1495_);
lean_ctor_set_uint32(v_reuseFailAlloc_1521_, sizeof(void*)*13 + 4, v_numThreads_1496_);
lean_ctor_set_uint8(v_reuseFailAlloc_1521_, sizeof(void*)*13 + 15, v_jsonOutput_1503_);
lean_ctor_set_uint8(v_reuseFailAlloc_1521_, sizeof(void*)*13 + 16, v_printStats_1505_);
lean_ctor_set_uint8(v_reuseFailAlloc_1521_, sizeof(void*)*13 + 17, v_run_1506_);
v___x_1517_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
lean_object* v___x_1519_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1517_);
v___x_1519_ = v___x_1483_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1517_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_dec(v_a_1480_);
lean_dec_ref(v_opts_934_);
v_a_1525_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1481_, 1);
v___x_1529_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1530_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1529_);
lean_dec_ref(v___x_1530_);
goto v___jp_1526_;
v___jp_1526_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = lean_io_error_to_string(v_a_1525_);
v___x_1528_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1527_);
lean_dec_ref(v___x_1528_);
goto v___jp_1086_;
}
}
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_dec_ref(v_opts_934_);
v_a_1531_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v___x_1479_, 1);
v___x_1535_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1536_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1535_);
lean_dec_ref(v___x_1536_);
goto v___jp_1532_;
v___jp_1532_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = lean_io_error_to_string(v_a_1531_);
v___x_1534_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1533_);
lean_dec_ref(v___x_1534_);
goto v___jp_1022_;
}
}
}
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8));
v___x_1538_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1537_, v_optArg_x3f_936_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1611_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1541_ = v___x_1538_;
v_isShared_1542_ = v_isSharedCheck_1611_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1611_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v_fst_1544_; lean_object* v_snd_1545_; lean_object* v___y_1594_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1605_ = lean_unsigned_to_nat(0u);
v___x_1606_ = lean_string_utf8_byte_size(v_a_1539_);
lean_inc(v_a_1539_);
v___x_1607_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1607_, 0, v_a_1539_);
lean_ctor_set(v___x_1607_, 1, v___x_1605_);
lean_ctor_set(v___x_1607_, 2, v___x_1606_);
v___x_1608_ = lean_box(0);
v___x_1609_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_1607_, v_a_1539_, v___x_1605_, v___x_1608_);
lean_dec_ref_known(v___x_1607_, 3);
if (lean_obj_tag(v___x_1609_) == 0)
{
v___y_1594_ = v___x_1606_;
goto v___jp_1593_;
}
else
{
lean_object* v_val_1610_; 
v_val_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_val_1610_);
lean_dec_ref_known(v___x_1609_, 1);
v___y_1594_ = v_val_1610_;
goto v___jp_1593_;
}
v___jp_1543_:
{
lean_object* v___x_1546_; 
v___x_1546_ = lean_load_plugin(v_fst_1544_, v_snd_1545_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1588_; 
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1588_ == 0)
{
lean_object* v_unused_1589_; 
v_unused_1589_ = lean_ctor_get(v___x_1546_, 0);
lean_dec(v_unused_1589_);
v___x_1548_ = v___x_1546_;
v_isShared_1549_ = v_isSharedCheck_1588_;
goto v_resetjp_1547_;
}
else
{
lean_dec(v___x_1546_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1588_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v_leanOpts_1550_; lean_object* v_forwardedArgs_1551_; uint8_t v_component_1552_; uint8_t v_printPrefix_1553_; uint8_t v_printLibDir_1554_; uint8_t v_useStdin_1555_; uint8_t v_onlyDeps_1556_; uint8_t v_onlySrcDeps_1557_; uint8_t v_depsJson_1558_; lean_object* v_opts_1559_; uint32_t v_trustLevel_1560_; uint32_t v_numThreads_1561_; lean_object* v_rootDir_x3f_1562_; lean_object* v_setupFileName_x3f_1563_; lean_object* v_oleanFileName_x3f_1564_; lean_object* v_ileanFileName_x3f_1565_; lean_object* v_cFileName_x3f_1566_; lean_object* v_bcFileName_x3f_1567_; uint8_t v_jsonOutput_1568_; lean_object* v_errorOnKinds_1569_; uint8_t v_printStats_1570_; uint8_t v_run_1571_; lean_object* v_incrSaveFileName_x3f_1572_; lean_object* v_incrLoadFileName_x3f_1573_; lean_object* v_incrHeaderSaveFileName_x3f_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1587_; 
v_leanOpts_1550_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_1551_ = lean_ctor_get(v_opts_934_, 1);
v_component_1552_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_1553_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_1554_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_1555_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_1556_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1557_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_1558_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_1559_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_1560_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_1561_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1562_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_1563_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_1564_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_1565_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_1566_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_1567_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_1568_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_1569_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_1570_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_1571_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1572_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_1573_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_1574_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1576_ = v_opts_934_;
v_isShared_1577_ = v_isSharedCheck_1587_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1574_);
lean_inc(v_incrLoadFileName_x3f_1573_);
lean_inc(v_incrSaveFileName_x3f_1572_);
lean_inc(v_errorOnKinds_1569_);
lean_inc(v_bcFileName_x3f_1567_);
lean_inc(v_cFileName_x3f_1566_);
lean_inc(v_ileanFileName_x3f_1565_);
lean_inc(v_oleanFileName_x3f_1564_);
lean_inc(v_setupFileName_x3f_1563_);
lean_inc(v_rootDir_x3f_1562_);
lean_inc(v_opts_1559_);
lean_inc(v_forwardedArgs_1551_);
lean_inc(v_leanOpts_1550_);
lean_dec(v_opts_934_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1587_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1582_; 
v___x_1578_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9));
v___x_1579_ = lean_string_append(v___x_1578_, v_a_1539_);
lean_dec(v_a_1539_);
v___x_1580_ = lean_array_push(v_forwardedArgs_1551_, v___x_1579_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 1, v___x_1580_);
v___x_1582_ = v___x_1576_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_leanOpts_1550_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1586_, 2, v_opts_1559_);
lean_ctor_set(v_reuseFailAlloc_1586_, 3, v_rootDir_x3f_1562_);
lean_ctor_set(v_reuseFailAlloc_1586_, 4, v_setupFileName_x3f_1563_);
lean_ctor_set(v_reuseFailAlloc_1586_, 5, v_oleanFileName_x3f_1564_);
lean_ctor_set(v_reuseFailAlloc_1586_, 6, v_ileanFileName_x3f_1565_);
lean_ctor_set(v_reuseFailAlloc_1586_, 7, v_cFileName_x3f_1566_);
lean_ctor_set(v_reuseFailAlloc_1586_, 8, v_bcFileName_x3f_1567_);
lean_ctor_set(v_reuseFailAlloc_1586_, 9, v_errorOnKinds_1569_);
lean_ctor_set(v_reuseFailAlloc_1586_, 10, v_incrSaveFileName_x3f_1572_);
lean_ctor_set(v_reuseFailAlloc_1586_, 11, v_incrLoadFileName_x3f_1573_);
lean_ctor_set(v_reuseFailAlloc_1586_, 12, v_incrHeaderSaveFileName_x3f_1574_);
lean_ctor_set_uint8(v_reuseFailAlloc_1586_, sizeof(void*)*13 + 8, v_component_1552_);
lean_ctor_set_uint8(v_reuseFailAlloc_1586_, sizeof(void*)*13 + 9, v_printPrefix_1553_);
lean_ctor_set_uint8(v_reuseFailAlloc_1586_, sizeof(void*)*13 + 10, v_printLibDir_1554_);
lean_ctor_set_uint8(v_reuseFailAlloc_1586_, sizeof(void*)*13 + 11, v_useStdin_1555_);
lean_ctor_set_uint8(v_reuseFailAlloc_1586_, sizeof(void*)*13 + 12, v_onlyDeps_1556_);
lean_ctor_set_uint8(v_reuseFailAlloc_1586_, sizeof(void*)*13 + 13, v_onlySrcDeps_1557_);
lean_ctor_set_uint8(v_reuseFailAlloc_1586_, sizeof(void*)*13 + 14, v_depsJson_1558_);
lean_ctor_set_uint32(v_reuseFailAlloc_1586_, sizeof(void*)*13, v_trustLevel_1560_);
lean_ctor_set_uint32(v_reuseFailAlloc_1586_, sizeof(void*)*13 + 4, v_numThreads_1561_);
lean_ctor_set_uint8(v_reuseFailAlloc_1586_, sizeof(void*)*13 + 15, v_jsonOutput_1568_);
lean_ctor_set_uint8(v_reuseFailAlloc_1586_, sizeof(void*)*13 + 16, v_printStats_1570_);
lean_ctor_set_uint8(v_reuseFailAlloc_1586_, sizeof(void*)*13 + 17, v_run_1571_);
v___x_1582_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1584_; 
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v___x_1582_);
v___x_1584_ = v___x_1548_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
lean_dec(v_a_1539_);
lean_dec_ref(v_opts_934_);
v_a_1590_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1546_, 1);
v___x_1591_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1592_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1591_);
lean_dec_ref(v___x_1592_);
v___y_1096_ = v_a_1590_;
goto v___jp_1095_;
}
}
v___jp_1593_:
{
lean_object* v___x_1595_; uint8_t v___x_1596_; 
v___x_1595_ = lean_string_utf8_byte_size(v_a_1539_);
v___x_1596_ = lean_nat_dec_eq(v___y_1594_, v___x_1595_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1602_; 
v___x_1597_ = lean_unsigned_to_nat(0u);
v___x_1598_ = lean_string_utf8_next_fast(v_a_1539_, v___y_1594_);
v___x_1599_ = lean_string_utf8_extract_fast(v_a_1539_, v___x_1597_, v___y_1594_);
lean_dec(v___y_1594_);
v___x_1600_ = lean_string_utf8_extract_fast(v_a_1539_, v___x_1598_, v___x_1595_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set_tag(v___x_1541_, 1);
lean_ctor_set(v___x_1541_, 0, v___x_1600_);
v___x_1602_ = v___x_1541_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
v_fst_1544_ = v___x_1599_;
v_snd_1545_ = v___x_1602_;
goto v___jp_1543_;
}
}
else
{
lean_object* v___x_1604_; 
lean_dec(v___y_1594_);
lean_del_object(v___x_1541_);
v___x_1604_ = lean_box(0);
lean_inc(v_a_1539_);
v_fst_1544_ = v_a_1539_;
v_snd_1545_ = v___x_1604_;
goto v___jp_1543_;
}
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
lean_dec_ref(v_opts_934_);
v_a_1612_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1612_);
lean_dec_ref_known(v___x_1538_, 1);
v___x_1616_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1617_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1616_);
lean_dec_ref(v___x_1617_);
goto v___jp_1613_;
v___jp_1613_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = lean_io_error_to_string(v_a_1612_);
v___x_1615_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1614_);
lean_dec_ref(v___x_1615_);
goto v___jp_1016_;
}
}
}
}
else
{
uint8_t v___x_1618_; 
v___x_1618_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__16, &l___private_Lean_Shell_0__Lean_displayHelp___closed__16_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__16);
if (v___x_1618_ == 0)
{
lean_dec(v_optArg_x3f_936_);
lean_dec_ref(v_opts_934_);
goto v___jp_1068_;
}
else
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10));
v___x_1620_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1619_, v_optArg_x3f_936_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1629_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1623_ = v___x_1620_;
v_isShared_1624_ = v_isSharedCheck_1629_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1620_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1629_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1625_; lean_object* v___x_1627_; 
v___x_1625_ = lean_internal_enable_debug(v_a_1621_);
lean_dec(v_a_1621_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 0, v_opts_934_);
v___x_1627_ = v___x_1623_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_opts_934_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
lean_dec_ref(v_opts_934_);
v_a_1630_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1630_);
lean_dec_ref_known(v___x_1620_, 1);
v___x_1634_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1635_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1634_);
lean_dec_ref(v___x_1635_);
goto v___jp_1631_;
v___jp_1631_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = lean_io_error_to_string(v_a_1630_);
v___x_1633_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1632_);
lean_dec_ref(v___x_1633_);
goto v___jp_1102_;
}
}
}
}
}
else
{
lean_object* v_leanOpts_1636_; lean_object* v_forwardedArgs_1637_; uint8_t v_component_1638_; uint8_t v_printPrefix_1639_; uint8_t v_printLibDir_1640_; uint8_t v_useStdin_1641_; uint8_t v_onlyDeps_1642_; uint8_t v_onlySrcDeps_1643_; uint8_t v_depsJson_1644_; lean_object* v_opts_1645_; uint32_t v_trustLevel_1646_; uint32_t v_numThreads_1647_; lean_object* v_rootDir_x3f_1648_; lean_object* v_setupFileName_x3f_1649_; lean_object* v_oleanFileName_x3f_1650_; lean_object* v_ileanFileName_x3f_1651_; lean_object* v_cFileName_x3f_1652_; lean_object* v_bcFileName_x3f_1653_; uint8_t v_jsonOutput_1654_; lean_object* v_errorOnKinds_1655_; uint8_t v_printStats_1656_; uint8_t v_run_1657_; lean_object* v_incrSaveFileName_x3f_1658_; lean_object* v_incrLoadFileName_x3f_1659_; lean_object* v_incrHeaderSaveFileName_x3f_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1670_; 
lean_dec(v_optArg_x3f_936_);
v_leanOpts_1636_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_1637_ = lean_ctor_get(v_opts_934_, 1);
v_component_1638_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_1639_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_1640_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_1641_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_1642_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1643_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_1644_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_1645_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_1646_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_1647_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1648_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_1649_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_1650_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_1651_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_1652_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_1653_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_1654_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_1655_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_1656_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_1657_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1658_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_1659_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_1660_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1662_ = v_opts_934_;
v_isShared_1663_ = v_isSharedCheck_1670_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1660_);
lean_inc(v_incrLoadFileName_x3f_1659_);
lean_inc(v_incrSaveFileName_x3f_1658_);
lean_inc(v_errorOnKinds_1655_);
lean_inc(v_bcFileName_x3f_1653_);
lean_inc(v_cFileName_x3f_1652_);
lean_inc(v_ileanFileName_x3f_1651_);
lean_inc(v_oleanFileName_x3f_1650_);
lean_inc(v_setupFileName_x3f_1649_);
lean_inc(v_rootDir_x3f_1648_);
lean_inc(v_opts_1645_);
lean_inc(v_forwardedArgs_1637_);
lean_inc(v_leanOpts_1636_);
lean_dec(v_opts_934_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1670_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1667_; 
v___x_1664_ = l_Lean_profiler;
v___x_1665_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_1636_, v___x_1664_, v___x_1215_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v___x_1665_);
v___x_1667_ = v___x_1662_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1665_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_forwardedArgs_1637_);
lean_ctor_set(v_reuseFailAlloc_1669_, 2, v_opts_1645_);
lean_ctor_set(v_reuseFailAlloc_1669_, 3, v_rootDir_x3f_1648_);
lean_ctor_set(v_reuseFailAlloc_1669_, 4, v_setupFileName_x3f_1649_);
lean_ctor_set(v_reuseFailAlloc_1669_, 5, v_oleanFileName_x3f_1650_);
lean_ctor_set(v_reuseFailAlloc_1669_, 6, v_ileanFileName_x3f_1651_);
lean_ctor_set(v_reuseFailAlloc_1669_, 7, v_cFileName_x3f_1652_);
lean_ctor_set(v_reuseFailAlloc_1669_, 8, v_bcFileName_x3f_1653_);
lean_ctor_set(v_reuseFailAlloc_1669_, 9, v_errorOnKinds_1655_);
lean_ctor_set(v_reuseFailAlloc_1669_, 10, v_incrSaveFileName_x3f_1658_);
lean_ctor_set(v_reuseFailAlloc_1669_, 11, v_incrLoadFileName_x3f_1659_);
lean_ctor_set(v_reuseFailAlloc_1669_, 12, v_incrHeaderSaveFileName_x3f_1660_);
lean_ctor_set_uint8(v_reuseFailAlloc_1669_, sizeof(void*)*13 + 8, v_component_1638_);
lean_ctor_set_uint8(v_reuseFailAlloc_1669_, sizeof(void*)*13 + 9, v_printPrefix_1639_);
lean_ctor_set_uint8(v_reuseFailAlloc_1669_, sizeof(void*)*13 + 10, v_printLibDir_1640_);
lean_ctor_set_uint8(v_reuseFailAlloc_1669_, sizeof(void*)*13 + 11, v_useStdin_1641_);
lean_ctor_set_uint8(v_reuseFailAlloc_1669_, sizeof(void*)*13 + 12, v_onlyDeps_1642_);
lean_ctor_set_uint8(v_reuseFailAlloc_1669_, sizeof(void*)*13 + 13, v_onlySrcDeps_1643_);
lean_ctor_set_uint8(v_reuseFailAlloc_1669_, sizeof(void*)*13 + 14, v_depsJson_1644_);
lean_ctor_set_uint32(v_reuseFailAlloc_1669_, sizeof(void*)*13, v_trustLevel_1646_);
lean_ctor_set_uint32(v_reuseFailAlloc_1669_, sizeof(void*)*13 + 4, v_numThreads_1647_);
lean_ctor_set_uint8(v_reuseFailAlloc_1669_, sizeof(void*)*13 + 15, v_jsonOutput_1654_);
lean_ctor_set_uint8(v_reuseFailAlloc_1669_, sizeof(void*)*13 + 16, v_printStats_1656_);
lean_ctor_set_uint8(v_reuseFailAlloc_1669_, sizeof(void*)*13 + 17, v_run_1657_);
v___x_1667_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
lean_object* v___x_1668_; 
v___x_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
return v___x_1668_;
}
}
}
}
else
{
lean_object* v_leanOpts_1671_; lean_object* v_forwardedArgs_1672_; uint8_t v_printPrefix_1673_; uint8_t v_printLibDir_1674_; uint8_t v_useStdin_1675_; uint8_t v_onlyDeps_1676_; uint8_t v_onlySrcDeps_1677_; uint8_t v_depsJson_1678_; lean_object* v_opts_1679_; uint32_t v_trustLevel_1680_; uint32_t v_numThreads_1681_; lean_object* v_rootDir_x3f_1682_; lean_object* v_setupFileName_x3f_1683_; lean_object* v_oleanFileName_x3f_1684_; lean_object* v_ileanFileName_x3f_1685_; lean_object* v_cFileName_x3f_1686_; lean_object* v_bcFileName_x3f_1687_; uint8_t v_jsonOutput_1688_; lean_object* v_errorOnKinds_1689_; uint8_t v_printStats_1690_; uint8_t v_run_1691_; lean_object* v_incrSaveFileName_x3f_1692_; lean_object* v_incrLoadFileName_x3f_1693_; lean_object* v_incrHeaderSaveFileName_x3f_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1703_; 
lean_dec(v_optArg_x3f_936_);
v_leanOpts_1671_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_1672_ = lean_ctor_get(v_opts_934_, 1);
v_printPrefix_1673_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_1674_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_1675_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_1676_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1677_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_1678_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_1679_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_1680_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_1681_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1682_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_1683_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_1684_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_1685_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_1686_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_1687_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_1688_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_1689_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_1690_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_1691_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1692_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_1693_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_1694_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1696_ = v_opts_934_;
v_isShared_1697_ = v_isSharedCheck_1703_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1694_);
lean_inc(v_incrLoadFileName_x3f_1693_);
lean_inc(v_incrSaveFileName_x3f_1692_);
lean_inc(v_errorOnKinds_1689_);
lean_inc(v_bcFileName_x3f_1687_);
lean_inc(v_cFileName_x3f_1686_);
lean_inc(v_ileanFileName_x3f_1685_);
lean_inc(v_oleanFileName_x3f_1684_);
lean_inc(v_setupFileName_x3f_1683_);
lean_inc(v_rootDir_x3f_1682_);
lean_inc(v_opts_1679_);
lean_inc(v_forwardedArgs_1672_);
lean_inc(v_leanOpts_1671_);
lean_dec(v_opts_934_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1703_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
uint8_t v___x_1698_; lean_object* v___x_1700_; 
v___x_1698_ = 2;
if (v_isShared_1697_ == 0)
{
v___x_1700_ = v___x_1696_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_leanOpts_1671_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_forwardedArgs_1672_);
lean_ctor_set(v_reuseFailAlloc_1702_, 2, v_opts_1679_);
lean_ctor_set(v_reuseFailAlloc_1702_, 3, v_rootDir_x3f_1682_);
lean_ctor_set(v_reuseFailAlloc_1702_, 4, v_setupFileName_x3f_1683_);
lean_ctor_set(v_reuseFailAlloc_1702_, 5, v_oleanFileName_x3f_1684_);
lean_ctor_set(v_reuseFailAlloc_1702_, 6, v_ileanFileName_x3f_1685_);
lean_ctor_set(v_reuseFailAlloc_1702_, 7, v_cFileName_x3f_1686_);
lean_ctor_set(v_reuseFailAlloc_1702_, 8, v_bcFileName_x3f_1687_);
lean_ctor_set(v_reuseFailAlloc_1702_, 9, v_errorOnKinds_1689_);
lean_ctor_set(v_reuseFailAlloc_1702_, 10, v_incrSaveFileName_x3f_1692_);
lean_ctor_set(v_reuseFailAlloc_1702_, 11, v_incrLoadFileName_x3f_1693_);
lean_ctor_set(v_reuseFailAlloc_1702_, 12, v_incrHeaderSaveFileName_x3f_1694_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*13 + 9, v_printPrefix_1673_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*13 + 10, v_printLibDir_1674_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*13 + 11, v_useStdin_1675_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*13 + 12, v_onlyDeps_1676_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*13 + 13, v_onlySrcDeps_1677_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*13 + 14, v_depsJson_1678_);
lean_ctor_set_uint32(v_reuseFailAlloc_1702_, sizeof(void*)*13, v_trustLevel_1680_);
lean_ctor_set_uint32(v_reuseFailAlloc_1702_, sizeof(void*)*13 + 4, v_numThreads_1681_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*13 + 15, v_jsonOutput_1688_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*13 + 16, v_printStats_1690_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*13 + 17, v_run_1691_);
v___x_1700_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
lean_object* v___x_1701_; 
lean_ctor_set_uint8(v___x_1700_, sizeof(void*)*13 + 8, v___x_1698_);
v___x_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1700_);
return v___x_1701_;
}
}
}
}
else
{
lean_object* v_leanOpts_1704_; lean_object* v_forwardedArgs_1705_; uint8_t v_printPrefix_1706_; uint8_t v_printLibDir_1707_; uint8_t v_useStdin_1708_; uint8_t v_onlyDeps_1709_; uint8_t v_onlySrcDeps_1710_; uint8_t v_depsJson_1711_; lean_object* v_opts_1712_; uint32_t v_trustLevel_1713_; uint32_t v_numThreads_1714_; lean_object* v_rootDir_x3f_1715_; lean_object* v_setupFileName_x3f_1716_; lean_object* v_oleanFileName_x3f_1717_; lean_object* v_ileanFileName_x3f_1718_; lean_object* v_cFileName_x3f_1719_; lean_object* v_bcFileName_x3f_1720_; uint8_t v_jsonOutput_1721_; lean_object* v_errorOnKinds_1722_; uint8_t v_printStats_1723_; uint8_t v_run_1724_; lean_object* v_incrSaveFileName_x3f_1725_; lean_object* v_incrLoadFileName_x3f_1726_; lean_object* v_incrHeaderSaveFileName_x3f_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1736_; 
lean_dec(v_optArg_x3f_936_);
v_leanOpts_1704_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_1705_ = lean_ctor_get(v_opts_934_, 1);
v_printPrefix_1706_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_1707_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_1708_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_1709_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1710_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_1711_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_1712_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_1713_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_1714_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1715_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_1716_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_1717_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_1718_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_1719_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_1720_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_1721_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_1722_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_1723_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_1724_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1725_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_1726_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_1727_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1729_ = v_opts_934_;
v_isShared_1730_ = v_isSharedCheck_1736_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1727_);
lean_inc(v_incrLoadFileName_x3f_1726_);
lean_inc(v_incrSaveFileName_x3f_1725_);
lean_inc(v_errorOnKinds_1722_);
lean_inc(v_bcFileName_x3f_1720_);
lean_inc(v_cFileName_x3f_1719_);
lean_inc(v_ileanFileName_x3f_1718_);
lean_inc(v_oleanFileName_x3f_1717_);
lean_inc(v_setupFileName_x3f_1716_);
lean_inc(v_rootDir_x3f_1715_);
lean_inc(v_opts_1712_);
lean_inc(v_forwardedArgs_1705_);
lean_inc(v_leanOpts_1704_);
lean_dec(v_opts_934_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1736_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
uint8_t v___x_1731_; lean_object* v___x_1733_; 
v___x_1731_ = 1;
if (v_isShared_1730_ == 0)
{
v___x_1733_ = v___x_1729_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_leanOpts_1704_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_forwardedArgs_1705_);
lean_ctor_set(v_reuseFailAlloc_1735_, 2, v_opts_1712_);
lean_ctor_set(v_reuseFailAlloc_1735_, 3, v_rootDir_x3f_1715_);
lean_ctor_set(v_reuseFailAlloc_1735_, 4, v_setupFileName_x3f_1716_);
lean_ctor_set(v_reuseFailAlloc_1735_, 5, v_oleanFileName_x3f_1717_);
lean_ctor_set(v_reuseFailAlloc_1735_, 6, v_ileanFileName_x3f_1718_);
lean_ctor_set(v_reuseFailAlloc_1735_, 7, v_cFileName_x3f_1719_);
lean_ctor_set(v_reuseFailAlloc_1735_, 8, v_bcFileName_x3f_1720_);
lean_ctor_set(v_reuseFailAlloc_1735_, 9, v_errorOnKinds_1722_);
lean_ctor_set(v_reuseFailAlloc_1735_, 10, v_incrSaveFileName_x3f_1725_);
lean_ctor_set(v_reuseFailAlloc_1735_, 11, v_incrLoadFileName_x3f_1726_);
lean_ctor_set(v_reuseFailAlloc_1735_, 12, v_incrHeaderSaveFileName_x3f_1727_);
lean_ctor_set_uint8(v_reuseFailAlloc_1735_, sizeof(void*)*13 + 9, v_printPrefix_1706_);
lean_ctor_set_uint8(v_reuseFailAlloc_1735_, sizeof(void*)*13 + 10, v_printLibDir_1707_);
lean_ctor_set_uint8(v_reuseFailAlloc_1735_, sizeof(void*)*13 + 11, v_useStdin_1708_);
lean_ctor_set_uint8(v_reuseFailAlloc_1735_, sizeof(void*)*13 + 12, v_onlyDeps_1709_);
lean_ctor_set_uint8(v_reuseFailAlloc_1735_, sizeof(void*)*13 + 13, v_onlySrcDeps_1710_);
lean_ctor_set_uint8(v_reuseFailAlloc_1735_, sizeof(void*)*13 + 14, v_depsJson_1711_);
lean_ctor_set_uint32(v_reuseFailAlloc_1735_, sizeof(void*)*13, v_trustLevel_1713_);
lean_ctor_set_uint32(v_reuseFailAlloc_1735_, sizeof(void*)*13 + 4, v_numThreads_1714_);
lean_ctor_set_uint8(v_reuseFailAlloc_1735_, sizeof(void*)*13 + 15, v_jsonOutput_1721_);
lean_ctor_set_uint8(v_reuseFailAlloc_1735_, sizeof(void*)*13 + 16, v_printStats_1723_);
lean_ctor_set_uint8(v_reuseFailAlloc_1735_, sizeof(void*)*13 + 17, v_run_1724_);
v___x_1733_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___x_1734_; 
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*13 + 8, v___x_1731_);
v___x_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
return v___x_1734_;
}
}
}
}
else
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11));
v___x_1738_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1737_, v_optArg_x3f_936_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v_leanOpts_1740_; lean_object* v_forwardedArgs_1741_; uint8_t v_component_1742_; uint8_t v_printPrefix_1743_; uint8_t v_printLibDir_1744_; uint8_t v_useStdin_1745_; uint8_t v_onlyDeps_1746_; uint8_t v_onlySrcDeps_1747_; uint8_t v_depsJson_1748_; lean_object* v_opts_1749_; uint32_t v_trustLevel_1750_; uint32_t v_numThreads_1751_; lean_object* v_rootDir_x3f_1752_; lean_object* v_setupFileName_x3f_1753_; lean_object* v_oleanFileName_x3f_1754_; lean_object* v_ileanFileName_x3f_1755_; lean_object* v_cFileName_x3f_1756_; lean_object* v_bcFileName_x3f_1757_; uint8_t v_jsonOutput_1758_; lean_object* v_errorOnKinds_1759_; uint8_t v_printStats_1760_; uint8_t v_run_1761_; lean_object* v_incrSaveFileName_x3f_1762_; lean_object* v_incrLoadFileName_x3f_1763_; lean_object* v_incrHeaderSaveFileName_x3f_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1789_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref_known(v___x_1738_, 1);
v_leanOpts_1740_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_1741_ = lean_ctor_get(v_opts_934_, 1);
v_component_1742_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_1743_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_1744_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_1745_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_1746_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1747_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_1748_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_1749_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_1750_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_1751_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1752_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_1753_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_1754_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_1755_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_1756_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_1757_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_1758_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_1759_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_1760_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_1761_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1762_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_1763_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_1764_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1766_ = v_opts_934_;
v_isShared_1767_ = v_isSharedCheck_1789_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1764_);
lean_inc(v_incrLoadFileName_x3f_1763_);
lean_inc(v_incrSaveFileName_x3f_1762_);
lean_inc(v_errorOnKinds_1759_);
lean_inc(v_bcFileName_x3f_1757_);
lean_inc(v_cFileName_x3f_1756_);
lean_inc(v_ileanFileName_x3f_1755_);
lean_inc(v_oleanFileName_x3f_1754_);
lean_inc(v_setupFileName_x3f_1753_);
lean_inc(v_rootDir_x3f_1752_);
lean_inc(v_opts_1749_);
lean_inc(v_forwardedArgs_1741_);
lean_inc(v_leanOpts_1740_);
lean_dec(v_opts_934_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1789_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1768_; 
lean_inc(v_a_1739_);
v___x_1768_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_leanOpts_1740_, v_a_1739_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1782_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1771_ = v___x_1768_;
v_isShared_1772_ = v_isSharedCheck_1782_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1768_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1782_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1773_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12));
v___x_1774_ = lean_string_append(v___x_1773_, v_a_1739_);
lean_dec(v_a_1739_);
v___x_1775_ = lean_array_push(v_forwardedArgs_1741_, v___x_1774_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 1, v___x_1775_);
lean_ctor_set(v___x_1766_, 0, v_a_1769_);
v___x_1777_ = v___x_1766_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1769_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v___x_1775_);
lean_ctor_set(v_reuseFailAlloc_1781_, 2, v_opts_1749_);
lean_ctor_set(v_reuseFailAlloc_1781_, 3, v_rootDir_x3f_1752_);
lean_ctor_set(v_reuseFailAlloc_1781_, 4, v_setupFileName_x3f_1753_);
lean_ctor_set(v_reuseFailAlloc_1781_, 5, v_oleanFileName_x3f_1754_);
lean_ctor_set(v_reuseFailAlloc_1781_, 6, v_ileanFileName_x3f_1755_);
lean_ctor_set(v_reuseFailAlloc_1781_, 7, v_cFileName_x3f_1756_);
lean_ctor_set(v_reuseFailAlloc_1781_, 8, v_bcFileName_x3f_1757_);
lean_ctor_set(v_reuseFailAlloc_1781_, 9, v_errorOnKinds_1759_);
lean_ctor_set(v_reuseFailAlloc_1781_, 10, v_incrSaveFileName_x3f_1762_);
lean_ctor_set(v_reuseFailAlloc_1781_, 11, v_incrLoadFileName_x3f_1763_);
lean_ctor_set(v_reuseFailAlloc_1781_, 12, v_incrHeaderSaveFileName_x3f_1764_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, sizeof(void*)*13 + 8, v_component_1742_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, sizeof(void*)*13 + 9, v_printPrefix_1743_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, sizeof(void*)*13 + 10, v_printLibDir_1744_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, sizeof(void*)*13 + 11, v_useStdin_1745_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, sizeof(void*)*13 + 12, v_onlyDeps_1746_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, sizeof(void*)*13 + 13, v_onlySrcDeps_1747_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, sizeof(void*)*13 + 14, v_depsJson_1748_);
lean_ctor_set_uint32(v_reuseFailAlloc_1781_, sizeof(void*)*13, v_trustLevel_1750_);
lean_ctor_set_uint32(v_reuseFailAlloc_1781_, sizeof(void*)*13 + 4, v_numThreads_1751_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, sizeof(void*)*13 + 15, v_jsonOutput_1758_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, sizeof(void*)*13 + 16, v_printStats_1760_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, sizeof(void*)*13 + 17, v_run_1761_);
v___x_1777_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1779_; 
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1777_);
v___x_1779_ = v___x_1771_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
lean_del_object(v___x_1766_);
lean_dec(v_incrHeaderSaveFileName_x3f_1764_);
lean_dec(v_incrLoadFileName_x3f_1763_);
lean_dec(v_incrSaveFileName_x3f_1762_);
lean_dec_ref(v_errorOnKinds_1759_);
lean_dec(v_bcFileName_x3f_1757_);
lean_dec(v_cFileName_x3f_1756_);
lean_dec(v_ileanFileName_x3f_1755_);
lean_dec(v_oleanFileName_x3f_1754_);
lean_dec(v_setupFileName_x3f_1753_);
lean_dec(v_rootDir_x3f_1752_);
lean_dec_ref(v_opts_1749_);
lean_dec_ref(v_forwardedArgs_1741_);
lean_dec(v_a_1739_);
v_a_1783_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___x_1768_, 1);
v___x_1787_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1788_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1787_);
lean_dec_ref(v___x_1788_);
goto v___jp_1784_;
v___jp_1784_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = lean_io_error_to_string(v_a_1783_);
v___x_1786_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1785_);
lean_dec_ref(v___x_1786_);
goto v___jp_1010_;
}
}
}
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
lean_dec_ref(v_opts_934_);
v_a_1790_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1790_);
lean_dec_ref_known(v___x_1738_, 1);
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
goto v___jp_1108_;
}
}
}
}
else
{
lean_object* v_leanOpts_1796_; lean_object* v_forwardedArgs_1797_; uint8_t v_component_1798_; uint8_t v_printPrefix_1799_; uint8_t v_useStdin_1800_; uint8_t v_onlyDeps_1801_; uint8_t v_onlySrcDeps_1802_; uint8_t v_depsJson_1803_; lean_object* v_opts_1804_; uint32_t v_trustLevel_1805_; uint32_t v_numThreads_1806_; lean_object* v_rootDir_x3f_1807_; lean_object* v_setupFileName_x3f_1808_; lean_object* v_oleanFileName_x3f_1809_; lean_object* v_ileanFileName_x3f_1810_; lean_object* v_cFileName_x3f_1811_; lean_object* v_bcFileName_x3f_1812_; uint8_t v_jsonOutput_1813_; lean_object* v_errorOnKinds_1814_; uint8_t v_printStats_1815_; uint8_t v_run_1816_; lean_object* v_incrSaveFileName_x3f_1817_; lean_object* v_incrLoadFileName_x3f_1818_; lean_object* v_incrHeaderSaveFileName_x3f_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1827_; 
lean_dec(v_optArg_x3f_936_);
v_leanOpts_1796_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_1797_ = lean_ctor_get(v_opts_934_, 1);
v_component_1798_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_1799_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_useStdin_1800_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_1801_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1802_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_1803_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_1804_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_1805_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_1806_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1807_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_1808_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_1809_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_1810_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_1811_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_1812_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_1813_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_1814_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_1815_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_1816_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1817_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_1818_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_1819_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1821_ = v_opts_934_;
v_isShared_1822_ = v_isSharedCheck_1827_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1819_);
lean_inc(v_incrLoadFileName_x3f_1818_);
lean_inc(v_incrSaveFileName_x3f_1817_);
lean_inc(v_errorOnKinds_1814_);
lean_inc(v_bcFileName_x3f_1812_);
lean_inc(v_cFileName_x3f_1811_);
lean_inc(v_ileanFileName_x3f_1810_);
lean_inc(v_oleanFileName_x3f_1809_);
lean_inc(v_setupFileName_x3f_1808_);
lean_inc(v_rootDir_x3f_1807_);
lean_inc(v_opts_1804_);
lean_inc(v_forwardedArgs_1797_);
lean_inc(v_leanOpts_1796_);
lean_dec(v_opts_934_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1827_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_leanOpts_1796_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_forwardedArgs_1797_);
lean_ctor_set(v_reuseFailAlloc_1826_, 2, v_opts_1804_);
lean_ctor_set(v_reuseFailAlloc_1826_, 3, v_rootDir_x3f_1807_);
lean_ctor_set(v_reuseFailAlloc_1826_, 4, v_setupFileName_x3f_1808_);
lean_ctor_set(v_reuseFailAlloc_1826_, 5, v_oleanFileName_x3f_1809_);
lean_ctor_set(v_reuseFailAlloc_1826_, 6, v_ileanFileName_x3f_1810_);
lean_ctor_set(v_reuseFailAlloc_1826_, 7, v_cFileName_x3f_1811_);
lean_ctor_set(v_reuseFailAlloc_1826_, 8, v_bcFileName_x3f_1812_);
lean_ctor_set(v_reuseFailAlloc_1826_, 9, v_errorOnKinds_1814_);
lean_ctor_set(v_reuseFailAlloc_1826_, 10, v_incrSaveFileName_x3f_1817_);
lean_ctor_set(v_reuseFailAlloc_1826_, 11, v_incrLoadFileName_x3f_1818_);
lean_ctor_set(v_reuseFailAlloc_1826_, 12, v_incrHeaderSaveFileName_x3f_1819_);
lean_ctor_set_uint8(v_reuseFailAlloc_1826_, sizeof(void*)*13 + 8, v_component_1798_);
lean_ctor_set_uint8(v_reuseFailAlloc_1826_, sizeof(void*)*13 + 9, v_printPrefix_1799_);
lean_ctor_set_uint8(v_reuseFailAlloc_1826_, sizeof(void*)*13 + 11, v_useStdin_1800_);
lean_ctor_set_uint8(v_reuseFailAlloc_1826_, sizeof(void*)*13 + 12, v_onlyDeps_1801_);
lean_ctor_set_uint8(v_reuseFailAlloc_1826_, sizeof(void*)*13 + 13, v_onlySrcDeps_1802_);
lean_ctor_set_uint8(v_reuseFailAlloc_1826_, sizeof(void*)*13 + 14, v_depsJson_1803_);
lean_ctor_set_uint32(v_reuseFailAlloc_1826_, sizeof(void*)*13, v_trustLevel_1805_);
lean_ctor_set_uint32(v_reuseFailAlloc_1826_, sizeof(void*)*13 + 4, v_numThreads_1806_);
lean_ctor_set_uint8(v_reuseFailAlloc_1826_, sizeof(void*)*13 + 15, v_jsonOutput_1813_);
lean_ctor_set_uint8(v_reuseFailAlloc_1826_, sizeof(void*)*13 + 16, v_printStats_1815_);
lean_ctor_set_uint8(v_reuseFailAlloc_1826_, sizeof(void*)*13 + 17, v_run_1816_);
v___x_1824_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1825_; 
lean_ctor_set_uint8(v___x_1824_, sizeof(void*)*13 + 10, v___x_1207_);
v___x_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
return v___x_1825_;
}
}
}
}
else
{
lean_object* v_leanOpts_1828_; lean_object* v_forwardedArgs_1829_; uint8_t v_component_1830_; uint8_t v_printLibDir_1831_; uint8_t v_useStdin_1832_; uint8_t v_onlyDeps_1833_; uint8_t v_onlySrcDeps_1834_; uint8_t v_depsJson_1835_; lean_object* v_opts_1836_; uint32_t v_trustLevel_1837_; uint32_t v_numThreads_1838_; lean_object* v_rootDir_x3f_1839_; lean_object* v_setupFileName_x3f_1840_; lean_object* v_oleanFileName_x3f_1841_; lean_object* v_ileanFileName_x3f_1842_; lean_object* v_cFileName_x3f_1843_; lean_object* v_bcFileName_x3f_1844_; uint8_t v_jsonOutput_1845_; lean_object* v_errorOnKinds_1846_; uint8_t v_printStats_1847_; uint8_t v_run_1848_; lean_object* v_incrSaveFileName_x3f_1849_; lean_object* v_incrLoadFileName_x3f_1850_; lean_object* v_incrHeaderSaveFileName_x3f_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1859_; 
lean_dec(v_optArg_x3f_936_);
v_leanOpts_1828_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_1829_ = lean_ctor_get(v_opts_934_, 1);
v_component_1830_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printLibDir_1831_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_1832_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_1833_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1834_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_1835_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_1836_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_1837_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_1838_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1839_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_1840_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_1841_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_1842_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_1843_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_1844_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_1845_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_1846_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_1847_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_1848_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1849_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_1850_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_1851_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1853_ = v_opts_934_;
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1851_);
lean_inc(v_incrLoadFileName_x3f_1850_);
lean_inc(v_incrSaveFileName_x3f_1849_);
lean_inc(v_errorOnKinds_1846_);
lean_inc(v_bcFileName_x3f_1844_);
lean_inc(v_cFileName_x3f_1843_);
lean_inc(v_ileanFileName_x3f_1842_);
lean_inc(v_oleanFileName_x3f_1841_);
lean_inc(v_setupFileName_x3f_1840_);
lean_inc(v_rootDir_x3f_1839_);
lean_inc(v_opts_1836_);
lean_inc(v_forwardedArgs_1829_);
lean_inc(v_leanOpts_1828_);
lean_dec(v_opts_934_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_leanOpts_1828_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_forwardedArgs_1829_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v_opts_1836_);
lean_ctor_set(v_reuseFailAlloc_1858_, 3, v_rootDir_x3f_1839_);
lean_ctor_set(v_reuseFailAlloc_1858_, 4, v_setupFileName_x3f_1840_);
lean_ctor_set(v_reuseFailAlloc_1858_, 5, v_oleanFileName_x3f_1841_);
lean_ctor_set(v_reuseFailAlloc_1858_, 6, v_ileanFileName_x3f_1842_);
lean_ctor_set(v_reuseFailAlloc_1858_, 7, v_cFileName_x3f_1843_);
lean_ctor_set(v_reuseFailAlloc_1858_, 8, v_bcFileName_x3f_1844_);
lean_ctor_set(v_reuseFailAlloc_1858_, 9, v_errorOnKinds_1846_);
lean_ctor_set(v_reuseFailAlloc_1858_, 10, v_incrSaveFileName_x3f_1849_);
lean_ctor_set(v_reuseFailAlloc_1858_, 11, v_incrLoadFileName_x3f_1850_);
lean_ctor_set(v_reuseFailAlloc_1858_, 12, v_incrHeaderSaveFileName_x3f_1851_);
lean_ctor_set_uint8(v_reuseFailAlloc_1858_, sizeof(void*)*13 + 8, v_component_1830_);
lean_ctor_set_uint8(v_reuseFailAlloc_1858_, sizeof(void*)*13 + 10, v_printLibDir_1831_);
lean_ctor_set_uint8(v_reuseFailAlloc_1858_, sizeof(void*)*13 + 11, v_useStdin_1832_);
lean_ctor_set_uint8(v_reuseFailAlloc_1858_, sizeof(void*)*13 + 12, v_onlyDeps_1833_);
lean_ctor_set_uint8(v_reuseFailAlloc_1858_, sizeof(void*)*13 + 13, v_onlySrcDeps_1834_);
lean_ctor_set_uint8(v_reuseFailAlloc_1858_, sizeof(void*)*13 + 14, v_depsJson_1835_);
lean_ctor_set_uint32(v_reuseFailAlloc_1858_, sizeof(void*)*13, v_trustLevel_1837_);
lean_ctor_set_uint32(v_reuseFailAlloc_1858_, sizeof(void*)*13 + 4, v_numThreads_1838_);
lean_ctor_set_uint8(v_reuseFailAlloc_1858_, sizeof(void*)*13 + 15, v_jsonOutput_1845_);
lean_ctor_set_uint8(v_reuseFailAlloc_1858_, sizeof(void*)*13 + 16, v_printStats_1847_);
lean_ctor_set_uint8(v_reuseFailAlloc_1858_, sizeof(void*)*13 + 17, v_run_1848_);
v___x_1856_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; 
lean_ctor_set_uint8(v___x_1856_, sizeof(void*)*13 + 9, v___x_1205_);
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
return v___x_1857_;
}
}
}
}
else
{
lean_object* v_leanOpts_1860_; lean_object* v_forwardedArgs_1861_; uint8_t v_component_1862_; uint8_t v_printPrefix_1863_; uint8_t v_printLibDir_1864_; uint8_t v_useStdin_1865_; uint8_t v_onlyDeps_1866_; uint8_t v_onlySrcDeps_1867_; uint8_t v_depsJson_1868_; lean_object* v_opts_1869_; uint32_t v_trustLevel_1870_; uint32_t v_numThreads_1871_; lean_object* v_rootDir_x3f_1872_; lean_object* v_setupFileName_x3f_1873_; lean_object* v_oleanFileName_x3f_1874_; lean_object* v_ileanFileName_x3f_1875_; lean_object* v_cFileName_x3f_1876_; lean_object* v_bcFileName_x3f_1877_; uint8_t v_jsonOutput_1878_; lean_object* v_errorOnKinds_1879_; uint8_t v_run_1880_; lean_object* v_incrSaveFileName_x3f_1881_; lean_object* v_incrLoadFileName_x3f_1882_; lean_object* v_incrHeaderSaveFileName_x3f_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1891_; 
lean_dec(v_optArg_x3f_936_);
v_leanOpts_1860_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_1861_ = lean_ctor_get(v_opts_934_, 1);
v_component_1862_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_1863_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_1864_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_1865_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_1866_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1867_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_1868_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_1869_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_1870_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_1871_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1872_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_1873_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_1874_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_1875_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_1876_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_1877_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_1878_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_1879_ = lean_ctor_get(v_opts_934_, 9);
v_run_1880_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1881_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_1882_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_1883_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_1891_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1885_ = v_opts_934_;
v_isShared_1886_ = v_isSharedCheck_1891_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1883_);
lean_inc(v_incrLoadFileName_x3f_1882_);
lean_inc(v_incrSaveFileName_x3f_1881_);
lean_inc(v_errorOnKinds_1879_);
lean_inc(v_bcFileName_x3f_1877_);
lean_inc(v_cFileName_x3f_1876_);
lean_inc(v_ileanFileName_x3f_1875_);
lean_inc(v_oleanFileName_x3f_1874_);
lean_inc(v_setupFileName_x3f_1873_);
lean_inc(v_rootDir_x3f_1872_);
lean_inc(v_opts_1869_);
lean_inc(v_forwardedArgs_1861_);
lean_inc(v_leanOpts_1860_);
lean_dec(v_opts_934_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1891_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_leanOpts_1860_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_forwardedArgs_1861_);
lean_ctor_set(v_reuseFailAlloc_1890_, 2, v_opts_1869_);
lean_ctor_set(v_reuseFailAlloc_1890_, 3, v_rootDir_x3f_1872_);
lean_ctor_set(v_reuseFailAlloc_1890_, 4, v_setupFileName_x3f_1873_);
lean_ctor_set(v_reuseFailAlloc_1890_, 5, v_oleanFileName_x3f_1874_);
lean_ctor_set(v_reuseFailAlloc_1890_, 6, v_ileanFileName_x3f_1875_);
lean_ctor_set(v_reuseFailAlloc_1890_, 7, v_cFileName_x3f_1876_);
lean_ctor_set(v_reuseFailAlloc_1890_, 8, v_bcFileName_x3f_1877_);
lean_ctor_set(v_reuseFailAlloc_1890_, 9, v_errorOnKinds_1879_);
lean_ctor_set(v_reuseFailAlloc_1890_, 10, v_incrSaveFileName_x3f_1881_);
lean_ctor_set(v_reuseFailAlloc_1890_, 11, v_incrLoadFileName_x3f_1882_);
lean_ctor_set(v_reuseFailAlloc_1890_, 12, v_incrHeaderSaveFileName_x3f_1883_);
lean_ctor_set_uint8(v_reuseFailAlloc_1890_, sizeof(void*)*13 + 8, v_component_1862_);
lean_ctor_set_uint8(v_reuseFailAlloc_1890_, sizeof(void*)*13 + 9, v_printPrefix_1863_);
lean_ctor_set_uint8(v_reuseFailAlloc_1890_, sizeof(void*)*13 + 10, v_printLibDir_1864_);
lean_ctor_set_uint8(v_reuseFailAlloc_1890_, sizeof(void*)*13 + 11, v_useStdin_1865_);
lean_ctor_set_uint8(v_reuseFailAlloc_1890_, sizeof(void*)*13 + 12, v_onlyDeps_1866_);
lean_ctor_set_uint8(v_reuseFailAlloc_1890_, sizeof(void*)*13 + 13, v_onlySrcDeps_1867_);
lean_ctor_set_uint8(v_reuseFailAlloc_1890_, sizeof(void*)*13 + 14, v_depsJson_1868_);
lean_ctor_set_uint32(v_reuseFailAlloc_1890_, sizeof(void*)*13, v_trustLevel_1870_);
lean_ctor_set_uint32(v_reuseFailAlloc_1890_, sizeof(void*)*13 + 4, v_numThreads_1871_);
lean_ctor_set_uint8(v_reuseFailAlloc_1890_, sizeof(void*)*13 + 15, v_jsonOutput_1878_);
lean_ctor_set_uint8(v_reuseFailAlloc_1890_, sizeof(void*)*13 + 17, v_run_1880_);
v___x_1888_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1889_; 
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*13 + 16, v___x_1203_);
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
return v___x_1889_;
}
}
}
}
else
{
lean_object* v_leanOpts_1892_; lean_object* v_forwardedArgs_1893_; uint8_t v_component_1894_; uint8_t v_printPrefix_1895_; uint8_t v_printLibDir_1896_; uint8_t v_useStdin_1897_; uint8_t v_onlyDeps_1898_; uint8_t v_onlySrcDeps_1899_; uint8_t v_depsJson_1900_; lean_object* v_opts_1901_; uint32_t v_trustLevel_1902_; uint32_t v_numThreads_1903_; lean_object* v_rootDir_x3f_1904_; lean_object* v_setupFileName_x3f_1905_; lean_object* v_oleanFileName_x3f_1906_; lean_object* v_ileanFileName_x3f_1907_; lean_object* v_cFileName_x3f_1908_; lean_object* v_bcFileName_x3f_1909_; lean_object* v_errorOnKinds_1910_; uint8_t v_printStats_1911_; uint8_t v_run_1912_; lean_object* v_incrSaveFileName_x3f_1913_; lean_object* v_incrLoadFileName_x3f_1914_; lean_object* v_incrHeaderSaveFileName_x3f_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1923_; 
lean_dec(v_optArg_x3f_936_);
v_leanOpts_1892_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_1893_ = lean_ctor_get(v_opts_934_, 1);
v_component_1894_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_1895_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_1896_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_1897_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_1898_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1899_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_1900_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_1901_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_1902_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_1903_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1904_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_1905_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_1906_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_1907_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_1908_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_1909_ = lean_ctor_get(v_opts_934_, 8);
v_errorOnKinds_1910_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_1911_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_1912_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1913_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_1914_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_1915_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_1923_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1917_ = v_opts_934_;
v_isShared_1918_ = v_isSharedCheck_1923_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1915_);
lean_inc(v_incrLoadFileName_x3f_1914_);
lean_inc(v_incrSaveFileName_x3f_1913_);
lean_inc(v_errorOnKinds_1910_);
lean_inc(v_bcFileName_x3f_1909_);
lean_inc(v_cFileName_x3f_1908_);
lean_inc(v_ileanFileName_x3f_1907_);
lean_inc(v_oleanFileName_x3f_1906_);
lean_inc(v_setupFileName_x3f_1905_);
lean_inc(v_rootDir_x3f_1904_);
lean_inc(v_opts_1901_);
lean_inc(v_forwardedArgs_1893_);
lean_inc(v_leanOpts_1892_);
lean_dec(v_opts_934_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1923_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_leanOpts_1892_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_forwardedArgs_1893_);
lean_ctor_set(v_reuseFailAlloc_1922_, 2, v_opts_1901_);
lean_ctor_set(v_reuseFailAlloc_1922_, 3, v_rootDir_x3f_1904_);
lean_ctor_set(v_reuseFailAlloc_1922_, 4, v_setupFileName_x3f_1905_);
lean_ctor_set(v_reuseFailAlloc_1922_, 5, v_oleanFileName_x3f_1906_);
lean_ctor_set(v_reuseFailAlloc_1922_, 6, v_ileanFileName_x3f_1907_);
lean_ctor_set(v_reuseFailAlloc_1922_, 7, v_cFileName_x3f_1908_);
lean_ctor_set(v_reuseFailAlloc_1922_, 8, v_bcFileName_x3f_1909_);
lean_ctor_set(v_reuseFailAlloc_1922_, 9, v_errorOnKinds_1910_);
lean_ctor_set(v_reuseFailAlloc_1922_, 10, v_incrSaveFileName_x3f_1913_);
lean_ctor_set(v_reuseFailAlloc_1922_, 11, v_incrLoadFileName_x3f_1914_);
lean_ctor_set(v_reuseFailAlloc_1922_, 12, v_incrHeaderSaveFileName_x3f_1915_);
lean_ctor_set_uint8(v_reuseFailAlloc_1922_, sizeof(void*)*13 + 8, v_component_1894_);
lean_ctor_set_uint8(v_reuseFailAlloc_1922_, sizeof(void*)*13 + 9, v_printPrefix_1895_);
lean_ctor_set_uint8(v_reuseFailAlloc_1922_, sizeof(void*)*13 + 10, v_printLibDir_1896_);
lean_ctor_set_uint8(v_reuseFailAlloc_1922_, sizeof(void*)*13 + 11, v_useStdin_1897_);
lean_ctor_set_uint8(v_reuseFailAlloc_1922_, sizeof(void*)*13 + 12, v_onlyDeps_1898_);
lean_ctor_set_uint8(v_reuseFailAlloc_1922_, sizeof(void*)*13 + 13, v_onlySrcDeps_1899_);
lean_ctor_set_uint8(v_reuseFailAlloc_1922_, sizeof(void*)*13 + 14, v_depsJson_1900_);
lean_ctor_set_uint32(v_reuseFailAlloc_1922_, sizeof(void*)*13, v_trustLevel_1902_);
lean_ctor_set_uint32(v_reuseFailAlloc_1922_, sizeof(void*)*13 + 4, v_numThreads_1903_);
lean_ctor_set_uint8(v_reuseFailAlloc_1922_, sizeof(void*)*13 + 16, v_printStats_1911_);
lean_ctor_set_uint8(v_reuseFailAlloc_1922_, sizeof(void*)*13 + 17, v_run_1912_);
v___x_1920_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
lean_object* v___x_1921_; 
lean_ctor_set_uint8(v___x_1920_, sizeof(void*)*13 + 15, v___x_1201_);
v___x_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
return v___x_1921_;
}
}
}
}
else
{
lean_object* v_leanOpts_1924_; lean_object* v_forwardedArgs_1925_; uint8_t v_component_1926_; uint8_t v_printPrefix_1927_; uint8_t v_printLibDir_1928_; uint8_t v_useStdin_1929_; uint8_t v_onlySrcDeps_1930_; lean_object* v_opts_1931_; uint32_t v_trustLevel_1932_; uint32_t v_numThreads_1933_; lean_object* v_rootDir_x3f_1934_; lean_object* v_setupFileName_x3f_1935_; lean_object* v_oleanFileName_x3f_1936_; lean_object* v_ileanFileName_x3f_1937_; lean_object* v_cFileName_x3f_1938_; lean_object* v_bcFileName_x3f_1939_; uint8_t v_jsonOutput_1940_; lean_object* v_errorOnKinds_1941_; uint8_t v_printStats_1942_; uint8_t v_run_1943_; lean_object* v_incrSaveFileName_x3f_1944_; lean_object* v_incrLoadFileName_x3f_1945_; lean_object* v_incrHeaderSaveFileName_x3f_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1954_; 
lean_dec(v_optArg_x3f_936_);
v_leanOpts_1924_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_1925_ = lean_ctor_get(v_opts_934_, 1);
v_component_1926_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_1927_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_1928_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_1929_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlySrcDeps_1930_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_opts_1931_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_1932_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_1933_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1934_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_1935_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_1936_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_1937_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_1938_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_1939_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_1940_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_1941_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_1942_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_1943_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1944_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_1945_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_1946_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_1954_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1948_ = v_opts_934_;
v_isShared_1949_ = v_isSharedCheck_1954_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1946_);
lean_inc(v_incrLoadFileName_x3f_1945_);
lean_inc(v_incrSaveFileName_x3f_1944_);
lean_inc(v_errorOnKinds_1941_);
lean_inc(v_bcFileName_x3f_1939_);
lean_inc(v_cFileName_x3f_1938_);
lean_inc(v_ileanFileName_x3f_1937_);
lean_inc(v_oleanFileName_x3f_1936_);
lean_inc(v_setupFileName_x3f_1935_);
lean_inc(v_rootDir_x3f_1934_);
lean_inc(v_opts_1931_);
lean_inc(v_forwardedArgs_1925_);
lean_inc(v_leanOpts_1924_);
lean_dec(v_opts_934_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1954_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_leanOpts_1924_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v_forwardedArgs_1925_);
lean_ctor_set(v_reuseFailAlloc_1953_, 2, v_opts_1931_);
lean_ctor_set(v_reuseFailAlloc_1953_, 3, v_rootDir_x3f_1934_);
lean_ctor_set(v_reuseFailAlloc_1953_, 4, v_setupFileName_x3f_1935_);
lean_ctor_set(v_reuseFailAlloc_1953_, 5, v_oleanFileName_x3f_1936_);
lean_ctor_set(v_reuseFailAlloc_1953_, 6, v_ileanFileName_x3f_1937_);
lean_ctor_set(v_reuseFailAlloc_1953_, 7, v_cFileName_x3f_1938_);
lean_ctor_set(v_reuseFailAlloc_1953_, 8, v_bcFileName_x3f_1939_);
lean_ctor_set(v_reuseFailAlloc_1953_, 9, v_errorOnKinds_1941_);
lean_ctor_set(v_reuseFailAlloc_1953_, 10, v_incrSaveFileName_x3f_1944_);
lean_ctor_set(v_reuseFailAlloc_1953_, 11, v_incrLoadFileName_x3f_1945_);
lean_ctor_set(v_reuseFailAlloc_1953_, 12, v_incrHeaderSaveFileName_x3f_1946_);
lean_ctor_set_uint8(v_reuseFailAlloc_1953_, sizeof(void*)*13 + 8, v_component_1926_);
lean_ctor_set_uint8(v_reuseFailAlloc_1953_, sizeof(void*)*13 + 9, v_printPrefix_1927_);
lean_ctor_set_uint8(v_reuseFailAlloc_1953_, sizeof(void*)*13 + 10, v_printLibDir_1928_);
lean_ctor_set_uint8(v_reuseFailAlloc_1953_, sizeof(void*)*13 + 11, v_useStdin_1929_);
lean_ctor_set_uint8(v_reuseFailAlloc_1953_, sizeof(void*)*13 + 13, v_onlySrcDeps_1930_);
lean_ctor_set_uint32(v_reuseFailAlloc_1953_, sizeof(void*)*13, v_trustLevel_1932_);
lean_ctor_set_uint32(v_reuseFailAlloc_1953_, sizeof(void*)*13 + 4, v_numThreads_1933_);
lean_ctor_set_uint8(v_reuseFailAlloc_1953_, sizeof(void*)*13 + 15, v_jsonOutput_1940_);
lean_ctor_set_uint8(v_reuseFailAlloc_1953_, sizeof(void*)*13 + 16, v_printStats_1942_);
lean_ctor_set_uint8(v_reuseFailAlloc_1953_, sizeof(void*)*13 + 17, v_run_1943_);
v___x_1951_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
lean_object* v___x_1952_; 
lean_ctor_set_uint8(v___x_1951_, sizeof(void*)*13 + 12, v___x_1199_);
lean_ctor_set_uint8(v___x_1951_, sizeof(void*)*13 + 14, v___x_1199_);
v___x_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
return v___x_1952_;
}
}
}
}
else
{
lean_object* v_leanOpts_1955_; lean_object* v_forwardedArgs_1956_; uint8_t v_component_1957_; uint8_t v_printPrefix_1958_; uint8_t v_printLibDir_1959_; uint8_t v_useStdin_1960_; uint8_t v_onlyDeps_1961_; uint8_t v_depsJson_1962_; lean_object* v_opts_1963_; uint32_t v_trustLevel_1964_; uint32_t v_numThreads_1965_; lean_object* v_rootDir_x3f_1966_; lean_object* v_setupFileName_x3f_1967_; lean_object* v_oleanFileName_x3f_1968_; lean_object* v_ileanFileName_x3f_1969_; lean_object* v_cFileName_x3f_1970_; lean_object* v_bcFileName_x3f_1971_; uint8_t v_jsonOutput_1972_; lean_object* v_errorOnKinds_1973_; uint8_t v_printStats_1974_; uint8_t v_run_1975_; lean_object* v_incrSaveFileName_x3f_1976_; lean_object* v_incrLoadFileName_x3f_1977_; lean_object* v_incrHeaderSaveFileName_x3f_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1986_; 
lean_dec(v_optArg_x3f_936_);
v_leanOpts_1955_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_1956_ = lean_ctor_get(v_opts_934_, 1);
v_component_1957_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_1958_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_1959_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_1960_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_1961_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_depsJson_1962_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_1963_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_1964_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_1965_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1966_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_1967_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_1968_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_1969_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_1970_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_1971_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_1972_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_1973_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_1974_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_1975_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1976_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_1977_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_1978_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1980_ = v_opts_934_;
v_isShared_1981_ = v_isSharedCheck_1986_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1978_);
lean_inc(v_incrLoadFileName_x3f_1977_);
lean_inc(v_incrSaveFileName_x3f_1976_);
lean_inc(v_errorOnKinds_1973_);
lean_inc(v_bcFileName_x3f_1971_);
lean_inc(v_cFileName_x3f_1970_);
lean_inc(v_ileanFileName_x3f_1969_);
lean_inc(v_oleanFileName_x3f_1968_);
lean_inc(v_setupFileName_x3f_1967_);
lean_inc(v_rootDir_x3f_1966_);
lean_inc(v_opts_1963_);
lean_inc(v_forwardedArgs_1956_);
lean_inc(v_leanOpts_1955_);
lean_dec(v_opts_934_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1986_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_leanOpts_1955_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v_forwardedArgs_1956_);
lean_ctor_set(v_reuseFailAlloc_1985_, 2, v_opts_1963_);
lean_ctor_set(v_reuseFailAlloc_1985_, 3, v_rootDir_x3f_1966_);
lean_ctor_set(v_reuseFailAlloc_1985_, 4, v_setupFileName_x3f_1967_);
lean_ctor_set(v_reuseFailAlloc_1985_, 5, v_oleanFileName_x3f_1968_);
lean_ctor_set(v_reuseFailAlloc_1985_, 6, v_ileanFileName_x3f_1969_);
lean_ctor_set(v_reuseFailAlloc_1985_, 7, v_cFileName_x3f_1970_);
lean_ctor_set(v_reuseFailAlloc_1985_, 8, v_bcFileName_x3f_1971_);
lean_ctor_set(v_reuseFailAlloc_1985_, 9, v_errorOnKinds_1973_);
lean_ctor_set(v_reuseFailAlloc_1985_, 10, v_incrSaveFileName_x3f_1976_);
lean_ctor_set(v_reuseFailAlloc_1985_, 11, v_incrLoadFileName_x3f_1977_);
lean_ctor_set(v_reuseFailAlloc_1985_, 12, v_incrHeaderSaveFileName_x3f_1978_);
lean_ctor_set_uint8(v_reuseFailAlloc_1985_, sizeof(void*)*13 + 8, v_component_1957_);
lean_ctor_set_uint8(v_reuseFailAlloc_1985_, sizeof(void*)*13 + 9, v_printPrefix_1958_);
lean_ctor_set_uint8(v_reuseFailAlloc_1985_, sizeof(void*)*13 + 10, v_printLibDir_1959_);
lean_ctor_set_uint8(v_reuseFailAlloc_1985_, sizeof(void*)*13 + 11, v_useStdin_1960_);
lean_ctor_set_uint8(v_reuseFailAlloc_1985_, sizeof(void*)*13 + 12, v_onlyDeps_1961_);
lean_ctor_set_uint8(v_reuseFailAlloc_1985_, sizeof(void*)*13 + 14, v_depsJson_1962_);
lean_ctor_set_uint32(v_reuseFailAlloc_1985_, sizeof(void*)*13, v_trustLevel_1964_);
lean_ctor_set_uint32(v_reuseFailAlloc_1985_, sizeof(void*)*13 + 4, v_numThreads_1965_);
lean_ctor_set_uint8(v_reuseFailAlloc_1985_, sizeof(void*)*13 + 15, v_jsonOutput_1972_);
lean_ctor_set_uint8(v_reuseFailAlloc_1985_, sizeof(void*)*13 + 16, v_printStats_1974_);
lean_ctor_set_uint8(v_reuseFailAlloc_1985_, sizeof(void*)*13 + 17, v_run_1975_);
v___x_1983_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
lean_object* v___x_1984_; 
lean_ctor_set_uint8(v___x_1983_, sizeof(void*)*13 + 13, v___x_1197_);
v___x_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
return v___x_1984_;
}
}
}
}
else
{
lean_object* v_leanOpts_1987_; lean_object* v_forwardedArgs_1988_; uint8_t v_component_1989_; uint8_t v_printPrefix_1990_; uint8_t v_printLibDir_1991_; uint8_t v_useStdin_1992_; uint8_t v_onlySrcDeps_1993_; uint8_t v_depsJson_1994_; lean_object* v_opts_1995_; uint32_t v_trustLevel_1996_; uint32_t v_numThreads_1997_; lean_object* v_rootDir_x3f_1998_; lean_object* v_setupFileName_x3f_1999_; lean_object* v_oleanFileName_x3f_2000_; lean_object* v_ileanFileName_x3f_2001_; lean_object* v_cFileName_x3f_2002_; lean_object* v_bcFileName_x3f_2003_; uint8_t v_jsonOutput_2004_; lean_object* v_errorOnKinds_2005_; uint8_t v_printStats_2006_; uint8_t v_run_2007_; lean_object* v_incrSaveFileName_x3f_2008_; lean_object* v_incrLoadFileName_x3f_2009_; lean_object* v_incrHeaderSaveFileName_x3f_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2018_; 
lean_dec(v_optArg_x3f_936_);
v_leanOpts_1987_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_1988_ = lean_ctor_get(v_opts_934_, 1);
v_component_1989_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_1990_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_1991_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_1992_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlySrcDeps_1993_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_1994_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_1995_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_1996_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_1997_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1998_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_1999_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_2000_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_2001_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_2002_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_2003_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_2004_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_2005_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_2006_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_2007_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2008_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_2009_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_2010_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2012_ = v_opts_934_;
v_isShared_2013_ = v_isSharedCheck_2018_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2010_);
lean_inc(v_incrLoadFileName_x3f_2009_);
lean_inc(v_incrSaveFileName_x3f_2008_);
lean_inc(v_errorOnKinds_2005_);
lean_inc(v_bcFileName_x3f_2003_);
lean_inc(v_cFileName_x3f_2002_);
lean_inc(v_ileanFileName_x3f_2001_);
lean_inc(v_oleanFileName_x3f_2000_);
lean_inc(v_setupFileName_x3f_1999_);
lean_inc(v_rootDir_x3f_1998_);
lean_inc(v_opts_1995_);
lean_inc(v_forwardedArgs_1988_);
lean_inc(v_leanOpts_1987_);
lean_dec(v_opts_934_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2018_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_leanOpts_1987_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_forwardedArgs_1988_);
lean_ctor_set(v_reuseFailAlloc_2017_, 2, v_opts_1995_);
lean_ctor_set(v_reuseFailAlloc_2017_, 3, v_rootDir_x3f_1998_);
lean_ctor_set(v_reuseFailAlloc_2017_, 4, v_setupFileName_x3f_1999_);
lean_ctor_set(v_reuseFailAlloc_2017_, 5, v_oleanFileName_x3f_2000_);
lean_ctor_set(v_reuseFailAlloc_2017_, 6, v_ileanFileName_x3f_2001_);
lean_ctor_set(v_reuseFailAlloc_2017_, 7, v_cFileName_x3f_2002_);
lean_ctor_set(v_reuseFailAlloc_2017_, 8, v_bcFileName_x3f_2003_);
lean_ctor_set(v_reuseFailAlloc_2017_, 9, v_errorOnKinds_2005_);
lean_ctor_set(v_reuseFailAlloc_2017_, 10, v_incrSaveFileName_x3f_2008_);
lean_ctor_set(v_reuseFailAlloc_2017_, 11, v_incrLoadFileName_x3f_2009_);
lean_ctor_set(v_reuseFailAlloc_2017_, 12, v_incrHeaderSaveFileName_x3f_2010_);
lean_ctor_set_uint8(v_reuseFailAlloc_2017_, sizeof(void*)*13 + 8, v_component_1989_);
lean_ctor_set_uint8(v_reuseFailAlloc_2017_, sizeof(void*)*13 + 9, v_printPrefix_1990_);
lean_ctor_set_uint8(v_reuseFailAlloc_2017_, sizeof(void*)*13 + 10, v_printLibDir_1991_);
lean_ctor_set_uint8(v_reuseFailAlloc_2017_, sizeof(void*)*13 + 11, v_useStdin_1992_);
lean_ctor_set_uint8(v_reuseFailAlloc_2017_, sizeof(void*)*13 + 13, v_onlySrcDeps_1993_);
lean_ctor_set_uint8(v_reuseFailAlloc_2017_, sizeof(void*)*13 + 14, v_depsJson_1994_);
lean_ctor_set_uint32(v_reuseFailAlloc_2017_, sizeof(void*)*13, v_trustLevel_1996_);
lean_ctor_set_uint32(v_reuseFailAlloc_2017_, sizeof(void*)*13 + 4, v_numThreads_1997_);
lean_ctor_set_uint8(v_reuseFailAlloc_2017_, sizeof(void*)*13 + 15, v_jsonOutput_2004_);
lean_ctor_set_uint8(v_reuseFailAlloc_2017_, sizeof(void*)*13 + 16, v_printStats_2006_);
lean_ctor_set_uint8(v_reuseFailAlloc_2017_, sizeof(void*)*13 + 17, v_run_2007_);
v___x_2015_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
lean_object* v___x_2016_; 
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*13 + 12, v___x_1195_);
v___x_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
return v___x_2016_;
}
}
}
}
else
{
lean_object* v_leanOpts_2019_; lean_object* v_forwardedArgs_2020_; uint8_t v_component_2021_; uint8_t v_printPrefix_2022_; uint8_t v_printLibDir_2023_; uint8_t v_useStdin_2024_; uint8_t v_onlyDeps_2025_; uint8_t v_onlySrcDeps_2026_; uint8_t v_depsJson_2027_; lean_object* v_opts_2028_; uint32_t v_trustLevel_2029_; uint32_t v_numThreads_2030_; lean_object* v_rootDir_x3f_2031_; lean_object* v_setupFileName_x3f_2032_; lean_object* v_oleanFileName_x3f_2033_; lean_object* v_ileanFileName_x3f_2034_; lean_object* v_cFileName_x3f_2035_; lean_object* v_bcFileName_x3f_2036_; uint8_t v_jsonOutput_2037_; lean_object* v_errorOnKinds_2038_; uint8_t v_printStats_2039_; uint8_t v_run_2040_; lean_object* v_incrSaveFileName_x3f_2041_; lean_object* v_incrLoadFileName_x3f_2042_; lean_object* v_incrHeaderSaveFileName_x3f_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2053_; 
lean_dec(v_optArg_x3f_936_);
v_leanOpts_2019_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_2020_ = lean_ctor_get(v_opts_934_, 1);
v_component_2021_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_2022_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_2023_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_2024_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_2025_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2026_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_2027_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_2028_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_2029_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_2030_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2031_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_2032_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_2033_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_2034_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_2035_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_2036_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_2037_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_2038_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_2039_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_2040_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2041_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_2042_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_2043_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2045_ = v_opts_934_;
v_isShared_2046_ = v_isSharedCheck_2053_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2043_);
lean_inc(v_incrLoadFileName_x3f_2042_);
lean_inc(v_incrSaveFileName_x3f_2041_);
lean_inc(v_errorOnKinds_2038_);
lean_inc(v_bcFileName_x3f_2036_);
lean_inc(v_cFileName_x3f_2035_);
lean_inc(v_ileanFileName_x3f_2034_);
lean_inc(v_oleanFileName_x3f_2033_);
lean_inc(v_setupFileName_x3f_2032_);
lean_inc(v_rootDir_x3f_2031_);
lean_inc(v_opts_2028_);
lean_inc(v_forwardedArgs_2020_);
lean_inc(v_leanOpts_2019_);
lean_dec(v_opts_934_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2053_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2050_; 
v___x_2047_ = l___private_Lean_Shell_0__Lean_verbose;
v___x_2048_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_2019_, v___x_2047_, v___x_1191_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v___x_2048_);
v___x_2050_ = v___x_2045_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2048_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_forwardedArgs_2020_);
lean_ctor_set(v_reuseFailAlloc_2052_, 2, v_opts_2028_);
lean_ctor_set(v_reuseFailAlloc_2052_, 3, v_rootDir_x3f_2031_);
lean_ctor_set(v_reuseFailAlloc_2052_, 4, v_setupFileName_x3f_2032_);
lean_ctor_set(v_reuseFailAlloc_2052_, 5, v_oleanFileName_x3f_2033_);
lean_ctor_set(v_reuseFailAlloc_2052_, 6, v_ileanFileName_x3f_2034_);
lean_ctor_set(v_reuseFailAlloc_2052_, 7, v_cFileName_x3f_2035_);
lean_ctor_set(v_reuseFailAlloc_2052_, 8, v_bcFileName_x3f_2036_);
lean_ctor_set(v_reuseFailAlloc_2052_, 9, v_errorOnKinds_2038_);
lean_ctor_set(v_reuseFailAlloc_2052_, 10, v_incrSaveFileName_x3f_2041_);
lean_ctor_set(v_reuseFailAlloc_2052_, 11, v_incrLoadFileName_x3f_2042_);
lean_ctor_set(v_reuseFailAlloc_2052_, 12, v_incrHeaderSaveFileName_x3f_2043_);
lean_ctor_set_uint8(v_reuseFailAlloc_2052_, sizeof(void*)*13 + 8, v_component_2021_);
lean_ctor_set_uint8(v_reuseFailAlloc_2052_, sizeof(void*)*13 + 9, v_printPrefix_2022_);
lean_ctor_set_uint8(v_reuseFailAlloc_2052_, sizeof(void*)*13 + 10, v_printLibDir_2023_);
lean_ctor_set_uint8(v_reuseFailAlloc_2052_, sizeof(void*)*13 + 11, v_useStdin_2024_);
lean_ctor_set_uint8(v_reuseFailAlloc_2052_, sizeof(void*)*13 + 12, v_onlyDeps_2025_);
lean_ctor_set_uint8(v_reuseFailAlloc_2052_, sizeof(void*)*13 + 13, v_onlySrcDeps_2026_);
lean_ctor_set_uint8(v_reuseFailAlloc_2052_, sizeof(void*)*13 + 14, v_depsJson_2027_);
lean_ctor_set_uint32(v_reuseFailAlloc_2052_, sizeof(void*)*13, v_trustLevel_2029_);
lean_ctor_set_uint32(v_reuseFailAlloc_2052_, sizeof(void*)*13 + 4, v_numThreads_2030_);
lean_ctor_set_uint8(v_reuseFailAlloc_2052_, sizeof(void*)*13 + 15, v_jsonOutput_2037_);
lean_ctor_set_uint8(v_reuseFailAlloc_2052_, sizeof(void*)*13 + 16, v_printStats_2039_);
lean_ctor_set_uint8(v_reuseFailAlloc_2052_, sizeof(void*)*13 + 17, v_run_2040_);
v___x_2050_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
return v___x_2051_;
}
}
}
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13));
v___x_2055_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2054_, v_optArg_x3f_936_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2109_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2109_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2109_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2060_ = lean_unsigned_to_nat(0u);
v___x_2061_ = lean_string_utf8_byte_size(v_a_2056_);
lean_inc(v_a_2056_);
v___x_2062_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2062_, 0, v_a_2056_);
lean_ctor_set(v___x_2062_, 1, v___x_2060_);
lean_ctor_set(v___x_2062_, 2, v___x_2061_);
v___x_2063_ = l_String_Slice_toNat_x3f(v___x_2062_);
lean_dec_ref_known(v___x_2062_, 3);
if (lean_obj_tag(v___x_2063_) == 1)
{
lean_object* v_val_2064_; lean_object* v___x_2065_; uint8_t v___x_2066_; 
v_val_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_val_2064_);
lean_dec_ref_known(v___x_2063_, 1);
v___x_2065_ = lean_cstr_to_nat("4294967296");
v___x_2066_ = lean_nat_dec_lt(v_val_2064_, v___x_2065_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
lean_dec(v_val_2064_);
lean_del_object(v___x_2058_);
lean_dec(v_a_2056_);
lean_dec_ref(v_opts_934_);
v___x_2067_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14));
v___x_2068_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2067_);
lean_dec_ref(v___x_2068_);
goto v___jp_1004_;
}
else
{
lean_object* v_leanOpts_2069_; lean_object* v_forwardedArgs_2070_; uint8_t v_component_2071_; uint8_t v_printPrefix_2072_; uint8_t v_printLibDir_2073_; uint8_t v_useStdin_2074_; uint8_t v_onlyDeps_2075_; uint8_t v_onlySrcDeps_2076_; uint8_t v_depsJson_2077_; lean_object* v_opts_2078_; uint32_t v_numThreads_2079_; lean_object* v_rootDir_x3f_2080_; lean_object* v_setupFileName_x3f_2081_; lean_object* v_oleanFileName_x3f_2082_; lean_object* v_ileanFileName_x3f_2083_; lean_object* v_cFileName_x3f_2084_; lean_object* v_bcFileName_x3f_2085_; uint8_t v_jsonOutput_2086_; lean_object* v_errorOnKinds_2087_; uint8_t v_printStats_2088_; uint8_t v_run_2089_; lean_object* v_incrSaveFileName_x3f_2090_; lean_object* v_incrLoadFileName_x3f_2091_; lean_object* v_incrHeaderSaveFileName_x3f_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2106_; 
v_leanOpts_2069_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_2070_ = lean_ctor_get(v_opts_934_, 1);
v_component_2071_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_2072_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_2073_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_2074_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_2075_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2076_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_2077_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_2078_ = lean_ctor_get(v_opts_934_, 2);
v_numThreads_2079_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2080_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_2081_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_2082_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_2083_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_2084_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_2085_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_2086_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_2087_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_2088_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_2089_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2090_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_2091_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_2092_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_2106_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2094_ = v_opts_934_;
v_isShared_2095_ = v_isSharedCheck_2106_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2092_);
lean_inc(v_incrLoadFileName_x3f_2091_);
lean_inc(v_incrSaveFileName_x3f_2090_);
lean_inc(v_errorOnKinds_2087_);
lean_inc(v_bcFileName_x3f_2085_);
lean_inc(v_cFileName_x3f_2084_);
lean_inc(v_ileanFileName_x3f_2083_);
lean_inc(v_oleanFileName_x3f_2082_);
lean_inc(v_setupFileName_x3f_2081_);
lean_inc(v_rootDir_x3f_2080_);
lean_inc(v_opts_2078_);
lean_inc(v_forwardedArgs_2070_);
lean_inc(v_leanOpts_2069_);
lean_dec(v_opts_934_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2106_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
uint32_t v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2096_ = lean_uint32_of_nat(v_val_2064_);
lean_dec(v_val_2064_);
v___x_2097_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15));
v___x_2098_ = lean_string_append(v___x_2097_, v_a_2056_);
lean_dec(v_a_2056_);
v___x_2099_ = lean_array_push(v_forwardedArgs_2070_, v___x_2098_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 1, v___x_2099_);
v___x_2101_ = v___x_2094_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_leanOpts_2069_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v___x_2099_);
lean_ctor_set(v_reuseFailAlloc_2105_, 2, v_opts_2078_);
lean_ctor_set(v_reuseFailAlloc_2105_, 3, v_rootDir_x3f_2080_);
lean_ctor_set(v_reuseFailAlloc_2105_, 4, v_setupFileName_x3f_2081_);
lean_ctor_set(v_reuseFailAlloc_2105_, 5, v_oleanFileName_x3f_2082_);
lean_ctor_set(v_reuseFailAlloc_2105_, 6, v_ileanFileName_x3f_2083_);
lean_ctor_set(v_reuseFailAlloc_2105_, 7, v_cFileName_x3f_2084_);
lean_ctor_set(v_reuseFailAlloc_2105_, 8, v_bcFileName_x3f_2085_);
lean_ctor_set(v_reuseFailAlloc_2105_, 9, v_errorOnKinds_2087_);
lean_ctor_set(v_reuseFailAlloc_2105_, 10, v_incrSaveFileName_x3f_2090_);
lean_ctor_set(v_reuseFailAlloc_2105_, 11, v_incrLoadFileName_x3f_2091_);
lean_ctor_set(v_reuseFailAlloc_2105_, 12, v_incrHeaderSaveFileName_x3f_2092_);
lean_ctor_set_uint8(v_reuseFailAlloc_2105_, sizeof(void*)*13 + 8, v_component_2071_);
lean_ctor_set_uint8(v_reuseFailAlloc_2105_, sizeof(void*)*13 + 9, v_printPrefix_2072_);
lean_ctor_set_uint8(v_reuseFailAlloc_2105_, sizeof(void*)*13 + 10, v_printLibDir_2073_);
lean_ctor_set_uint8(v_reuseFailAlloc_2105_, sizeof(void*)*13 + 11, v_useStdin_2074_);
lean_ctor_set_uint8(v_reuseFailAlloc_2105_, sizeof(void*)*13 + 12, v_onlyDeps_2075_);
lean_ctor_set_uint8(v_reuseFailAlloc_2105_, sizeof(void*)*13 + 13, v_onlySrcDeps_2076_);
lean_ctor_set_uint8(v_reuseFailAlloc_2105_, sizeof(void*)*13 + 14, v_depsJson_2077_);
lean_ctor_set_uint32(v_reuseFailAlloc_2105_, sizeof(void*)*13 + 4, v_numThreads_2079_);
lean_ctor_set_uint8(v_reuseFailAlloc_2105_, sizeof(void*)*13 + 15, v_jsonOutput_2086_);
lean_ctor_set_uint8(v_reuseFailAlloc_2105_, sizeof(void*)*13 + 16, v_printStats_2088_);
lean_ctor_set_uint8(v_reuseFailAlloc_2105_, sizeof(void*)*13 + 17, v_run_2089_);
v___x_2101_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2103_; 
lean_ctor_set_uint32(v___x_2101_, sizeof(void*)*13, v___x_2096_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v___x_2101_);
v___x_2103_ = v___x_2058_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
}
else
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
lean_dec(v___x_2063_);
lean_del_object(v___x_2058_);
lean_dec(v_a_2056_);
lean_dec_ref(v_opts_934_);
v___x_2107_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16));
v___x_2108_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2107_);
lean_dec_ref(v___x_2108_);
goto v___jp_1001_;
}
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
lean_dec_ref(v_opts_934_);
v_a_2110_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2110_);
lean_dec_ref_known(v___x_2055_, 1);
v___x_2114_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2115_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2114_);
lean_dec_ref(v___x_2115_);
goto v___jp_2111_;
v___jp_2111_:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = lean_io_error_to_string(v_a_2110_);
v___x_2113_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2112_);
lean_dec_ref(v___x_2113_);
goto v___jp_998_;
}
}
}
}
else
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17));
v___x_2117_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2116_, v_optArg_x3f_936_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2169_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2120_ = v___x_2117_;
v_isShared_2121_ = v_isSharedCheck_2169_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2117_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2169_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2122_ = lean_unsigned_to_nat(0u);
v___x_2123_ = lean_string_utf8_byte_size(v_a_2118_);
lean_inc(v_a_2118_);
v___x_2124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2124_, 0, v_a_2118_);
lean_ctor_set(v___x_2124_, 1, v___x_2122_);
lean_ctor_set(v___x_2124_, 2, v___x_2123_);
v___x_2125_ = l_String_Slice_toNat_x3f(v___x_2124_);
lean_dec_ref_known(v___x_2124_, 3);
if (lean_obj_tag(v___x_2125_) == 1)
{
lean_object* v_val_2126_; lean_object* v_leanOpts_2127_; lean_object* v_forwardedArgs_2128_; uint8_t v_component_2129_; uint8_t v_printPrefix_2130_; uint8_t v_printLibDir_2131_; uint8_t v_useStdin_2132_; uint8_t v_onlyDeps_2133_; uint8_t v_onlySrcDeps_2134_; uint8_t v_depsJson_2135_; lean_object* v_opts_2136_; uint32_t v_trustLevel_2137_; uint32_t v_numThreads_2138_; lean_object* v_rootDir_x3f_2139_; lean_object* v_setupFileName_x3f_2140_; lean_object* v_oleanFileName_x3f_2141_; lean_object* v_ileanFileName_x3f_2142_; lean_object* v_cFileName_x3f_2143_; lean_object* v_bcFileName_x3f_2144_; uint8_t v_jsonOutput_2145_; lean_object* v_errorOnKinds_2146_; uint8_t v_printStats_2147_; uint8_t v_run_2148_; lean_object* v_incrSaveFileName_x3f_2149_; lean_object* v_incrLoadFileName_x3f_2150_; lean_object* v_incrHeaderSaveFileName_x3f_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2166_; 
v_val_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_val_2126_);
lean_dec_ref_known(v___x_2125_, 1);
v_leanOpts_2127_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_2128_ = lean_ctor_get(v_opts_934_, 1);
v_component_2129_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_2130_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_2131_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_2132_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_2133_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2134_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_2135_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_2136_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_2137_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_2138_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2139_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_2140_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_2141_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_2142_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_2143_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_2144_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_2145_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_2146_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_2147_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_2148_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2149_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_2150_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_2151_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2153_ = v_opts_934_;
v_isShared_2154_ = v_isSharedCheck_2166_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2151_);
lean_inc(v_incrLoadFileName_x3f_2150_);
lean_inc(v_incrSaveFileName_x3f_2149_);
lean_inc(v_errorOnKinds_2146_);
lean_inc(v_bcFileName_x3f_2144_);
lean_inc(v_cFileName_x3f_2143_);
lean_inc(v_ileanFileName_x3f_2142_);
lean_inc(v_oleanFileName_x3f_2141_);
lean_inc(v_setupFileName_x3f_2140_);
lean_inc(v_rootDir_x3f_2139_);
lean_inc(v_opts_2136_);
lean_inc(v_forwardedArgs_2128_);
lean_inc(v_leanOpts_2127_);
lean_dec(v_opts_934_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2166_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2161_; 
v___x_2155_ = l___private_Lean_Shell_0__Lean_timeout;
v___x_2156_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_2127_, v___x_2155_, v_val_2126_);
v___x_2157_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18));
v___x_2158_ = lean_string_append(v___x_2157_, v_a_2118_);
lean_dec(v_a_2118_);
v___x_2159_ = lean_array_push(v_forwardedArgs_2128_, v___x_2158_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 1, v___x_2159_);
lean_ctor_set(v___x_2153_, 0, v___x_2156_);
v___x_2161_ = v___x_2153_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v___x_2159_);
lean_ctor_set(v_reuseFailAlloc_2165_, 2, v_opts_2136_);
lean_ctor_set(v_reuseFailAlloc_2165_, 3, v_rootDir_x3f_2139_);
lean_ctor_set(v_reuseFailAlloc_2165_, 4, v_setupFileName_x3f_2140_);
lean_ctor_set(v_reuseFailAlloc_2165_, 5, v_oleanFileName_x3f_2141_);
lean_ctor_set(v_reuseFailAlloc_2165_, 6, v_ileanFileName_x3f_2142_);
lean_ctor_set(v_reuseFailAlloc_2165_, 7, v_cFileName_x3f_2143_);
lean_ctor_set(v_reuseFailAlloc_2165_, 8, v_bcFileName_x3f_2144_);
lean_ctor_set(v_reuseFailAlloc_2165_, 9, v_errorOnKinds_2146_);
lean_ctor_set(v_reuseFailAlloc_2165_, 10, v_incrSaveFileName_x3f_2149_);
lean_ctor_set(v_reuseFailAlloc_2165_, 11, v_incrLoadFileName_x3f_2150_);
lean_ctor_set(v_reuseFailAlloc_2165_, 12, v_incrHeaderSaveFileName_x3f_2151_);
lean_ctor_set_uint8(v_reuseFailAlloc_2165_, sizeof(void*)*13 + 8, v_component_2129_);
lean_ctor_set_uint8(v_reuseFailAlloc_2165_, sizeof(void*)*13 + 9, v_printPrefix_2130_);
lean_ctor_set_uint8(v_reuseFailAlloc_2165_, sizeof(void*)*13 + 10, v_printLibDir_2131_);
lean_ctor_set_uint8(v_reuseFailAlloc_2165_, sizeof(void*)*13 + 11, v_useStdin_2132_);
lean_ctor_set_uint8(v_reuseFailAlloc_2165_, sizeof(void*)*13 + 12, v_onlyDeps_2133_);
lean_ctor_set_uint8(v_reuseFailAlloc_2165_, sizeof(void*)*13 + 13, v_onlySrcDeps_2134_);
lean_ctor_set_uint8(v_reuseFailAlloc_2165_, sizeof(void*)*13 + 14, v_depsJson_2135_);
lean_ctor_set_uint32(v_reuseFailAlloc_2165_, sizeof(void*)*13, v_trustLevel_2137_);
lean_ctor_set_uint32(v_reuseFailAlloc_2165_, sizeof(void*)*13 + 4, v_numThreads_2138_);
lean_ctor_set_uint8(v_reuseFailAlloc_2165_, sizeof(void*)*13 + 15, v_jsonOutput_2145_);
lean_ctor_set_uint8(v_reuseFailAlloc_2165_, sizeof(void*)*13 + 16, v_printStats_2147_);
lean_ctor_set_uint8(v_reuseFailAlloc_2165_, sizeof(void*)*13 + 17, v_run_2148_);
v___x_2161_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
lean_object* v___x_2163_; 
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v___x_2161_);
v___x_2163_ = v___x_2120_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
else
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
lean_dec(v___x_2125_);
lean_del_object(v___x_2120_);
lean_dec(v_a_2118_);
lean_dec_ref(v_opts_934_);
v___x_2167_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19));
v___x_2168_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2167_);
lean_dec_ref(v___x_2168_);
goto v___jp_1111_;
}
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
lean_dec_ref(v_opts_934_);
v_a_2170_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2170_);
lean_dec_ref_known(v___x_2117_, 1);
v___x_2174_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2175_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2174_);
lean_dec_ref(v___x_2175_);
goto v___jp_2171_;
v___jp_2171_:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2172_ = lean_io_error_to_string(v_a_2170_);
v___x_2173_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2172_);
lean_dec_ref(v___x_2173_);
goto v___jp_1117_;
}
}
}
}
else
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20));
v___x_2177_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2176_, v_optArg_x3f_936_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2229_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2180_ = v___x_2177_;
v_isShared_2181_ = v_isSharedCheck_2229_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2177_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2229_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2182_ = lean_unsigned_to_nat(0u);
v___x_2183_ = lean_string_utf8_byte_size(v_a_2178_);
lean_inc(v_a_2178_);
v___x_2184_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2184_, 0, v_a_2178_);
lean_ctor_set(v___x_2184_, 1, v___x_2182_);
lean_ctor_set(v___x_2184_, 2, v___x_2183_);
v___x_2185_ = l_String_Slice_toNat_x3f(v___x_2184_);
lean_dec_ref_known(v___x_2184_, 3);
if (lean_obj_tag(v___x_2185_) == 1)
{
lean_object* v_val_2186_; lean_object* v_leanOpts_2187_; lean_object* v_forwardedArgs_2188_; uint8_t v_component_2189_; uint8_t v_printPrefix_2190_; uint8_t v_printLibDir_2191_; uint8_t v_useStdin_2192_; uint8_t v_onlyDeps_2193_; uint8_t v_onlySrcDeps_2194_; uint8_t v_depsJson_2195_; lean_object* v_opts_2196_; uint32_t v_trustLevel_2197_; uint32_t v_numThreads_2198_; lean_object* v_rootDir_x3f_2199_; lean_object* v_setupFileName_x3f_2200_; lean_object* v_oleanFileName_x3f_2201_; lean_object* v_ileanFileName_x3f_2202_; lean_object* v_cFileName_x3f_2203_; lean_object* v_bcFileName_x3f_2204_; uint8_t v_jsonOutput_2205_; lean_object* v_errorOnKinds_2206_; uint8_t v_printStats_2207_; uint8_t v_run_2208_; lean_object* v_incrSaveFileName_x3f_2209_; lean_object* v_incrLoadFileName_x3f_2210_; lean_object* v_incrHeaderSaveFileName_x3f_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2226_; 
v_val_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_val_2186_);
lean_dec_ref_known(v___x_2185_, 1);
v_leanOpts_2187_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_2188_ = lean_ctor_get(v_opts_934_, 1);
v_component_2189_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_2190_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_2191_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_2192_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_2193_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2194_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_2195_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_2196_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_2197_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_2198_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2199_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_2200_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_2201_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_2202_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_2203_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_2204_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_2205_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_2206_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_2207_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_2208_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2209_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_2210_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_2211_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2213_ = v_opts_934_;
v_isShared_2214_ = v_isSharedCheck_2226_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2211_);
lean_inc(v_incrLoadFileName_x3f_2210_);
lean_inc(v_incrSaveFileName_x3f_2209_);
lean_inc(v_errorOnKinds_2206_);
lean_inc(v_bcFileName_x3f_2204_);
lean_inc(v_cFileName_x3f_2203_);
lean_inc(v_ileanFileName_x3f_2202_);
lean_inc(v_oleanFileName_x3f_2201_);
lean_inc(v_setupFileName_x3f_2200_);
lean_inc(v_rootDir_x3f_2199_);
lean_inc(v_opts_2196_);
lean_inc(v_forwardedArgs_2188_);
lean_inc(v_leanOpts_2187_);
lean_dec(v_opts_934_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2226_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2221_; 
v___x_2215_ = l___private_Lean_Shell_0__Lean_maxMemory;
v___x_2216_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_2187_, v___x_2215_, v_val_2186_);
v___x_2217_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21));
v___x_2218_ = lean_string_append(v___x_2217_, v_a_2178_);
lean_dec(v_a_2178_);
v___x_2219_ = lean_array_push(v_forwardedArgs_2188_, v___x_2218_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 1, v___x_2219_);
lean_ctor_set(v___x_2213_, 0, v___x_2216_);
v___x_2221_ = v___x_2213_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2216_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v___x_2219_);
lean_ctor_set(v_reuseFailAlloc_2225_, 2, v_opts_2196_);
lean_ctor_set(v_reuseFailAlloc_2225_, 3, v_rootDir_x3f_2199_);
lean_ctor_set(v_reuseFailAlloc_2225_, 4, v_setupFileName_x3f_2200_);
lean_ctor_set(v_reuseFailAlloc_2225_, 5, v_oleanFileName_x3f_2201_);
lean_ctor_set(v_reuseFailAlloc_2225_, 6, v_ileanFileName_x3f_2202_);
lean_ctor_set(v_reuseFailAlloc_2225_, 7, v_cFileName_x3f_2203_);
lean_ctor_set(v_reuseFailAlloc_2225_, 8, v_bcFileName_x3f_2204_);
lean_ctor_set(v_reuseFailAlloc_2225_, 9, v_errorOnKinds_2206_);
lean_ctor_set(v_reuseFailAlloc_2225_, 10, v_incrSaveFileName_x3f_2209_);
lean_ctor_set(v_reuseFailAlloc_2225_, 11, v_incrLoadFileName_x3f_2210_);
lean_ctor_set(v_reuseFailAlloc_2225_, 12, v_incrHeaderSaveFileName_x3f_2211_);
lean_ctor_set_uint8(v_reuseFailAlloc_2225_, sizeof(void*)*13 + 8, v_component_2189_);
lean_ctor_set_uint8(v_reuseFailAlloc_2225_, sizeof(void*)*13 + 9, v_printPrefix_2190_);
lean_ctor_set_uint8(v_reuseFailAlloc_2225_, sizeof(void*)*13 + 10, v_printLibDir_2191_);
lean_ctor_set_uint8(v_reuseFailAlloc_2225_, sizeof(void*)*13 + 11, v_useStdin_2192_);
lean_ctor_set_uint8(v_reuseFailAlloc_2225_, sizeof(void*)*13 + 12, v_onlyDeps_2193_);
lean_ctor_set_uint8(v_reuseFailAlloc_2225_, sizeof(void*)*13 + 13, v_onlySrcDeps_2194_);
lean_ctor_set_uint8(v_reuseFailAlloc_2225_, sizeof(void*)*13 + 14, v_depsJson_2195_);
lean_ctor_set_uint32(v_reuseFailAlloc_2225_, sizeof(void*)*13, v_trustLevel_2197_);
lean_ctor_set_uint32(v_reuseFailAlloc_2225_, sizeof(void*)*13 + 4, v_numThreads_2198_);
lean_ctor_set_uint8(v_reuseFailAlloc_2225_, sizeof(void*)*13 + 15, v_jsonOutput_2205_);
lean_ctor_set_uint8(v_reuseFailAlloc_2225_, sizeof(void*)*13 + 16, v_printStats_2207_);
lean_ctor_set_uint8(v_reuseFailAlloc_2225_, sizeof(void*)*13 + 17, v_run_2208_);
v___x_2221_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
lean_object* v___x_2223_; 
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 0, v___x_2221_);
v___x_2223_ = v___x_2180_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2221_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
else
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
lean_dec(v___x_2185_);
lean_del_object(v___x_2180_);
lean_dec(v_a_2178_);
lean_dec_ref(v_opts_934_);
v___x_2227_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22));
v___x_2228_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2227_);
lean_dec_ref(v___x_2228_);
goto v___jp_992_;
}
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
lean_dec_ref(v_opts_934_);
v_a_2230_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v___x_2177_, 1);
v___x_2234_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2235_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2234_);
lean_dec_ref(v___x_2235_);
goto v___jp_2231_;
v___jp_2231_:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = lean_io_error_to_string(v_a_2230_);
v___x_2233_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2232_);
lean_dec_ref(v___x_2233_);
goto v___jp_989_;
}
}
}
}
else
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23));
v___x_2237_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2236_, v_optArg_x3f_936_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2281_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2240_ = v___x_2237_;
v_isShared_2241_ = v_isSharedCheck_2281_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2237_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2281_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v_leanOpts_2242_; lean_object* v_forwardedArgs_2243_; uint8_t v_component_2244_; uint8_t v_printPrefix_2245_; uint8_t v_printLibDir_2246_; uint8_t v_useStdin_2247_; uint8_t v_onlyDeps_2248_; uint8_t v_onlySrcDeps_2249_; uint8_t v_depsJson_2250_; lean_object* v_opts_2251_; uint32_t v_trustLevel_2252_; uint32_t v_numThreads_2253_; lean_object* v_setupFileName_x3f_2254_; lean_object* v_oleanFileName_x3f_2255_; lean_object* v_ileanFileName_x3f_2256_; lean_object* v_cFileName_x3f_2257_; lean_object* v_bcFileName_x3f_2258_; uint8_t v_jsonOutput_2259_; lean_object* v_errorOnKinds_2260_; uint8_t v_printStats_2261_; uint8_t v_run_2262_; lean_object* v_incrSaveFileName_x3f_2263_; lean_object* v_incrLoadFileName_x3f_2264_; lean_object* v_incrHeaderSaveFileName_x3f_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2279_; 
v_leanOpts_2242_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_2243_ = lean_ctor_get(v_opts_934_, 1);
v_component_2244_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_2245_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_2246_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_2247_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_2248_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2249_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_2250_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_2251_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_2252_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_2253_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_setupFileName_x3f_2254_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_2255_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_2256_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_2257_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_2258_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_2259_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_2260_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_2261_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_2262_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2263_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_2264_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_2265_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_2279_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_2279_ == 0)
{
lean_object* v_unused_2280_; 
v_unused_2280_ = lean_ctor_get(v_opts_934_, 3);
lean_dec(v_unused_2280_);
v___x_2267_ = v_opts_934_;
v_isShared_2268_ = v_isSharedCheck_2279_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2265_);
lean_inc(v_incrLoadFileName_x3f_2264_);
lean_inc(v_incrSaveFileName_x3f_2263_);
lean_inc(v_errorOnKinds_2260_);
lean_inc(v_bcFileName_x3f_2258_);
lean_inc(v_cFileName_x3f_2257_);
lean_inc(v_ileanFileName_x3f_2256_);
lean_inc(v_oleanFileName_x3f_2255_);
lean_inc(v_setupFileName_x3f_2254_);
lean_inc(v_opts_2251_);
lean_inc(v_forwardedArgs_2243_);
lean_inc(v_leanOpts_2242_);
lean_dec(v_opts_934_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2279_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2274_; 
v___x_2269_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24));
v___x_2270_ = lean_string_append(v___x_2269_, v_a_2238_);
v___x_2271_ = lean_array_push(v_forwardedArgs_2243_, v___x_2270_);
v___x_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2272_, 0, v_a_2238_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 3, v___x_2272_);
lean_ctor_set(v___x_2267_, 1, v___x_2271_);
v___x_2274_ = v___x_2267_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_leanOpts_2242_);
lean_ctor_set(v_reuseFailAlloc_2278_, 1, v___x_2271_);
lean_ctor_set(v_reuseFailAlloc_2278_, 2, v_opts_2251_);
lean_ctor_set(v_reuseFailAlloc_2278_, 3, v___x_2272_);
lean_ctor_set(v_reuseFailAlloc_2278_, 4, v_setupFileName_x3f_2254_);
lean_ctor_set(v_reuseFailAlloc_2278_, 5, v_oleanFileName_x3f_2255_);
lean_ctor_set(v_reuseFailAlloc_2278_, 6, v_ileanFileName_x3f_2256_);
lean_ctor_set(v_reuseFailAlloc_2278_, 7, v_cFileName_x3f_2257_);
lean_ctor_set(v_reuseFailAlloc_2278_, 8, v_bcFileName_x3f_2258_);
lean_ctor_set(v_reuseFailAlloc_2278_, 9, v_errorOnKinds_2260_);
lean_ctor_set(v_reuseFailAlloc_2278_, 10, v_incrSaveFileName_x3f_2263_);
lean_ctor_set(v_reuseFailAlloc_2278_, 11, v_incrLoadFileName_x3f_2264_);
lean_ctor_set(v_reuseFailAlloc_2278_, 12, v_incrHeaderSaveFileName_x3f_2265_);
lean_ctor_set_uint8(v_reuseFailAlloc_2278_, sizeof(void*)*13 + 8, v_component_2244_);
lean_ctor_set_uint8(v_reuseFailAlloc_2278_, sizeof(void*)*13 + 9, v_printPrefix_2245_);
lean_ctor_set_uint8(v_reuseFailAlloc_2278_, sizeof(void*)*13 + 10, v_printLibDir_2246_);
lean_ctor_set_uint8(v_reuseFailAlloc_2278_, sizeof(void*)*13 + 11, v_useStdin_2247_);
lean_ctor_set_uint8(v_reuseFailAlloc_2278_, sizeof(void*)*13 + 12, v_onlyDeps_2248_);
lean_ctor_set_uint8(v_reuseFailAlloc_2278_, sizeof(void*)*13 + 13, v_onlySrcDeps_2249_);
lean_ctor_set_uint8(v_reuseFailAlloc_2278_, sizeof(void*)*13 + 14, v_depsJson_2250_);
lean_ctor_set_uint32(v_reuseFailAlloc_2278_, sizeof(void*)*13, v_trustLevel_2252_);
lean_ctor_set_uint32(v_reuseFailAlloc_2278_, sizeof(void*)*13 + 4, v_numThreads_2253_);
lean_ctor_set_uint8(v_reuseFailAlloc_2278_, sizeof(void*)*13 + 15, v_jsonOutput_2259_);
lean_ctor_set_uint8(v_reuseFailAlloc_2278_, sizeof(void*)*13 + 16, v_printStats_2261_);
lean_ctor_set_uint8(v_reuseFailAlloc_2278_, sizeof(void*)*13 + 17, v_run_2262_);
v___x_2274_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
lean_object* v___x_2276_; 
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 0, v___x_2274_);
v___x_2276_ = v___x_2240_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
lean_dec_ref(v_opts_934_);
v_a_2282_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_a_2282_);
lean_dec_ref_known(v___x_2237_, 1);
v___x_2286_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2287_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2286_);
lean_dec_ref(v___x_2287_);
goto v___jp_2283_;
v___jp_2283_:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2284_ = lean_io_error_to_string(v_a_2282_);
v___x_2285_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2284_);
lean_dec_ref(v___x_2285_);
goto v___jp_1123_;
}
}
}
}
else
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25));
v___x_2289_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2288_, v_optArg_x3f_936_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2330_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2292_ = v___x_2289_;
v_isShared_2293_ = v_isSharedCheck_2330_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2289_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2330_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v_leanOpts_2294_; lean_object* v_forwardedArgs_2295_; uint8_t v_component_2296_; uint8_t v_printPrefix_2297_; uint8_t v_printLibDir_2298_; uint8_t v_useStdin_2299_; uint8_t v_onlyDeps_2300_; uint8_t v_onlySrcDeps_2301_; uint8_t v_depsJson_2302_; lean_object* v_opts_2303_; uint32_t v_trustLevel_2304_; uint32_t v_numThreads_2305_; lean_object* v_rootDir_x3f_2306_; lean_object* v_setupFileName_x3f_2307_; lean_object* v_oleanFileName_x3f_2308_; lean_object* v_cFileName_x3f_2309_; lean_object* v_bcFileName_x3f_2310_; uint8_t v_jsonOutput_2311_; lean_object* v_errorOnKinds_2312_; uint8_t v_printStats_2313_; uint8_t v_run_2314_; lean_object* v_incrSaveFileName_x3f_2315_; lean_object* v_incrLoadFileName_x3f_2316_; lean_object* v_incrHeaderSaveFileName_x3f_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2328_; 
v_leanOpts_2294_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_2295_ = lean_ctor_get(v_opts_934_, 1);
v_component_2296_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_2297_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_2298_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_2299_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_2300_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2301_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_2302_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_2303_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_2304_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_2305_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2306_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_2307_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_2308_ = lean_ctor_get(v_opts_934_, 5);
v_cFileName_x3f_2309_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_2310_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_2311_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_2312_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_2313_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_2314_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2315_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_2316_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_2317_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_2328_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_2328_ == 0)
{
lean_object* v_unused_2329_; 
v_unused_2329_ = lean_ctor_get(v_opts_934_, 6);
lean_dec(v_unused_2329_);
v___x_2319_ = v_opts_934_;
v_isShared_2320_ = v_isSharedCheck_2328_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2317_);
lean_inc(v_incrLoadFileName_x3f_2316_);
lean_inc(v_incrSaveFileName_x3f_2315_);
lean_inc(v_errorOnKinds_2312_);
lean_inc(v_bcFileName_x3f_2310_);
lean_inc(v_cFileName_x3f_2309_);
lean_inc(v_oleanFileName_x3f_2308_);
lean_inc(v_setupFileName_x3f_2307_);
lean_inc(v_rootDir_x3f_2306_);
lean_inc(v_opts_2303_);
lean_inc(v_forwardedArgs_2295_);
lean_inc(v_leanOpts_2294_);
lean_dec(v_opts_934_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2328_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2321_; lean_object* v___x_2323_; 
v___x_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2321_, 0, v_a_2290_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 6, v___x_2321_);
v___x_2323_ = v___x_2319_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_leanOpts_2294_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_forwardedArgs_2295_);
lean_ctor_set(v_reuseFailAlloc_2327_, 2, v_opts_2303_);
lean_ctor_set(v_reuseFailAlloc_2327_, 3, v_rootDir_x3f_2306_);
lean_ctor_set(v_reuseFailAlloc_2327_, 4, v_setupFileName_x3f_2307_);
lean_ctor_set(v_reuseFailAlloc_2327_, 5, v_oleanFileName_x3f_2308_);
lean_ctor_set(v_reuseFailAlloc_2327_, 6, v___x_2321_);
lean_ctor_set(v_reuseFailAlloc_2327_, 7, v_cFileName_x3f_2309_);
lean_ctor_set(v_reuseFailAlloc_2327_, 8, v_bcFileName_x3f_2310_);
lean_ctor_set(v_reuseFailAlloc_2327_, 9, v_errorOnKinds_2312_);
lean_ctor_set(v_reuseFailAlloc_2327_, 10, v_incrSaveFileName_x3f_2315_);
lean_ctor_set(v_reuseFailAlloc_2327_, 11, v_incrLoadFileName_x3f_2316_);
lean_ctor_set(v_reuseFailAlloc_2327_, 12, v_incrHeaderSaveFileName_x3f_2317_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, sizeof(void*)*13 + 8, v_component_2296_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, sizeof(void*)*13 + 9, v_printPrefix_2297_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, sizeof(void*)*13 + 10, v_printLibDir_2298_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, sizeof(void*)*13 + 11, v_useStdin_2299_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, sizeof(void*)*13 + 12, v_onlyDeps_2300_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, sizeof(void*)*13 + 13, v_onlySrcDeps_2301_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, sizeof(void*)*13 + 14, v_depsJson_2302_);
lean_ctor_set_uint32(v_reuseFailAlloc_2327_, sizeof(void*)*13, v_trustLevel_2304_);
lean_ctor_set_uint32(v_reuseFailAlloc_2327_, sizeof(void*)*13 + 4, v_numThreads_2305_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, sizeof(void*)*13 + 15, v_jsonOutput_2311_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, sizeof(void*)*13 + 16, v_printStats_2313_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, sizeof(void*)*13 + 17, v_run_2314_);
v___x_2323_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
lean_object* v___x_2325_; 
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 0, v___x_2323_);
v___x_2325_ = v___x_2292_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2323_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
}
else
{
lean_object* v_a_2331_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
lean_dec_ref(v_opts_934_);
v_a_2331_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2331_);
lean_dec_ref_known(v___x_2289_, 1);
v___x_2335_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2336_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2335_);
lean_dec_ref(v___x_2336_);
goto v___jp_2332_;
v___jp_2332_:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2333_ = lean_io_error_to_string(v_a_2331_);
v___x_2334_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2333_);
lean_dec_ref(v___x_2334_);
goto v___jp_983_;
}
}
}
}
else
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26));
v___x_2338_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2337_, v_optArg_x3f_936_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2379_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2341_ = v___x_2338_;
v_isShared_2342_ = v_isSharedCheck_2379_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2338_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2379_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v_leanOpts_2343_; lean_object* v_forwardedArgs_2344_; uint8_t v_component_2345_; uint8_t v_printPrefix_2346_; uint8_t v_printLibDir_2347_; uint8_t v_useStdin_2348_; uint8_t v_onlyDeps_2349_; uint8_t v_onlySrcDeps_2350_; uint8_t v_depsJson_2351_; lean_object* v_opts_2352_; uint32_t v_trustLevel_2353_; uint32_t v_numThreads_2354_; lean_object* v_rootDir_x3f_2355_; lean_object* v_setupFileName_x3f_2356_; lean_object* v_ileanFileName_x3f_2357_; lean_object* v_cFileName_x3f_2358_; lean_object* v_bcFileName_x3f_2359_; uint8_t v_jsonOutput_2360_; lean_object* v_errorOnKinds_2361_; uint8_t v_printStats_2362_; uint8_t v_run_2363_; lean_object* v_incrSaveFileName_x3f_2364_; lean_object* v_incrLoadFileName_x3f_2365_; lean_object* v_incrHeaderSaveFileName_x3f_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2377_; 
v_leanOpts_2343_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_2344_ = lean_ctor_get(v_opts_934_, 1);
v_component_2345_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_2346_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_2347_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_2348_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_2349_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2350_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_2351_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_2352_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_2353_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_2354_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2355_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_2356_ = lean_ctor_get(v_opts_934_, 4);
v_ileanFileName_x3f_2357_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_2358_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_2359_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_2360_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_2361_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_2362_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_2363_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2364_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_2365_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_2366_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_2377_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_2377_ == 0)
{
lean_object* v_unused_2378_; 
v_unused_2378_ = lean_ctor_get(v_opts_934_, 5);
lean_dec(v_unused_2378_);
v___x_2368_ = v_opts_934_;
v_isShared_2369_ = v_isSharedCheck_2377_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2366_);
lean_inc(v_incrLoadFileName_x3f_2365_);
lean_inc(v_incrSaveFileName_x3f_2364_);
lean_inc(v_errorOnKinds_2361_);
lean_inc(v_bcFileName_x3f_2359_);
lean_inc(v_cFileName_x3f_2358_);
lean_inc(v_ileanFileName_x3f_2357_);
lean_inc(v_setupFileName_x3f_2356_);
lean_inc(v_rootDir_x3f_2355_);
lean_inc(v_opts_2352_);
lean_inc(v_forwardedArgs_2344_);
lean_inc(v_leanOpts_2343_);
lean_dec(v_opts_934_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2377_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2370_; lean_object* v___x_2372_; 
v___x_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2370_, 0, v_a_2339_);
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 5, v___x_2370_);
v___x_2372_ = v___x_2368_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_leanOpts_2343_);
lean_ctor_set(v_reuseFailAlloc_2376_, 1, v_forwardedArgs_2344_);
lean_ctor_set(v_reuseFailAlloc_2376_, 2, v_opts_2352_);
lean_ctor_set(v_reuseFailAlloc_2376_, 3, v_rootDir_x3f_2355_);
lean_ctor_set(v_reuseFailAlloc_2376_, 4, v_setupFileName_x3f_2356_);
lean_ctor_set(v_reuseFailAlloc_2376_, 5, v___x_2370_);
lean_ctor_set(v_reuseFailAlloc_2376_, 6, v_ileanFileName_x3f_2357_);
lean_ctor_set(v_reuseFailAlloc_2376_, 7, v_cFileName_x3f_2358_);
lean_ctor_set(v_reuseFailAlloc_2376_, 8, v_bcFileName_x3f_2359_);
lean_ctor_set(v_reuseFailAlloc_2376_, 9, v_errorOnKinds_2361_);
lean_ctor_set(v_reuseFailAlloc_2376_, 10, v_incrSaveFileName_x3f_2364_);
lean_ctor_set(v_reuseFailAlloc_2376_, 11, v_incrLoadFileName_x3f_2365_);
lean_ctor_set(v_reuseFailAlloc_2376_, 12, v_incrHeaderSaveFileName_x3f_2366_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, sizeof(void*)*13 + 8, v_component_2345_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, sizeof(void*)*13 + 9, v_printPrefix_2346_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, sizeof(void*)*13 + 10, v_printLibDir_2347_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, sizeof(void*)*13 + 11, v_useStdin_2348_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, sizeof(void*)*13 + 12, v_onlyDeps_2349_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, sizeof(void*)*13 + 13, v_onlySrcDeps_2350_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, sizeof(void*)*13 + 14, v_depsJson_2351_);
lean_ctor_set_uint32(v_reuseFailAlloc_2376_, sizeof(void*)*13, v_trustLevel_2353_);
lean_ctor_set_uint32(v_reuseFailAlloc_2376_, sizeof(void*)*13 + 4, v_numThreads_2354_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, sizeof(void*)*13 + 15, v_jsonOutput_2360_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, sizeof(void*)*13 + 16, v_printStats_2362_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, sizeof(void*)*13 + 17, v_run_2363_);
v___x_2372_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
lean_object* v___x_2374_; 
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 0, v___x_2372_);
v___x_2374_ = v___x_2341_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2372_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
lean_dec_ref(v_opts_934_);
v_a_2380_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2380_);
lean_dec_ref_known(v___x_2338_, 1);
v___x_2384_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2385_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2384_);
lean_dec_ref(v___x_2385_);
goto v___jp_2381_;
v___jp_2381_:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = lean_io_error_to_string(v_a_2380_);
v___x_2383_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2382_);
lean_dec_ref(v___x_2383_);
goto v___jp_1129_;
}
}
}
}
else
{
lean_object* v_leanOpts_2386_; lean_object* v_forwardedArgs_2387_; uint8_t v_component_2388_; uint8_t v_printPrefix_2389_; uint8_t v_printLibDir_2390_; uint8_t v_useStdin_2391_; uint8_t v_onlyDeps_2392_; uint8_t v_onlySrcDeps_2393_; uint8_t v_depsJson_2394_; lean_object* v_opts_2395_; uint32_t v_trustLevel_2396_; uint32_t v_numThreads_2397_; lean_object* v_rootDir_x3f_2398_; lean_object* v_setupFileName_x3f_2399_; lean_object* v_oleanFileName_x3f_2400_; lean_object* v_ileanFileName_x3f_2401_; lean_object* v_cFileName_x3f_2402_; lean_object* v_bcFileName_x3f_2403_; uint8_t v_jsonOutput_2404_; lean_object* v_errorOnKinds_2405_; uint8_t v_printStats_2406_; lean_object* v_incrSaveFileName_x3f_2407_; lean_object* v_incrLoadFileName_x3f_2408_; lean_object* v_incrHeaderSaveFileName_x3f_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2419_; 
lean_dec(v_optArg_x3f_936_);
v_leanOpts_2386_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_2387_ = lean_ctor_get(v_opts_934_, 1);
v_component_2388_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_2389_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_2390_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_2391_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_2392_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2393_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_2394_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_2395_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_2396_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_2397_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2398_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_2399_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_2400_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_2401_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_2402_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_2403_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_2404_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_2405_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_2406_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_incrSaveFileName_x3f_2407_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_2408_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_2409_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_2419_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2411_ = v_opts_934_;
v_isShared_2412_ = v_isSharedCheck_2419_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2409_);
lean_inc(v_incrLoadFileName_x3f_2408_);
lean_inc(v_incrSaveFileName_x3f_2407_);
lean_inc(v_errorOnKinds_2405_);
lean_inc(v_bcFileName_x3f_2403_);
lean_inc(v_cFileName_x3f_2402_);
lean_inc(v_ileanFileName_x3f_2401_);
lean_inc(v_oleanFileName_x3f_2400_);
lean_inc(v_setupFileName_x3f_2399_);
lean_inc(v_rootDir_x3f_2398_);
lean_inc(v_opts_2395_);
lean_inc(v_forwardedArgs_2387_);
lean_inc(v_leanOpts_2386_);
lean_dec(v_opts_934_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2419_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2416_; 
v___x_2413_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_2414_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_2386_, v___x_2413_, v___x_1177_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 0, v___x_2414_);
v___x_2416_ = v___x_2411_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2414_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v_forwardedArgs_2387_);
lean_ctor_set(v_reuseFailAlloc_2418_, 2, v_opts_2395_);
lean_ctor_set(v_reuseFailAlloc_2418_, 3, v_rootDir_x3f_2398_);
lean_ctor_set(v_reuseFailAlloc_2418_, 4, v_setupFileName_x3f_2399_);
lean_ctor_set(v_reuseFailAlloc_2418_, 5, v_oleanFileName_x3f_2400_);
lean_ctor_set(v_reuseFailAlloc_2418_, 6, v_ileanFileName_x3f_2401_);
lean_ctor_set(v_reuseFailAlloc_2418_, 7, v_cFileName_x3f_2402_);
lean_ctor_set(v_reuseFailAlloc_2418_, 8, v_bcFileName_x3f_2403_);
lean_ctor_set(v_reuseFailAlloc_2418_, 9, v_errorOnKinds_2405_);
lean_ctor_set(v_reuseFailAlloc_2418_, 10, v_incrSaveFileName_x3f_2407_);
lean_ctor_set(v_reuseFailAlloc_2418_, 11, v_incrLoadFileName_x3f_2408_);
lean_ctor_set(v_reuseFailAlloc_2418_, 12, v_incrHeaderSaveFileName_x3f_2409_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, sizeof(void*)*13 + 8, v_component_2388_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, sizeof(void*)*13 + 9, v_printPrefix_2389_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, sizeof(void*)*13 + 10, v_printLibDir_2390_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, sizeof(void*)*13 + 11, v_useStdin_2391_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, sizeof(void*)*13 + 12, v_onlyDeps_2392_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, sizeof(void*)*13 + 13, v_onlySrcDeps_2393_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, sizeof(void*)*13 + 14, v_depsJson_2394_);
lean_ctor_set_uint32(v_reuseFailAlloc_2418_, sizeof(void*)*13, v_trustLevel_2396_);
lean_ctor_set_uint32(v_reuseFailAlloc_2418_, sizeof(void*)*13 + 4, v_numThreads_2397_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, sizeof(void*)*13 + 15, v_jsonOutput_2404_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, sizeof(void*)*13 + 16, v_printStats_2406_);
v___x_2416_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
lean_object* v___x_2417_; 
lean_ctor_set_uint8(v___x_2416_, sizeof(void*)*13 + 17, v___x_1179_);
v___x_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
return v___x_2417_;
}
}
}
}
else
{
lean_object* v_leanOpts_2420_; lean_object* v_forwardedArgs_2421_; uint8_t v_component_2422_; uint8_t v_printPrefix_2423_; uint8_t v_printLibDir_2424_; uint8_t v_onlyDeps_2425_; uint8_t v_onlySrcDeps_2426_; uint8_t v_depsJson_2427_; lean_object* v_opts_2428_; uint32_t v_trustLevel_2429_; uint32_t v_numThreads_2430_; lean_object* v_rootDir_x3f_2431_; lean_object* v_setupFileName_x3f_2432_; lean_object* v_oleanFileName_x3f_2433_; lean_object* v_ileanFileName_x3f_2434_; lean_object* v_cFileName_x3f_2435_; lean_object* v_bcFileName_x3f_2436_; uint8_t v_jsonOutput_2437_; lean_object* v_errorOnKinds_2438_; uint8_t v_printStats_2439_; uint8_t v_run_2440_; lean_object* v_incrSaveFileName_x3f_2441_; lean_object* v_incrLoadFileName_x3f_2442_; lean_object* v_incrHeaderSaveFileName_x3f_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2451_; 
lean_dec(v_optArg_x3f_936_);
v_leanOpts_2420_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_2421_ = lean_ctor_get(v_opts_934_, 1);
v_component_2422_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_2423_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_2424_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_onlyDeps_2425_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2426_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_2427_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_2428_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_2429_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_2430_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2431_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_2432_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_2433_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_2434_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_2435_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_2436_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_2437_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_2438_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_2439_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_2440_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2441_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_2442_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_2443_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_2451_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2445_ = v_opts_934_;
v_isShared_2446_ = v_isSharedCheck_2451_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2443_);
lean_inc(v_incrLoadFileName_x3f_2442_);
lean_inc(v_incrSaveFileName_x3f_2441_);
lean_inc(v_errorOnKinds_2438_);
lean_inc(v_bcFileName_x3f_2436_);
lean_inc(v_cFileName_x3f_2435_);
lean_inc(v_ileanFileName_x3f_2434_);
lean_inc(v_oleanFileName_x3f_2433_);
lean_inc(v_setupFileName_x3f_2432_);
lean_inc(v_rootDir_x3f_2431_);
lean_inc(v_opts_2428_);
lean_inc(v_forwardedArgs_2421_);
lean_inc(v_leanOpts_2420_);
lean_dec(v_opts_934_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2451_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_leanOpts_2420_);
lean_ctor_set(v_reuseFailAlloc_2450_, 1, v_forwardedArgs_2421_);
lean_ctor_set(v_reuseFailAlloc_2450_, 2, v_opts_2428_);
lean_ctor_set(v_reuseFailAlloc_2450_, 3, v_rootDir_x3f_2431_);
lean_ctor_set(v_reuseFailAlloc_2450_, 4, v_setupFileName_x3f_2432_);
lean_ctor_set(v_reuseFailAlloc_2450_, 5, v_oleanFileName_x3f_2433_);
lean_ctor_set(v_reuseFailAlloc_2450_, 6, v_ileanFileName_x3f_2434_);
lean_ctor_set(v_reuseFailAlloc_2450_, 7, v_cFileName_x3f_2435_);
lean_ctor_set(v_reuseFailAlloc_2450_, 8, v_bcFileName_x3f_2436_);
lean_ctor_set(v_reuseFailAlloc_2450_, 9, v_errorOnKinds_2438_);
lean_ctor_set(v_reuseFailAlloc_2450_, 10, v_incrSaveFileName_x3f_2441_);
lean_ctor_set(v_reuseFailAlloc_2450_, 11, v_incrLoadFileName_x3f_2442_);
lean_ctor_set(v_reuseFailAlloc_2450_, 12, v_incrHeaderSaveFileName_x3f_2443_);
lean_ctor_set_uint8(v_reuseFailAlloc_2450_, sizeof(void*)*13 + 8, v_component_2422_);
lean_ctor_set_uint8(v_reuseFailAlloc_2450_, sizeof(void*)*13 + 9, v_printPrefix_2423_);
lean_ctor_set_uint8(v_reuseFailAlloc_2450_, sizeof(void*)*13 + 10, v_printLibDir_2424_);
lean_ctor_set_uint8(v_reuseFailAlloc_2450_, sizeof(void*)*13 + 12, v_onlyDeps_2425_);
lean_ctor_set_uint8(v_reuseFailAlloc_2450_, sizeof(void*)*13 + 13, v_onlySrcDeps_2426_);
lean_ctor_set_uint8(v_reuseFailAlloc_2450_, sizeof(void*)*13 + 14, v_depsJson_2427_);
lean_ctor_set_uint32(v_reuseFailAlloc_2450_, sizeof(void*)*13, v_trustLevel_2429_);
lean_ctor_set_uint32(v_reuseFailAlloc_2450_, sizeof(void*)*13 + 4, v_numThreads_2430_);
lean_ctor_set_uint8(v_reuseFailAlloc_2450_, sizeof(void*)*13 + 15, v_jsonOutput_2437_);
lean_ctor_set_uint8(v_reuseFailAlloc_2450_, sizeof(void*)*13 + 16, v_printStats_2439_);
lean_ctor_set_uint8(v_reuseFailAlloc_2450_, sizeof(void*)*13 + 17, v_run_2440_);
v___x_2448_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2449_; 
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*13 + 11, v___x_1177_);
v___x_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2448_);
return v___x_2449_;
}
}
}
}
else
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27));
v___x_2453_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2452_, v_optArg_x3f_936_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2515_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2456_ = v___x_2453_;
v_isShared_2457_ = v_isSharedCheck_2515_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2453_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2515_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2458_ = lean_unsigned_to_nat(0u);
v___x_2459_ = lean_string_utf8_byte_size(v_a_2454_);
lean_inc(v_a_2454_);
v___x_2460_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2460_, 0, v_a_2454_);
lean_ctor_set(v___x_2460_, 1, v___x_2458_);
lean_ctor_set(v___x_2460_, 2, v___x_2459_);
v___x_2461_ = l_String_Slice_toNat_x3f(v___x_2460_);
lean_dec_ref_known(v___x_2460_, 3);
if (lean_obj_tag(v___x_2461_) == 1)
{
lean_object* v_val_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; 
v_val_2462_ = lean_ctor_get(v___x_2461_, 0);
lean_inc(v_val_2462_);
lean_dec_ref_known(v___x_2461_, 1);
v___x_2463_ = lean_unsigned_to_nat(4u);
v___x_2464_ = lean_unsigned_to_nat(2u);
v___x_2465_ = lean_nat_shiftr(v_val_2462_, v___x_2464_);
lean_dec(v_val_2462_);
v___x_2466_ = lean_nat_mul(v___x_2465_, v___x_2463_);
lean_dec(v___x_2465_);
v___x_2467_ = lean_unsigned_to_nat(1024u);
v___x_2468_ = lean_nat_mul(v___x_2466_, v___x_2467_);
lean_dec(v___x_2466_);
v___x_2469_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28, &l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28_once, _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28);
v___x_2470_ = lean_nat_dec_lt(v___x_2468_, v___x_2469_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
lean_dec(v___x_2468_);
lean_del_object(v___x_2456_);
lean_dec(v_a_2454_);
lean_dec_ref(v_opts_934_);
v___x_2471_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29));
v___x_2472_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2471_);
lean_dec_ref(v___x_2472_);
goto v___jp_977_;
}
else
{
size_t v___x_2473_; lean_object* v___x_2474_; lean_object* v_leanOpts_2475_; lean_object* v_forwardedArgs_2476_; uint8_t v_component_2477_; uint8_t v_printPrefix_2478_; uint8_t v_printLibDir_2479_; uint8_t v_useStdin_2480_; uint8_t v_onlyDeps_2481_; uint8_t v_onlySrcDeps_2482_; uint8_t v_depsJson_2483_; lean_object* v_opts_2484_; uint32_t v_trustLevel_2485_; uint32_t v_numThreads_2486_; lean_object* v_rootDir_x3f_2487_; lean_object* v_setupFileName_x3f_2488_; lean_object* v_oleanFileName_x3f_2489_; lean_object* v_ileanFileName_x3f_2490_; lean_object* v_cFileName_x3f_2491_; lean_object* v_bcFileName_x3f_2492_; uint8_t v_jsonOutput_2493_; lean_object* v_errorOnKinds_2494_; uint8_t v_printStats_2495_; uint8_t v_run_2496_; lean_object* v_incrSaveFileName_x3f_2497_; lean_object* v_incrLoadFileName_x3f_2498_; lean_object* v_incrHeaderSaveFileName_x3f_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2512_; 
v___x_2473_ = lean_usize_of_nat(v___x_2468_);
lean_dec(v___x_2468_);
v___x_2474_ = lean_internal_set_thread_stack_size(v___x_2473_);
v_leanOpts_2475_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_2476_ = lean_ctor_get(v_opts_934_, 1);
v_component_2477_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_2478_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_2479_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_2480_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_2481_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2482_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_2483_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_2484_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_2485_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_2486_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2487_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_2488_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_2489_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_2490_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_2491_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_2492_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_2493_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_2494_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_2495_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_2496_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2497_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_2498_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_2499_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_2512_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2501_ = v_opts_934_;
v_isShared_2502_ = v_isSharedCheck_2512_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2499_);
lean_inc(v_incrLoadFileName_x3f_2498_);
lean_inc(v_incrSaveFileName_x3f_2497_);
lean_inc(v_errorOnKinds_2494_);
lean_inc(v_bcFileName_x3f_2492_);
lean_inc(v_cFileName_x3f_2491_);
lean_inc(v_ileanFileName_x3f_2490_);
lean_inc(v_oleanFileName_x3f_2489_);
lean_inc(v_setupFileName_x3f_2488_);
lean_inc(v_rootDir_x3f_2487_);
lean_inc(v_opts_2484_);
lean_inc(v_forwardedArgs_2476_);
lean_inc(v_leanOpts_2475_);
lean_dec(v_opts_934_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2512_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2507_; 
v___x_2503_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30));
v___x_2504_ = lean_string_append(v___x_2503_, v_a_2454_);
lean_dec(v_a_2454_);
v___x_2505_ = lean_array_push(v_forwardedArgs_2476_, v___x_2504_);
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 1, v___x_2505_);
v___x_2507_ = v___x_2501_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_leanOpts_2475_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v___x_2505_);
lean_ctor_set(v_reuseFailAlloc_2511_, 2, v_opts_2484_);
lean_ctor_set(v_reuseFailAlloc_2511_, 3, v_rootDir_x3f_2487_);
lean_ctor_set(v_reuseFailAlloc_2511_, 4, v_setupFileName_x3f_2488_);
lean_ctor_set(v_reuseFailAlloc_2511_, 5, v_oleanFileName_x3f_2489_);
lean_ctor_set(v_reuseFailAlloc_2511_, 6, v_ileanFileName_x3f_2490_);
lean_ctor_set(v_reuseFailAlloc_2511_, 7, v_cFileName_x3f_2491_);
lean_ctor_set(v_reuseFailAlloc_2511_, 8, v_bcFileName_x3f_2492_);
lean_ctor_set(v_reuseFailAlloc_2511_, 9, v_errorOnKinds_2494_);
lean_ctor_set(v_reuseFailAlloc_2511_, 10, v_incrSaveFileName_x3f_2497_);
lean_ctor_set(v_reuseFailAlloc_2511_, 11, v_incrLoadFileName_x3f_2498_);
lean_ctor_set(v_reuseFailAlloc_2511_, 12, v_incrHeaderSaveFileName_x3f_2499_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, sizeof(void*)*13 + 8, v_component_2477_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, sizeof(void*)*13 + 9, v_printPrefix_2478_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, sizeof(void*)*13 + 10, v_printLibDir_2479_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, sizeof(void*)*13 + 11, v_useStdin_2480_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, sizeof(void*)*13 + 12, v_onlyDeps_2481_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, sizeof(void*)*13 + 13, v_onlySrcDeps_2482_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, sizeof(void*)*13 + 14, v_depsJson_2483_);
lean_ctor_set_uint32(v_reuseFailAlloc_2511_, sizeof(void*)*13, v_trustLevel_2485_);
lean_ctor_set_uint32(v_reuseFailAlloc_2511_, sizeof(void*)*13 + 4, v_numThreads_2486_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, sizeof(void*)*13 + 15, v_jsonOutput_2493_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, sizeof(void*)*13 + 16, v_printStats_2495_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, sizeof(void*)*13 + 17, v_run_2496_);
v___x_2507_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
lean_object* v___x_2509_; 
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 0, v___x_2507_);
v___x_2509_ = v___x_2456_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2507_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
}
else
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
lean_dec(v___x_2461_);
lean_del_object(v___x_2456_);
lean_dec(v_a_2454_);
lean_dec_ref(v_opts_934_);
v___x_2513_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31));
v___x_2514_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2513_);
lean_dec_ref(v___x_2514_);
goto v___jp_974_;
}
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
lean_dec_ref(v_opts_934_);
v_a_2516_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2516_);
lean_dec_ref_known(v___x_2453_, 1);
v___x_2520_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2521_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2520_);
lean_dec_ref(v___x_2521_);
goto v___jp_2517_;
v___jp_2517_:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2518_ = lean_io_error_to_string(v_a_2516_);
v___x_2519_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2518_);
lean_dec_ref(v___x_2519_);
goto v___jp_971_;
}
}
}
}
else
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32));
v___x_2523_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2522_, v_optArg_x3f_936_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2564_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2526_ = v___x_2523_;
v_isShared_2527_ = v_isSharedCheck_2564_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2523_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2564_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v_leanOpts_2528_; lean_object* v_forwardedArgs_2529_; uint8_t v_component_2530_; uint8_t v_printPrefix_2531_; uint8_t v_printLibDir_2532_; uint8_t v_useStdin_2533_; uint8_t v_onlyDeps_2534_; uint8_t v_onlySrcDeps_2535_; uint8_t v_depsJson_2536_; lean_object* v_opts_2537_; uint32_t v_trustLevel_2538_; uint32_t v_numThreads_2539_; lean_object* v_rootDir_x3f_2540_; lean_object* v_setupFileName_x3f_2541_; lean_object* v_oleanFileName_x3f_2542_; lean_object* v_ileanFileName_x3f_2543_; lean_object* v_cFileName_x3f_2544_; uint8_t v_jsonOutput_2545_; lean_object* v_errorOnKinds_2546_; uint8_t v_printStats_2547_; uint8_t v_run_2548_; lean_object* v_incrSaveFileName_x3f_2549_; lean_object* v_incrLoadFileName_x3f_2550_; lean_object* v_incrHeaderSaveFileName_x3f_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2562_; 
v_leanOpts_2528_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_2529_ = lean_ctor_get(v_opts_934_, 1);
v_component_2530_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_2531_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_2532_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_2533_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_2534_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2535_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_2536_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_2537_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_2538_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_2539_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2540_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_2541_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_2542_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_2543_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_2544_ = lean_ctor_get(v_opts_934_, 7);
v_jsonOutput_2545_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_2546_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_2547_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_2548_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2549_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_2550_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_2551_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_2562_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_2562_ == 0)
{
lean_object* v_unused_2563_; 
v_unused_2563_ = lean_ctor_get(v_opts_934_, 8);
lean_dec(v_unused_2563_);
v___x_2553_ = v_opts_934_;
v_isShared_2554_ = v_isSharedCheck_2562_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2551_);
lean_inc(v_incrLoadFileName_x3f_2550_);
lean_inc(v_incrSaveFileName_x3f_2549_);
lean_inc(v_errorOnKinds_2546_);
lean_inc(v_cFileName_x3f_2544_);
lean_inc(v_ileanFileName_x3f_2543_);
lean_inc(v_oleanFileName_x3f_2542_);
lean_inc(v_setupFileName_x3f_2541_);
lean_inc(v_rootDir_x3f_2540_);
lean_inc(v_opts_2537_);
lean_inc(v_forwardedArgs_2529_);
lean_inc(v_leanOpts_2528_);
lean_dec(v_opts_934_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2562_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2555_; lean_object* v___x_2557_; 
v___x_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2555_, 0, v_a_2524_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 8, v___x_2555_);
v___x_2557_ = v___x_2553_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_leanOpts_2528_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_forwardedArgs_2529_);
lean_ctor_set(v_reuseFailAlloc_2561_, 2, v_opts_2537_);
lean_ctor_set(v_reuseFailAlloc_2561_, 3, v_rootDir_x3f_2540_);
lean_ctor_set(v_reuseFailAlloc_2561_, 4, v_setupFileName_x3f_2541_);
lean_ctor_set(v_reuseFailAlloc_2561_, 5, v_oleanFileName_x3f_2542_);
lean_ctor_set(v_reuseFailAlloc_2561_, 6, v_ileanFileName_x3f_2543_);
lean_ctor_set(v_reuseFailAlloc_2561_, 7, v_cFileName_x3f_2544_);
lean_ctor_set(v_reuseFailAlloc_2561_, 8, v___x_2555_);
lean_ctor_set(v_reuseFailAlloc_2561_, 9, v_errorOnKinds_2546_);
lean_ctor_set(v_reuseFailAlloc_2561_, 10, v_incrSaveFileName_x3f_2549_);
lean_ctor_set(v_reuseFailAlloc_2561_, 11, v_incrLoadFileName_x3f_2550_);
lean_ctor_set(v_reuseFailAlloc_2561_, 12, v_incrHeaderSaveFileName_x3f_2551_);
lean_ctor_set_uint8(v_reuseFailAlloc_2561_, sizeof(void*)*13 + 8, v_component_2530_);
lean_ctor_set_uint8(v_reuseFailAlloc_2561_, sizeof(void*)*13 + 9, v_printPrefix_2531_);
lean_ctor_set_uint8(v_reuseFailAlloc_2561_, sizeof(void*)*13 + 10, v_printLibDir_2532_);
lean_ctor_set_uint8(v_reuseFailAlloc_2561_, sizeof(void*)*13 + 11, v_useStdin_2533_);
lean_ctor_set_uint8(v_reuseFailAlloc_2561_, sizeof(void*)*13 + 12, v_onlyDeps_2534_);
lean_ctor_set_uint8(v_reuseFailAlloc_2561_, sizeof(void*)*13 + 13, v_onlySrcDeps_2535_);
lean_ctor_set_uint8(v_reuseFailAlloc_2561_, sizeof(void*)*13 + 14, v_depsJson_2536_);
lean_ctor_set_uint32(v_reuseFailAlloc_2561_, sizeof(void*)*13, v_trustLevel_2538_);
lean_ctor_set_uint32(v_reuseFailAlloc_2561_, sizeof(void*)*13 + 4, v_numThreads_2539_);
lean_ctor_set_uint8(v_reuseFailAlloc_2561_, sizeof(void*)*13 + 15, v_jsonOutput_2545_);
lean_ctor_set_uint8(v_reuseFailAlloc_2561_, sizeof(void*)*13 + 16, v_printStats_2547_);
lean_ctor_set_uint8(v_reuseFailAlloc_2561_, sizeof(void*)*13 + 17, v_run_2548_);
v___x_2557_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2559_; 
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 0, v___x_2557_);
v___x_2559_ = v___x_2526_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2557_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
lean_dec_ref(v_opts_934_);
v_a_2565_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2565_);
lean_dec_ref_known(v___x_2523_, 1);
v___x_2569_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2570_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2569_);
lean_dec_ref(v___x_2570_);
goto v___jp_2566_;
v___jp_2566_:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2567_ = lean_io_error_to_string(v_a_2565_);
v___x_2568_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2567_);
lean_dec_ref(v___x_2568_);
goto v___jp_1135_;
}
}
}
}
else
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2571_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33));
v___x_2572_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2571_, v_optArg_x3f_936_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2613_; 
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2575_ = v___x_2572_;
v_isShared_2576_ = v_isSharedCheck_2613_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2572_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2613_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v_leanOpts_2577_; lean_object* v_forwardedArgs_2578_; uint8_t v_component_2579_; uint8_t v_printPrefix_2580_; uint8_t v_printLibDir_2581_; uint8_t v_useStdin_2582_; uint8_t v_onlyDeps_2583_; uint8_t v_onlySrcDeps_2584_; uint8_t v_depsJson_2585_; lean_object* v_opts_2586_; uint32_t v_trustLevel_2587_; uint32_t v_numThreads_2588_; lean_object* v_rootDir_x3f_2589_; lean_object* v_setupFileName_x3f_2590_; lean_object* v_oleanFileName_x3f_2591_; lean_object* v_ileanFileName_x3f_2592_; lean_object* v_bcFileName_x3f_2593_; uint8_t v_jsonOutput_2594_; lean_object* v_errorOnKinds_2595_; uint8_t v_printStats_2596_; uint8_t v_run_2597_; lean_object* v_incrSaveFileName_x3f_2598_; lean_object* v_incrLoadFileName_x3f_2599_; lean_object* v_incrHeaderSaveFileName_x3f_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2611_; 
v_leanOpts_2577_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_2578_ = lean_ctor_get(v_opts_934_, 1);
v_component_2579_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_2580_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_2581_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_2582_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_2583_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2584_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_2585_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_2586_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_2587_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_numThreads_2588_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2589_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_2590_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_2591_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_2592_ = lean_ctor_get(v_opts_934_, 6);
v_bcFileName_x3f_2593_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_2594_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_2595_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_2596_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_2597_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2598_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_2599_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_2600_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_2611_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_2611_ == 0)
{
lean_object* v_unused_2612_; 
v_unused_2612_ = lean_ctor_get(v_opts_934_, 7);
lean_dec(v_unused_2612_);
v___x_2602_ = v_opts_934_;
v_isShared_2603_ = v_isSharedCheck_2611_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2600_);
lean_inc(v_incrLoadFileName_x3f_2599_);
lean_inc(v_incrSaveFileName_x3f_2598_);
lean_inc(v_errorOnKinds_2595_);
lean_inc(v_bcFileName_x3f_2593_);
lean_inc(v_ileanFileName_x3f_2592_);
lean_inc(v_oleanFileName_x3f_2591_);
lean_inc(v_setupFileName_x3f_2590_);
lean_inc(v_rootDir_x3f_2589_);
lean_inc(v_opts_2586_);
lean_inc(v_forwardedArgs_2578_);
lean_inc(v_leanOpts_2577_);
lean_dec(v_opts_934_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2611_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2604_; lean_object* v___x_2606_; 
v___x_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2604_, 0, v_a_2573_);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 7, v___x_2604_);
v___x_2606_ = v___x_2602_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_leanOpts_2577_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_forwardedArgs_2578_);
lean_ctor_set(v_reuseFailAlloc_2610_, 2, v_opts_2586_);
lean_ctor_set(v_reuseFailAlloc_2610_, 3, v_rootDir_x3f_2589_);
lean_ctor_set(v_reuseFailAlloc_2610_, 4, v_setupFileName_x3f_2590_);
lean_ctor_set(v_reuseFailAlloc_2610_, 5, v_oleanFileName_x3f_2591_);
lean_ctor_set(v_reuseFailAlloc_2610_, 6, v_ileanFileName_x3f_2592_);
lean_ctor_set(v_reuseFailAlloc_2610_, 7, v___x_2604_);
lean_ctor_set(v_reuseFailAlloc_2610_, 8, v_bcFileName_x3f_2593_);
lean_ctor_set(v_reuseFailAlloc_2610_, 9, v_errorOnKinds_2595_);
lean_ctor_set(v_reuseFailAlloc_2610_, 10, v_incrSaveFileName_x3f_2598_);
lean_ctor_set(v_reuseFailAlloc_2610_, 11, v_incrLoadFileName_x3f_2599_);
lean_ctor_set(v_reuseFailAlloc_2610_, 12, v_incrHeaderSaveFileName_x3f_2600_);
lean_ctor_set_uint8(v_reuseFailAlloc_2610_, sizeof(void*)*13 + 8, v_component_2579_);
lean_ctor_set_uint8(v_reuseFailAlloc_2610_, sizeof(void*)*13 + 9, v_printPrefix_2580_);
lean_ctor_set_uint8(v_reuseFailAlloc_2610_, sizeof(void*)*13 + 10, v_printLibDir_2581_);
lean_ctor_set_uint8(v_reuseFailAlloc_2610_, sizeof(void*)*13 + 11, v_useStdin_2582_);
lean_ctor_set_uint8(v_reuseFailAlloc_2610_, sizeof(void*)*13 + 12, v_onlyDeps_2583_);
lean_ctor_set_uint8(v_reuseFailAlloc_2610_, sizeof(void*)*13 + 13, v_onlySrcDeps_2584_);
lean_ctor_set_uint8(v_reuseFailAlloc_2610_, sizeof(void*)*13 + 14, v_depsJson_2585_);
lean_ctor_set_uint32(v_reuseFailAlloc_2610_, sizeof(void*)*13, v_trustLevel_2587_);
lean_ctor_set_uint32(v_reuseFailAlloc_2610_, sizeof(void*)*13 + 4, v_numThreads_2588_);
lean_ctor_set_uint8(v_reuseFailAlloc_2610_, sizeof(void*)*13 + 15, v_jsonOutput_2594_);
lean_ctor_set_uint8(v_reuseFailAlloc_2610_, sizeof(void*)*13 + 16, v_printStats_2596_);
lean_ctor_set_uint8(v_reuseFailAlloc_2610_, sizeof(void*)*13 + 17, v_run_2597_);
v___x_2606_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
lean_object* v___x_2608_; 
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 0, v___x_2606_);
v___x_2608_ = v___x_2575_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2606_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
lean_dec_ref(v_opts_934_);
v_a_2614_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_a_2614_);
lean_dec_ref_known(v___x_2572_, 1);
v___x_2618_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2619_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2618_);
lean_dec_ref(v___x_2619_);
goto v___jp_2615_;
v___jp_2615_:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2616_ = lean_io_error_to_string(v_a_2614_);
v___x_2617_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2616_);
lean_dec_ref(v___x_2617_);
goto v___jp_965_;
}
}
}
}
else
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
lean_dec(v_optArg_x3f_936_);
lean_dec_ref(v_opts_934_);
v___x_2620_ = l___private_Lean_Shell_0__Lean_featuresString;
v___x_2621_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2620_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2629_; 
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2629_ == 0)
{
lean_object* v_unused_2630_; 
v_unused_2630_ = lean_ctor_get(v___x_2621_, 0);
lean_dec(v_unused_2630_);
v___x_2623_ = v___x_2621_;
v_isShared_2624_ = v_isSharedCheck_2629_;
goto v_resetjp_2622_;
}
else
{
lean_dec(v___x_2621_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2629_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2625_; lean_object* v___x_2627_; 
v___x_2625_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2624_ == 0)
{
lean_ctor_set_tag(v___x_2623_, 1);
lean_ctor_set(v___x_2623_, 0, v___x_2625_);
v___x_2627_ = v___x_2623_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2625_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v_a_2631_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_a_2631_);
lean_dec_ref_known(v___x_2621_, 1);
v___x_2635_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2636_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2635_);
lean_dec_ref(v___x_2636_);
goto v___jp_2632_;
v___jp_2632_:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2633_ = lean_io_error_to_string(v_a_2631_);
v___x_2634_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2633_);
lean_dec_ref(v___x_2634_);
goto v___jp_1141_;
}
}
}
}
else
{
lean_object* v___x_2637_; 
lean_dec(v_optArg_x3f_936_);
lean_dec_ref(v_opts_934_);
v___x_2637_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1165_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2645_; 
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2645_ == 0)
{
lean_object* v_unused_2646_; 
v_unused_2646_ = lean_ctor_get(v___x_2637_, 0);
lean_dec(v_unused_2646_);
v___x_2639_ = v___x_2637_;
v_isShared_2640_ = v_isSharedCheck_2645_;
goto v_resetjp_2638_;
}
else
{
lean_dec(v___x_2637_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2645_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2641_; lean_object* v___x_2643_; 
v___x_2641_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2640_ == 0)
{
lean_ctor_set_tag(v___x_2639_, 1);
lean_ctor_set(v___x_2639_, 0, v___x_2641_);
v___x_2643_ = v___x_2639_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2641_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v_a_2647_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2647_);
lean_dec_ref_known(v___x_2637_, 1);
v___x_2651_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2652_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2651_);
lean_dec_ref(v___x_2652_);
goto v___jp_2648_;
v___jp_2648_:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2649_ = lean_io_error_to_string(v_a_2647_);
v___x_2650_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2649_);
lean_dec_ref(v___x_2650_);
goto v___jp_959_;
}
}
}
}
else
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
lean_dec(v_optArg_x3f_936_);
lean_dec_ref(v_opts_934_);
v___x_2653_ = l_Lean_githash;
v___x_2654_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2653_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2662_; 
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2662_ == 0)
{
lean_object* v_unused_2663_; 
v_unused_2663_ = lean_ctor_get(v___x_2654_, 0);
lean_dec(v_unused_2663_);
v___x_2656_ = v___x_2654_;
v_isShared_2657_ = v_isSharedCheck_2662_;
goto v_resetjp_2655_;
}
else
{
lean_dec(v___x_2654_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2662_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2658_; lean_object* v___x_2660_; 
v___x_2658_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2657_ == 0)
{
lean_ctor_set_tag(v___x_2656_, 1);
lean_ctor_set(v___x_2656_, 0, v___x_2658_);
v___x_2660_ = v___x_2656_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v_a_2664_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2664_);
lean_dec_ref_known(v___x_2654_, 1);
v___x_2668_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2669_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2668_);
lean_dec_ref(v___x_2669_);
goto v___jp_2665_;
v___jp_2665_:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2666_ = lean_io_error_to_string(v_a_2664_);
v___x_2667_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2666_);
lean_dec_ref(v___x_2667_);
goto v___jp_1147_;
}
}
}
}
else
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
lean_dec(v_optArg_x3f_936_);
lean_dec_ref(v_opts_934_);
v___x_2670_ = l___private_Lean_Shell_0__Lean_shortVersionString;
v___x_2671_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2670_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2679_; 
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2679_ == 0)
{
lean_object* v_unused_2680_; 
v_unused_2680_ = lean_ctor_get(v___x_2671_, 0);
lean_dec(v_unused_2680_);
v___x_2673_ = v___x_2671_;
v_isShared_2674_ = v_isSharedCheck_2679_;
goto v_resetjp_2672_;
}
else
{
lean_dec(v___x_2671_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2679_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2675_; lean_object* v___x_2677_; 
v___x_2675_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2674_ == 0)
{
lean_ctor_set_tag(v___x_2673_, 1);
lean_ctor_set(v___x_2673_, 0, v___x_2675_);
v___x_2677_ = v___x_2673_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2675_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
else
{
lean_object* v_a_2681_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v_a_2681_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2671_, 1);
v___x_2685_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2686_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2685_);
lean_dec_ref(v___x_2686_);
goto v___jp_2682_;
v___jp_2682_:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2683_ = lean_io_error_to_string(v_a_2681_);
v___x_2684_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2683_);
lean_dec_ref(v___x_2684_);
goto v___jp_953_;
}
}
}
}
else
{
lean_object* v___x_2687_; lean_object* v___x_2688_; 
lean_dec(v_optArg_x3f_936_);
lean_dec_ref(v_opts_934_);
v___x_2687_ = l___private_Lean_Shell_0__Lean_versionHeader;
v___x_2688_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2687_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2696_; 
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2696_ == 0)
{
lean_object* v_unused_2697_; 
v_unused_2697_ = lean_ctor_get(v___x_2688_, 0);
lean_dec(v_unused_2697_);
v___x_2690_ = v___x_2688_;
v_isShared_2691_ = v_isSharedCheck_2696_;
goto v_resetjp_2689_;
}
else
{
lean_dec(v___x_2688_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2696_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2692_; lean_object* v___x_2694_; 
v___x_2692_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2691_ == 0)
{
lean_ctor_set_tag(v___x_2690_, 1);
lean_ctor_set(v___x_2690_, 0, v___x_2692_);
v___x_2694_ = v___x_2690_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2692_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v_a_2698_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_a_2698_);
lean_dec_ref_known(v___x_2688_, 1);
v___x_2702_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2703_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2702_);
lean_dec_ref(v___x_2703_);
goto v___jp_2699_;
v___jp_2699_:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = lean_io_error_to_string(v_a_2698_);
v___x_2701_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2700_);
lean_dec_ref(v___x_2701_);
goto v___jp_1153_;
}
}
}
}
else
{
lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2704_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34));
v___x_2705_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2704_, v_optArg_x3f_936_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2759_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2708_ = v___x_2705_;
v_isShared_2709_ = v_isSharedCheck_2759_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2705_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2759_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2710_ = lean_unsigned_to_nat(0u);
v___x_2711_ = lean_string_utf8_byte_size(v_a_2706_);
lean_inc(v_a_2706_);
v___x_2712_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2712_, 0, v_a_2706_);
lean_ctor_set(v___x_2712_, 1, v___x_2710_);
lean_ctor_set(v___x_2712_, 2, v___x_2711_);
v___x_2713_ = l_String_Slice_toNat_x3f(v___x_2712_);
lean_dec_ref_known(v___x_2712_, 3);
if (lean_obj_tag(v___x_2713_) == 1)
{
lean_object* v_val_2714_; lean_object* v___x_2715_; uint8_t v___x_2716_; 
v_val_2714_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_val_2714_);
lean_dec_ref_known(v___x_2713_, 1);
v___x_2715_ = lean_cstr_to_nat("4294967296");
v___x_2716_ = lean_nat_dec_lt(v_val_2714_, v___x_2715_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
lean_dec(v_val_2714_);
lean_del_object(v___x_2708_);
lean_dec(v_a_2706_);
lean_dec_ref(v_opts_934_);
v___x_2717_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__35));
v___x_2718_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2717_);
lean_dec_ref(v___x_2718_);
goto v___jp_947_;
}
else
{
lean_object* v_leanOpts_2719_; lean_object* v_forwardedArgs_2720_; uint8_t v_component_2721_; uint8_t v_printPrefix_2722_; uint8_t v_printLibDir_2723_; uint8_t v_useStdin_2724_; uint8_t v_onlyDeps_2725_; uint8_t v_onlySrcDeps_2726_; uint8_t v_depsJson_2727_; lean_object* v_opts_2728_; uint32_t v_trustLevel_2729_; lean_object* v_rootDir_x3f_2730_; lean_object* v_setupFileName_x3f_2731_; lean_object* v_oleanFileName_x3f_2732_; lean_object* v_ileanFileName_x3f_2733_; lean_object* v_cFileName_x3f_2734_; lean_object* v_bcFileName_x3f_2735_; uint8_t v_jsonOutput_2736_; lean_object* v_errorOnKinds_2737_; uint8_t v_printStats_2738_; uint8_t v_run_2739_; lean_object* v_incrSaveFileName_x3f_2740_; lean_object* v_incrLoadFileName_x3f_2741_; lean_object* v_incrHeaderSaveFileName_x3f_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2756_; 
v_leanOpts_2719_ = lean_ctor_get(v_opts_934_, 0);
v_forwardedArgs_2720_ = lean_ctor_get(v_opts_934_, 1);
v_component_2721_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 8);
v_printPrefix_2722_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 9);
v_printLibDir_2723_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 10);
v_useStdin_2724_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 11);
v_onlyDeps_2725_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2726_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 13);
v_depsJson_2727_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 14);
v_opts_2728_ = lean_ctor_get(v_opts_934_, 2);
v_trustLevel_2729_ = lean_ctor_get_uint32(v_opts_934_, sizeof(void*)*13);
v_rootDir_x3f_2730_ = lean_ctor_get(v_opts_934_, 3);
v_setupFileName_x3f_2731_ = lean_ctor_get(v_opts_934_, 4);
v_oleanFileName_x3f_2732_ = lean_ctor_get(v_opts_934_, 5);
v_ileanFileName_x3f_2733_ = lean_ctor_get(v_opts_934_, 6);
v_cFileName_x3f_2734_ = lean_ctor_get(v_opts_934_, 7);
v_bcFileName_x3f_2735_ = lean_ctor_get(v_opts_934_, 8);
v_jsonOutput_2736_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 15);
v_errorOnKinds_2737_ = lean_ctor_get(v_opts_934_, 9);
v_printStats_2738_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 16);
v_run_2739_ = lean_ctor_get_uint8(v_opts_934_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2740_ = lean_ctor_get(v_opts_934_, 10);
v_incrLoadFileName_x3f_2741_ = lean_ctor_get(v_opts_934_, 11);
v_incrHeaderSaveFileName_x3f_2742_ = lean_ctor_get(v_opts_934_, 12);
v_isSharedCheck_2756_ = !lean_is_exclusive(v_opts_934_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2744_ = v_opts_934_;
v_isShared_2745_ = v_isSharedCheck_2756_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2742_);
lean_inc(v_incrLoadFileName_x3f_2741_);
lean_inc(v_incrSaveFileName_x3f_2740_);
lean_inc(v_errorOnKinds_2737_);
lean_inc(v_bcFileName_x3f_2735_);
lean_inc(v_cFileName_x3f_2734_);
lean_inc(v_ileanFileName_x3f_2733_);
lean_inc(v_oleanFileName_x3f_2732_);
lean_inc(v_setupFileName_x3f_2731_);
lean_inc(v_rootDir_x3f_2730_);
lean_inc(v_opts_2728_);
lean_inc(v_forwardedArgs_2720_);
lean_inc(v_leanOpts_2719_);
lean_dec(v_opts_934_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2756_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
uint32_t v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2751_; 
v___x_2746_ = lean_uint32_of_nat(v_val_2714_);
lean_dec(v_val_2714_);
v___x_2747_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__36));
v___x_2748_ = lean_string_append(v___x_2747_, v_a_2706_);
lean_dec(v_a_2706_);
v___x_2749_ = lean_array_push(v_forwardedArgs_2720_, v___x_2748_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 1, v___x_2749_);
v___x_2751_ = v___x_2744_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_leanOpts_2719_);
lean_ctor_set(v_reuseFailAlloc_2755_, 1, v___x_2749_);
lean_ctor_set(v_reuseFailAlloc_2755_, 2, v_opts_2728_);
lean_ctor_set(v_reuseFailAlloc_2755_, 3, v_rootDir_x3f_2730_);
lean_ctor_set(v_reuseFailAlloc_2755_, 4, v_setupFileName_x3f_2731_);
lean_ctor_set(v_reuseFailAlloc_2755_, 5, v_oleanFileName_x3f_2732_);
lean_ctor_set(v_reuseFailAlloc_2755_, 6, v_ileanFileName_x3f_2733_);
lean_ctor_set(v_reuseFailAlloc_2755_, 7, v_cFileName_x3f_2734_);
lean_ctor_set(v_reuseFailAlloc_2755_, 8, v_bcFileName_x3f_2735_);
lean_ctor_set(v_reuseFailAlloc_2755_, 9, v_errorOnKinds_2737_);
lean_ctor_set(v_reuseFailAlloc_2755_, 10, v_incrSaveFileName_x3f_2740_);
lean_ctor_set(v_reuseFailAlloc_2755_, 11, v_incrLoadFileName_x3f_2741_);
lean_ctor_set(v_reuseFailAlloc_2755_, 12, v_incrHeaderSaveFileName_x3f_2742_);
lean_ctor_set_uint8(v_reuseFailAlloc_2755_, sizeof(void*)*13 + 8, v_component_2721_);
lean_ctor_set_uint8(v_reuseFailAlloc_2755_, sizeof(void*)*13 + 9, v_printPrefix_2722_);
lean_ctor_set_uint8(v_reuseFailAlloc_2755_, sizeof(void*)*13 + 10, v_printLibDir_2723_);
lean_ctor_set_uint8(v_reuseFailAlloc_2755_, sizeof(void*)*13 + 11, v_useStdin_2724_);
lean_ctor_set_uint8(v_reuseFailAlloc_2755_, sizeof(void*)*13 + 12, v_onlyDeps_2725_);
lean_ctor_set_uint8(v_reuseFailAlloc_2755_, sizeof(void*)*13 + 13, v_onlySrcDeps_2726_);
lean_ctor_set_uint8(v_reuseFailAlloc_2755_, sizeof(void*)*13 + 14, v_depsJson_2727_);
lean_ctor_set_uint32(v_reuseFailAlloc_2755_, sizeof(void*)*13, v_trustLevel_2729_);
lean_ctor_set_uint8(v_reuseFailAlloc_2755_, sizeof(void*)*13 + 15, v_jsonOutput_2736_);
lean_ctor_set_uint8(v_reuseFailAlloc_2755_, sizeof(void*)*13 + 16, v_printStats_2738_);
lean_ctor_set_uint8(v_reuseFailAlloc_2755_, sizeof(void*)*13 + 17, v_run_2739_);
v___x_2751_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
lean_object* v___x_2753_; 
lean_ctor_set_uint32(v___x_2751_, sizeof(void*)*13 + 4, v___x_2746_);
if (v_isShared_2709_ == 0)
{
lean_ctor_set(v___x_2708_, 0, v___x_2751_);
v___x_2753_ = v___x_2708_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2751_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
}
else
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
lean_dec(v___x_2713_);
lean_del_object(v___x_2708_);
lean_dec(v_a_2706_);
lean_dec_ref(v_opts_934_);
v___x_2757_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__37));
v___x_2758_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2757_);
lean_dec_ref(v___x_2758_);
goto v___jp_944_;
}
}
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
lean_dec_ref(v_opts_934_);
v_a_2760_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2760_);
lean_dec_ref_known(v___x_2705_, 1);
v___x_2764_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2765_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2764_);
lean_dec_ref(v___x_2765_);
goto v___jp_2761_;
v___jp_2761_:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = lean_io_error_to_string(v_a_2760_);
v___x_2763_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2762_);
lean_dec_ref(v___x_2763_);
goto v___jp_941_;
}
}
}
}
else
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
lean_dec(v_optArg_x3f_936_);
v___x_2766_ = lean_internal_set_exit_on_panic(v___x_1157_);
v___x_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2767_, 0, v_opts_934_);
return v___x_2767_;
}
v___jp_938_:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
return v___x_940_;
}
v___jp_941_:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_943_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_942_);
lean_dec_ref(v___x_943_);
goto v___jp_938_;
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
v___x_951_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
return v___x_952_;
}
v___jp_953_:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_955_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_954_);
lean_dec_ref(v___x_955_);
goto v___jp_950_;
}
v___jp_956_:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
v___jp_959_:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_961_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_960_);
lean_dec_ref(v___x_961_);
goto v___jp_956_;
}
v___jp_962_:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
v___jp_965_:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_967_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_966_);
lean_dec_ref(v___x_967_);
goto v___jp_962_;
}
v___jp_968_:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
return v___x_970_;
}
v___jp_971_:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_973_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_972_);
lean_dec_ref(v___x_973_);
goto v___jp_968_;
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
v___x_981_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
return v___x_982_;
}
v___jp_983_:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_985_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_984_);
lean_dec_ref(v___x_985_);
goto v___jp_980_;
}
v___jp_986_:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
v___jp_989_:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_991_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_990_);
lean_dec_ref(v___x_991_);
goto v___jp_986_;
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
v___x_996_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
return v___x_997_;
}
v___jp_998_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1000_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_999_);
lean_dec_ref(v___x_1000_);
goto v___jp_995_;
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
v___x_1008_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
return v___x_1009_;
}
v___jp_1010_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1012_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1011_);
lean_dec_ref(v___x_1012_);
goto v___jp_1007_;
}
v___jp_1013_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
return v___x_1015_;
}
v___jp_1016_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1018_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1017_);
lean_dec_ref(v___x_1018_);
goto v___jp_1013_;
}
v___jp_1019_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
return v___x_1021_;
}
v___jp_1022_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1024_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1023_);
lean_dec_ref(v___x_1024_);
goto v___jp_1019_;
}
v___jp_1025_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
return v___x_1027_;
}
v___jp_1028_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1030_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1029_);
lean_dec_ref(v___x_1030_);
goto v___jp_1025_;
}
v___jp_1031_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
return v___x_1033_;
}
v___jp_1034_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1036_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1035_);
lean_dec_ref(v___x_1036_);
goto v___jp_1031_;
}
v___jp_1037_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
return v___x_1039_;
}
v___jp_1040_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1042_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1041_);
lean_dec_ref(v___x_1042_);
goto v___jp_1037_;
}
v___jp_1043_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
return v___x_1045_;
}
v___jp_1046_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1048_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1047_);
lean_dec_ref(v___x_1048_);
goto v___jp_1043_;
}
v___jp_1049_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = lean_io_error_to_string(v___y_1050_);
v___x_1052_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1051_);
lean_dec_ref(v___x_1052_);
goto v___jp_1046_;
}
v___jp_1053_:
{
uint8_t v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = 1;
v___x_1055_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1054_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1063_; 
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; 
v_unused_1064_ = lean_ctor_get(v___x_1055_, 0);
lean_dec(v_unused_1064_);
v___x_1057_ = v___x_1055_;
v_isShared_1058_ = v_isSharedCheck_1063_;
goto v_resetjp_1056_;
}
else
{
lean_dec(v___x_1055_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1063_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1059_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_1058_ == 0)
{
lean_ctor_set_tag(v___x_1057_, 1);
lean_ctor_set(v___x_1057_, 0, v___x_1059_);
v___x_1061_ = v___x_1057_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v_a_1065_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___x_1055_, 1);
v___x_1066_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1067_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1066_);
lean_dec_ref(v___x_1067_);
v___y_1050_ = v_a_1065_;
goto v___jp_1049_;
}
}
v___jp_1068_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__0));
v___x_1070_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1069_);
lean_dec_ref(v___x_1070_);
goto v___jp_1053_;
}
v___jp_1071_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
return v___x_1073_;
}
v___jp_1074_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1076_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1075_);
lean_dec_ref(v___x_1076_);
goto v___jp_1071_;
}
v___jp_1077_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
return v___x_1079_;
}
v___jp_1080_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1082_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1081_);
lean_dec_ref(v___x_1082_);
goto v___jp_1077_;
}
v___jp_1083_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
return v___x_1085_;
}
v___jp_1086_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1088_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1087_);
lean_dec_ref(v___x_1088_);
goto v___jp_1083_;
}
v___jp_1089_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
return v___x_1091_;
}
v___jp_1092_:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1094_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1093_);
lean_dec_ref(v___x_1094_);
goto v___jp_1089_;
}
v___jp_1095_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = lean_io_error_to_string(v___y_1096_);
v___x_1098_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1097_);
lean_dec_ref(v___x_1098_);
goto v___jp_1092_;
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
v___x_1115_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
return v___x_1116_;
}
v___jp_1117_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1119_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1118_);
lean_dec_ref(v___x_1119_);
goto v___jp_1114_;
}
v___jp_1120_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
return v___x_1122_;
}
v___jp_1123_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1125_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1124_);
lean_dec_ref(v___x_1125_);
goto v___jp_1120_;
}
v___jp_1126_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
return v___x_1128_;
}
v___jp_1129_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1131_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1130_);
lean_dec_ref(v___x_1131_);
goto v___jp_1126_;
}
v___jp_1132_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
return v___x_1134_;
}
v___jp_1135_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1137_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1136_);
lean_dec_ref(v___x_1137_);
goto v___jp_1132_;
}
v___jp_1138_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
return v___x_1140_;
}
v___jp_1141_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1143_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1142_);
lean_dec_ref(v___x_1143_);
goto v___jp_1138_;
}
v___jp_1144_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
return v___x_1146_;
}
v___jp_1147_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1149_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1148_);
lean_dec_ref(v___x_1149_);
goto v___jp_1144_;
}
v___jp_1150_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
return v___x_1152_;
}
v___jp_1153_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1155_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1154_);
lean_dec_ref(v___x_1155_);
goto v___jp_1150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed(lean_object* v_opts_2768_, lean_object* v_opt_2769_, lean_object* v_optArg_x3f_2770_, lean_object* v_a_2771_){
_start:
{
uint32_t v_opt_boxed_2772_; lean_object* v_res_2773_; 
v_opt_boxed_2772_ = lean_unbox_uint32(v_opt_2769_);
lean_dec(v_opt_2769_);
v_res_2773_ = lean_shell_options_process(v_opts_2768_, v_opt_boxed_2772_, v_optArg_x3f_2770_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(lean_object* v_opts_2774_, lean_object* v_opt_2775_){
_start:
{
lean_object* v_name_2776_; lean_object* v_defValue_2777_; lean_object* v_map_2778_; lean_object* v___x_2779_; 
v_name_2776_ = lean_ctor_get(v_opt_2775_, 0);
v_defValue_2777_ = lean_ctor_get(v_opt_2775_, 1);
v_map_2778_ = lean_ctor_get(v_opts_2774_, 0);
v___x_2779_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2778_, v_name_2776_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_inc(v_defValue_2777_);
return v_defValue_2777_;
}
else
{
lean_object* v_val_2780_; 
v_val_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_val_2780_);
lean_dec_ref_known(v___x_2779_, 1);
if (lean_obj_tag(v_val_2780_) == 3)
{
lean_object* v_v_2781_; 
v_v_2781_ = lean_ctor_get(v_val_2780_, 0);
lean_inc(v_v_2781_);
lean_dec_ref_known(v_val_2780_, 1);
return v_v_2781_;
}
else
{
lean_dec(v_val_2780_);
lean_inc(v_defValue_2777_);
return v_defValue_2777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___boxed(lean_object* v_opts_2782_, lean_object* v_opt_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_opts_2782_, v_opt_2783_);
lean_dec_ref(v_opt_2783_);
lean_dec_ref(v_opts_2782_);
return v_res_2784_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2787_ = lean_string_utf8_byte_size(v___x_2786_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(lean_object* v_s_2788_){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; uint8_t v___x_2792_; 
v___x_2789_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2790_ = lean_string_utf8_byte_size(v_s_2788_);
v___x_2791_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1);
v___x_2792_ = lean_nat_dec_le(v___x_2791_, v___x_2790_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2793_; 
lean_dec_ref(v_s_2788_);
v___x_2793_ = lean_box(0);
return v___x_2793_;
}
else
{
lean_object* v___x_2794_; uint8_t v___x_2795_; 
v___x_2794_ = lean_unsigned_to_nat(0u);
v___x_2795_ = lean_string_memcmp(v_s_2788_, v___x_2789_, v___x_2794_, v___x_2794_, v___x_2791_);
if (v___x_2795_ == 0)
{
lean_object* v___x_2796_; 
lean_dec_ref(v_s_2788_);
v___x_2796_ = lean_box(0);
return v___x_2796_;
}
else
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
lean_inc_ref(v_s_2788_);
v___x_2797_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2797_, 0, v_s_2788_);
lean_ctor_set(v___x_2797_, 1, v___x_2794_);
lean_ctor_set(v___x_2797_, 2, v___x_2790_);
v___x_2798_ = l_String_Slice_pos_x21(v___x_2797_, v___x_2791_);
lean_dec_ref_known(v___x_2797_, 3);
v___x_2799_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2799_, 0, v_s_2788_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
lean_ctor_set(v___x_2799_, 2, v___x_2790_);
v___x_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
return v___x_2800_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(lean_object* v_s_2801_, lean_object* v_pat_2802_){
_start:
{
lean_object* v___x_2803_; 
v___x_2803_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v_s_2801_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___boxed(lean_object* v_s_2804_, lean_object* v_pat_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(v_s_2804_, v_pat_2805_);
lean_dec_ref(v_pat_2805_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object* v_x_2807_, lean_object* v_x_2808_, lean_object* v_v_2809_){
_start:
{
lean_inc_ref(v_v_2809_);
return v_v_2809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object* v_x_2810_, lean_object* v_x_2811_, lean_object* v_v_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l___private_Lean_Shell_0__Lean_shellMain___lam__0(v_x_2810_, v_x_2811_, v_v_2812_);
lean_dec_ref(v_v_2812_);
lean_dec_ref(v_x_2811_);
lean_dec(v_x_2810_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1(lean_object* v___x_2817_, lean_object* v___x_2818_, lean_object* v_mainModuleName_2819_, lean_object* v_a_2820_, uint8_t v___x_2821_, lean_object* v___x_2822_, lean_object* v_fileName_2823_, lean_object* v___x_2824_, lean_object* v___x_2825_, lean_object* v___x_2826_, lean_object* v___x_2827_, lean_object* v___x_2828_, lean_object* v___x_2829_, lean_object* v___x_2830_, lean_object* v___x_2831_, uint8_t v_run_2832_){
_start:
{
lean_object* v_a_2835_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v_env_2843_; lean_object* v___x_2844_; uint8_t v___x_2845_; lean_object* v_fileName_2847_; lean_object* v_fileMap_2848_; lean_object* v_currRecDepth_2849_; lean_object* v_ref_2850_; lean_object* v_currNamespace_2851_; lean_object* v_openDecls_2852_; lean_object* v_initHeartbeats_2853_; lean_object* v_maxHeartbeats_2854_; lean_object* v_quotContext_2855_; lean_object* v_currMacroScope_2856_; lean_object* v_cancelTk_x3f_2857_; uint8_t v_suppressElabErrors_2858_; lean_object* v_inheritedTraceOptions_2859_; lean_object* v___y_2860_; uint8_t v___y_2892_; uint8_t v___x_2912_; 
v___x_2838_ = lean_io_get_num_heartbeats();
v___x_2839_ = lean_st_mk_ref(v___x_2817_);
v___x_2840_ = l_Lean_inheritedTraceOptions;
v___x_2841_ = lean_st_ref_get(v___x_2840_);
v___x_2842_ = lean_st_ref_get(v___x_2839_);
v_env_2843_ = lean_ctor_get(v___x_2842_, 0);
lean_inc_ref(v_env_2843_);
lean_dec(v___x_2842_);
v___x_2844_ = l_Lean_diagnostics;
v___x_2845_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v___x_2818_, v___x_2844_);
v___x_2912_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2843_);
lean_dec_ref(v_env_2843_);
if (v___x_2912_ == 0)
{
if (v___x_2845_ == 0)
{
lean_dec_ref(v___x_2822_);
lean_inc(v___x_2839_);
lean_inc(v___x_2827_);
v_fileName_2847_ = v_fileName_2823_;
v_fileMap_2848_ = v___x_2824_;
v_currRecDepth_2849_ = v___x_2825_;
v_ref_2850_ = v___x_2826_;
v_currNamespace_2851_ = v___x_2827_;
v_openDecls_2852_ = v___x_2828_;
v_initHeartbeats_2853_ = v___x_2838_;
v_maxHeartbeats_2854_ = v___x_2829_;
v_quotContext_2855_ = v___x_2827_;
v_currMacroScope_2856_ = v___x_2830_;
v_cancelTk_x3f_2857_ = v___x_2831_;
v_suppressElabErrors_2858_ = v_run_2832_;
v_inheritedTraceOptions_2859_ = v___x_2841_;
v___y_2860_ = v___x_2839_;
goto v___jp_2846_;
}
else
{
v___y_2892_ = v___x_2912_;
goto v___jp_2891_;
}
}
else
{
v___y_2892_ = v___x_2845_;
goto v___jp_2891_;
}
v___jp_2834_:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = lean_mk_io_user_error(v_a_2835_);
v___x_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2836_);
return v___x_2837_;
}
v___jp_2846_:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2861_ = l_Lean_maxRecDepth;
v___x_2862_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_2818_, v___x_2861_);
v___x_2863_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2863_, 0, v_fileName_2847_);
lean_ctor_set(v___x_2863_, 1, v_fileMap_2848_);
lean_ctor_set(v___x_2863_, 2, v___x_2818_);
lean_ctor_set(v___x_2863_, 3, v_currRecDepth_2849_);
lean_ctor_set(v___x_2863_, 4, v___x_2862_);
lean_ctor_set(v___x_2863_, 5, v_ref_2850_);
lean_ctor_set(v___x_2863_, 6, v_currNamespace_2851_);
lean_ctor_set(v___x_2863_, 7, v_openDecls_2852_);
lean_ctor_set(v___x_2863_, 8, v_initHeartbeats_2853_);
lean_ctor_set(v___x_2863_, 9, v_maxHeartbeats_2854_);
lean_ctor_set(v___x_2863_, 10, v_quotContext_2855_);
lean_ctor_set(v___x_2863_, 11, v_currMacroScope_2856_);
lean_ctor_set(v___x_2863_, 12, v_cancelTk_x3f_2857_);
lean_ctor_set(v___x_2863_, 13, v_inheritedTraceOptions_2859_);
lean_ctor_set_uint8(v___x_2863_, sizeof(void*)*14, v___x_2845_);
lean_ctor_set_uint8(v___x_2863_, sizeof(void*)*14 + 1, v_suppressElabErrors_2858_);
v___x_2864_ = l_Lean_Compiler_LCNF_emitC(v_mainModuleName_2819_, v___x_2863_, v___y_2860_);
lean_dec(v___y_2860_);
lean_dec_ref_known(v___x_2863_, 14);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref_known(v___x_2864_, 1);
v___x_2866_ = lean_st_ref_get(v___x_2839_);
lean_dec(v___x_2839_);
lean_dec(v___x_2866_);
v___x_2867_ = lean_string_to_utf8(v_a_2865_);
lean_dec(v_a_2865_);
v___x_2868_ = lean_io_prim_handle_write(v_a_2820_, v___x_2867_);
lean_dec_ref(v___x_2867_);
return v___x_2868_;
}
else
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2890_; 
lean_dec(v___x_2839_);
v_a_2869_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2871_ = v___x_2864_;
v_isShared_2872_ = v_isSharedCheck_2890_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2864_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2890_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
if (lean_obj_tag(v_a_2869_) == 0)
{
lean_object* v_msg_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2877_; 
v_msg_2873_ = lean_ctor_get(v_a_2869_, 1);
lean_inc_ref(v_msg_2873_);
lean_dec_ref_known(v_a_2869_, 2);
v___x_2874_ = l_Lean_MessageData_toString(v_msg_2873_);
v___x_2875_ = lean_mk_io_user_error(v___x_2874_);
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v___x_2875_);
v___x_2877_ = v___x_2871_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v___x_2875_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
else
{
lean_object* v_id_2879_; lean_object* v___x_2880_; 
lean_del_object(v___x_2871_);
v_id_2879_ = lean_ctor_get(v_a_2869_, 0);
lean_inc(v_id_2879_);
lean_dec_ref_known(v_a_2869_, 2);
v___x_2880_ = l_Lean_InternalExceptionId_getName(v_id_2879_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
lean_dec(v_id_2879_);
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2881_);
lean_dec_ref_known(v___x_2880_, 1);
v___x_2882_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__0));
v___x_2883_ = l_Lean_Name_toString(v_a_2881_, v___x_2821_);
v___x_2884_ = lean_string_append(v___x_2882_, v___x_2883_);
lean_dec_ref(v___x_2883_);
v_a_2835_ = v___x_2884_;
goto v___jp_2834_;
}
else
{
lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
lean_dec_ref_known(v___x_2880_, 1);
v___x_2885_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__1));
v___x_2886_ = l_Nat_reprFast(v_id_2879_);
v___x_2887_ = lean_string_append(v___x_2885_, v___x_2886_);
lean_dec_ref(v___x_2886_);
v___x_2888_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__2));
v___x_2889_ = lean_string_append(v___x_2887_, v___x_2888_);
v_a_2835_ = v___x_2889_;
goto v___jp_2834_;
}
}
}
}
}
v___jp_2891_:
{
if (v___y_2892_ == 0)
{
lean_object* v___x_2893_; lean_object* v_env_2894_; lean_object* v_nextMacroScope_2895_; lean_object* v_ngen_2896_; lean_object* v_auxDeclNGen_2897_; lean_object* v_traceState_2898_; lean_object* v_messages_2899_; lean_object* v_infoState_2900_; lean_object* v_snapshotTasks_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2910_; 
v___x_2893_ = lean_st_ref_take(v___x_2839_);
v_env_2894_ = lean_ctor_get(v___x_2893_, 0);
v_nextMacroScope_2895_ = lean_ctor_get(v___x_2893_, 1);
v_ngen_2896_ = lean_ctor_get(v___x_2893_, 2);
v_auxDeclNGen_2897_ = lean_ctor_get(v___x_2893_, 3);
v_traceState_2898_ = lean_ctor_get(v___x_2893_, 4);
v_messages_2899_ = lean_ctor_get(v___x_2893_, 6);
v_infoState_2900_ = lean_ctor_get(v___x_2893_, 7);
v_snapshotTasks_2901_ = lean_ctor_get(v___x_2893_, 8);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2910_ == 0)
{
lean_object* v_unused_2911_; 
v_unused_2911_ = lean_ctor_get(v___x_2893_, 5);
lean_dec(v_unused_2911_);
v___x_2903_ = v___x_2893_;
v_isShared_2904_ = v_isSharedCheck_2910_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_snapshotTasks_2901_);
lean_inc(v_infoState_2900_);
lean_inc(v_messages_2899_);
lean_inc(v_traceState_2898_);
lean_inc(v_auxDeclNGen_2897_);
lean_inc(v_ngen_2896_);
lean_inc(v_nextMacroScope_2895_);
lean_inc(v_env_2894_);
lean_dec(v___x_2893_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2910_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2905_; lean_object* v___x_2907_; 
v___x_2905_ = l_Lean_Kernel_enableDiag(v_env_2894_, v___x_2845_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 5, v___x_2822_);
lean_ctor_set(v___x_2903_, 0, v___x_2905_);
v___x_2907_ = v___x_2903_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2905_);
lean_ctor_set(v_reuseFailAlloc_2909_, 1, v_nextMacroScope_2895_);
lean_ctor_set(v_reuseFailAlloc_2909_, 2, v_ngen_2896_);
lean_ctor_set(v_reuseFailAlloc_2909_, 3, v_auxDeclNGen_2897_);
lean_ctor_set(v_reuseFailAlloc_2909_, 4, v_traceState_2898_);
lean_ctor_set(v_reuseFailAlloc_2909_, 5, v___x_2822_);
lean_ctor_set(v_reuseFailAlloc_2909_, 6, v_messages_2899_);
lean_ctor_set(v_reuseFailAlloc_2909_, 7, v_infoState_2900_);
lean_ctor_set(v_reuseFailAlloc_2909_, 8, v_snapshotTasks_2901_);
v___x_2907_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
lean_object* v___x_2908_; 
v___x_2908_ = lean_st_ref_set(v___x_2839_, v___x_2907_);
lean_inc(v___x_2839_);
lean_inc(v___x_2827_);
v_fileName_2847_ = v_fileName_2823_;
v_fileMap_2848_ = v___x_2824_;
v_currRecDepth_2849_ = v___x_2825_;
v_ref_2850_ = v___x_2826_;
v_currNamespace_2851_ = v___x_2827_;
v_openDecls_2852_ = v___x_2828_;
v_initHeartbeats_2853_ = v___x_2838_;
v_maxHeartbeats_2854_ = v___x_2829_;
v_quotContext_2855_ = v___x_2827_;
v_currMacroScope_2856_ = v___x_2830_;
v_cancelTk_x3f_2857_ = v___x_2831_;
v_suppressElabErrors_2858_ = v_run_2832_;
v_inheritedTraceOptions_2859_ = v___x_2841_;
v___y_2860_ = v___x_2839_;
goto v___jp_2846_;
}
}
}
else
{
lean_dec_ref(v___x_2822_);
lean_inc(v___x_2839_);
lean_inc(v___x_2827_);
v_fileName_2847_ = v_fileName_2823_;
v_fileMap_2848_ = v___x_2824_;
v_currRecDepth_2849_ = v___x_2825_;
v_ref_2850_ = v___x_2826_;
v_currNamespace_2851_ = v___x_2827_;
v_openDecls_2852_ = v___x_2828_;
v_initHeartbeats_2853_ = v___x_2838_;
v_maxHeartbeats_2854_ = v___x_2829_;
v_quotContext_2855_ = v___x_2827_;
v_currMacroScope_2856_ = v___x_2830_;
v_cancelTk_x3f_2857_ = v___x_2831_;
v_suppressElabErrors_2858_ = v_run_2832_;
v_inheritedTraceOptions_2859_ = v___x_2841_;
v___y_2860_ = v___x_2839_;
goto v___jp_2846_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed(lean_object** _args){
lean_object* v___x_2913_ = _args[0];
lean_object* v___x_2914_ = _args[1];
lean_object* v_mainModuleName_2915_ = _args[2];
lean_object* v_a_2916_ = _args[3];
lean_object* v___x_2917_ = _args[4];
lean_object* v___x_2918_ = _args[5];
lean_object* v_fileName_2919_ = _args[6];
lean_object* v___x_2920_ = _args[7];
lean_object* v___x_2921_ = _args[8];
lean_object* v___x_2922_ = _args[9];
lean_object* v___x_2923_ = _args[10];
lean_object* v___x_2924_ = _args[11];
lean_object* v___x_2925_ = _args[12];
lean_object* v___x_2926_ = _args[13];
lean_object* v___x_2927_ = _args[14];
lean_object* v_run_2928_ = _args[15];
lean_object* v___y_2929_ = _args[16];
_start:
{
uint8_t v___x_22495__boxed_2930_; uint8_t v_run_boxed_2931_; lean_object* v_res_2932_; 
v___x_22495__boxed_2930_ = lean_unbox(v___x_2917_);
v_run_boxed_2931_ = lean_unbox(v_run_2928_);
v_res_2932_ = l___private_Lean_Shell_0__Lean_shellMain___lam__1(v___x_2913_, v___x_2914_, v_mainModuleName_2915_, v_a_2916_, v___x_22495__boxed_2930_, v___x_2918_, v_fileName_2919_, v___x_2920_, v___x_2921_, v___x_2922_, v___x_2923_, v___x_2924_, v___x_2925_, v___x_2926_, v___x_2927_, v_run_boxed_2931_);
lean_dec(v_a_2916_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(lean_object* v_val_2933_, lean_object* v_a_2934_, lean_object* v_b_2935_){
_start:
{
lean_object* v_str_2936_; lean_object* v_startInclusive_2937_; lean_object* v_endExclusive_2938_; lean_object* v___x_2939_; uint8_t v___x_2940_; 
v_str_2936_ = lean_ctor_get(v_val_2933_, 0);
v_startInclusive_2937_ = lean_ctor_get(v_val_2933_, 1);
v_endExclusive_2938_ = lean_ctor_get(v_val_2933_, 2);
v___x_2939_ = lean_nat_sub(v_endExclusive_2938_, v_startInclusive_2937_);
v___x_2940_ = lean_nat_dec_eq(v_a_2934_, v___x_2939_);
lean_dec(v___x_2939_);
if (v___x_2940_ == 0)
{
lean_object* v___x_2941_; uint32_t v___x_2942_; uint32_t v___x_2943_; uint8_t v___x_2944_; 
v___x_2941_ = lean_nat_add(v_startInclusive_2937_, v_a_2934_);
v___x_2942_ = lean_string_utf8_get_fast(v_str_2936_, v___x_2941_);
v___x_2943_ = 10;
v___x_2944_ = lean_uint32_dec_eq(v___x_2942_, v___x_2943_);
if (v___x_2944_ == 0)
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
lean_dec(v_a_2934_);
v___x_2945_ = lean_box(0);
v___x_2946_ = lean_string_utf8_next_fast(v_str_2936_, v___x_2941_);
lean_dec(v___x_2941_);
v___x_2947_ = lean_nat_sub(v___x_2946_, v_startInclusive_2937_);
v_a_2934_ = v___x_2947_;
v_b_2935_ = v___x_2945_;
goto _start;
}
else
{
lean_object* v___x_2949_; 
lean_dec(v___x_2941_);
v___x_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2949_, 0, v_a_2934_);
return v___x_2949_;
}
}
else
{
lean_dec(v_a_2934_);
lean_inc(v_b_2935_);
return v_b_2935_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg___boxed(lean_object* v_val_2950_, lean_object* v_a_2951_, lean_object* v_b_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_2950_, v_a_2951_, v_b_2952_);
lean_dec(v_b_2952_);
lean_dec_ref(v_val_2950_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(lean_object* v_s_2954_){
_start:
{
uint32_t v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2956_ = 10;
v___x_2957_ = lean_string_push(v_s_2954_, v___x_2956_);
v___x_2958_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4___boxed(lean_object* v_s_2959_, lean_object* v_a_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_s_2959_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object* v_s_2962_){
_start:
{
uint32_t v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2964_ = 10;
v___x_2965_ = lean_string_push(v_s_2962_, v___x_2964_);
v___x_2966_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___boxed(lean_object* v_s_2967_, lean_object* v_a_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v_s_2967_);
return v_res_2969_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shellMain___closed__1(void){
_start:
{
lean_object* v___x_2971_; uint8_t v___x_2972_; 
v___x_2971_ = lean_box(0);
v___x_2972_ = lean_internal_has_address_sanitizer(v___x_2971_);
return v___x_2972_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__2(void){
_start:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2973_ = lean_box(0);
v___x_2974_ = lean_internal_get_option_overrides(v___x_2973_);
return v___x_2974_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__6(void){
_start:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2979_ = l_Lean_Options_empty;
v___x_2980_ = l_Lean_Core_getMaxHeartbeats(v___x_2979_);
return v___x_2980_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__7(void){
_start:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2981_ = lean_unsigned_to_nat(1u);
v___x_2982_ = l_Lean_firstFrontendMacroScope;
v___x_2983_ = lean_nat_add(v___x_2982_, v___x_2981_);
return v___x_2983_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__12(void){
_start:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2994_ = lean_unsigned_to_nat(32u);
v___x_2995_ = lean_mk_empty_array_with_capacity(v___x_2994_);
v___x_2996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2995_);
return v___x_2996_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13(void){
_start:
{
size_t v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_2997_ = ((size_t)5ULL);
v___x_2998_ = lean_unsigned_to_nat(0u);
v___x_2999_ = lean_unsigned_to_nat(32u);
v___x_3000_ = lean_mk_empty_array_with_capacity(v___x_2999_);
v___x_3001_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__12, &l___private_Lean_Shell_0__Lean_shellMain___closed__12_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__12);
v___x_3002_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
lean_ctor_set(v___x_3002_, 1, v___x_3000_);
lean_ctor_set(v___x_3002_, 2, v___x_2998_);
lean_ctor_set(v___x_3002_, 3, v___x_2998_);
lean_ctor_set_usize(v___x_3002_, 4, v___x_2997_);
return v___x_3002_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14(void){
_start:
{
lean_object* v___x_3003_; uint64_t v___x_3004_; lean_object* v___x_3005_; 
v___x_3003_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__13, &l___private_Lean_Shell_0__Lean_shellMain___closed__13_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13);
v___x_3004_ = 0ULL;
v___x_3005_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3005_, 0, v___x_3003_);
lean_ctor_set_uint64(v___x_3005_, sizeof(void*)*1, v___x_3004_);
return v___x_3005_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__15(void){
_start:
{
lean_object* v___x_3006_; 
v___x_3006_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3006_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16(void){
_start:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3007_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__15, &l___private_Lean_Shell_0__Lean_shellMain___closed__15_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__15);
v___x_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
return v___x_3008_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__17(void){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3009_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__16, &l___private_Lean_Shell_0__Lean_shellMain___closed__16_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16);
v___x_3010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
lean_ctor_set(v___x_3010_, 1, v___x_3009_);
return v___x_3010_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__18(void){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3011_ = l_Lean_NameSet_empty;
v___x_3012_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__13, &l___private_Lean_Shell_0__Lean_shellMain___closed__13_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13);
v___x_3013_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
lean_ctor_set(v___x_3013_, 1, v___x_3012_);
lean_ctor_set(v___x_3013_, 2, v___x_3011_);
return v___x_3013_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__19(void){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; uint8_t v___x_3016_; lean_object* v___x_3017_; 
v___x_3014_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__13, &l___private_Lean_Shell_0__Lean_shellMain___closed__13_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13);
v___x_3015_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__16, &l___private_Lean_Shell_0__Lean_shellMain___closed__16_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16);
v___x_3016_ = 1;
v___x_3017_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3017_, 0, v___x_3015_);
lean_ctor_set(v___x_3017_, 1, v___x_3015_);
lean_ctor_set(v___x_3017_, 2, v___x_3014_);
lean_ctor_set_uint8(v___x_3017_, sizeof(void*)*3, v___x_3016_);
return v___x_3017_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__24(void){
_start:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3023_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__23));
v___x_3024_ = lean_string_utf8_byte_size(v___x_3023_);
return v___x_3024_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__25(void){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3025_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__24, &l___private_Lean_Shell_0__Lean_shellMain___closed__24_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__24);
v___x_3026_ = lean_unsigned_to_nat(0u);
v___x_3027_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__23));
v___x_3028_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3027_);
lean_ctor_set(v___x_3028_, 1, v___x_3026_);
lean_ctor_set(v___x_3028_, 2, v___x_3025_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* lean_shell_main(lean_object* v_args_3032_, lean_object* v_opts_3033_){
_start:
{
lean_object* v_fns_3042_; uint8_t v_printPrefix_3061_; 
v_printPrefix_3061_ = lean_ctor_get_uint8(v_opts_3033_, sizeof(void*)*13 + 9);
if (v_printPrefix_3061_ == 0)
{
uint8_t v_printLibDir_3062_; 
v_printLibDir_3062_ = lean_ctor_get_uint8(v_opts_3033_, sizeof(void*)*13 + 10);
if (v_printLibDir_3062_ == 0)
{
lean_object* v_leanOpts_3063_; lean_object* v_forwardedArgs_3064_; uint8_t v_component_3065_; uint8_t v_useStdin_3066_; uint8_t v_onlyDeps_3067_; uint8_t v_onlySrcDeps_3068_; uint8_t v_depsJson_3069_; uint32_t v_trustLevel_3070_; lean_object* v_rootDir_x3f_3071_; lean_object* v_setupFileName_x3f_3072_; lean_object* v_oleanFileName_x3f_3073_; lean_object* v_ileanFileName_x3f_3074_; lean_object* v_cFileName_x3f_3075_; lean_object* v_bcFileName_x3f_3076_; uint8_t v_jsonOutput_3077_; lean_object* v_errorOnKinds_3078_; uint8_t v_printStats_3079_; uint8_t v_run_3080_; lean_object* v_incrSaveFileName_x3f_3081_; lean_object* v_incrLoadFileName_x3f_3082_; lean_object* v_incrHeaderSaveFileName_x3f_3083_; lean_object* v___f_3084_; lean_object* v___y_3086_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; uint8_t v___x_3128_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v_mainModuleName_3135_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v_contents_3236_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v_str_3266_; lean_object* v_startInclusive_3267_; lean_object* v_endExclusive_3268_; lean_object* v___y_3269_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v_fileName_3368_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3406_; lean_object* v___y_3407_; uint8_t v___y_3438_; lean_object* v_fst_3439_; lean_object* v_snd_3440_; uint8_t v___y_3442_; lean_object* v___x_3472_; lean_object* v_maxMemory_3473_; lean_object* v___x_3474_; uint8_t v___x_3475_; 
v_leanOpts_3063_ = lean_ctor_get(v_opts_3033_, 0);
lean_inc_ref(v_leanOpts_3063_);
v_forwardedArgs_3064_ = lean_ctor_get(v_opts_3033_, 1);
lean_inc_ref(v_forwardedArgs_3064_);
v_component_3065_ = lean_ctor_get_uint8(v_opts_3033_, sizeof(void*)*13 + 8);
v_useStdin_3066_ = lean_ctor_get_uint8(v_opts_3033_, sizeof(void*)*13 + 11);
v_onlyDeps_3067_ = lean_ctor_get_uint8(v_opts_3033_, sizeof(void*)*13 + 12);
v_onlySrcDeps_3068_ = lean_ctor_get_uint8(v_opts_3033_, sizeof(void*)*13 + 13);
v_depsJson_3069_ = lean_ctor_get_uint8(v_opts_3033_, sizeof(void*)*13 + 14);
v_trustLevel_3070_ = lean_ctor_get_uint32(v_opts_3033_, sizeof(void*)*13);
v_rootDir_x3f_3071_ = lean_ctor_get(v_opts_3033_, 3);
lean_inc(v_rootDir_x3f_3071_);
v_setupFileName_x3f_3072_ = lean_ctor_get(v_opts_3033_, 4);
lean_inc(v_setupFileName_x3f_3072_);
v_oleanFileName_x3f_3073_ = lean_ctor_get(v_opts_3033_, 5);
lean_inc(v_oleanFileName_x3f_3073_);
v_ileanFileName_x3f_3074_ = lean_ctor_get(v_opts_3033_, 6);
lean_inc(v_ileanFileName_x3f_3074_);
v_cFileName_x3f_3075_ = lean_ctor_get(v_opts_3033_, 7);
lean_inc(v_cFileName_x3f_3075_);
v_bcFileName_x3f_3076_ = lean_ctor_get(v_opts_3033_, 8);
lean_inc(v_bcFileName_x3f_3076_);
v_jsonOutput_3077_ = lean_ctor_get_uint8(v_opts_3033_, sizeof(void*)*13 + 15);
v_errorOnKinds_3078_ = lean_ctor_get(v_opts_3033_, 9);
lean_inc_ref(v_errorOnKinds_3078_);
v_printStats_3079_ = lean_ctor_get_uint8(v_opts_3033_, sizeof(void*)*13 + 16);
v_run_3080_ = lean_ctor_get_uint8(v_opts_3033_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_3081_ = lean_ctor_get(v_opts_3033_, 10);
lean_inc(v_incrSaveFileName_x3f_3081_);
v_incrLoadFileName_x3f_3082_ = lean_ctor_get(v_opts_3033_, 11);
lean_inc(v_incrLoadFileName_x3f_3082_);
v_incrHeaderSaveFileName_x3f_3083_ = lean_ctor_get(v_opts_3033_, 12);
lean_inc(v_incrHeaderSaveFileName_x3f_3083_);
lean_dec_ref(v_opts_3033_);
v___f_3084_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__0));
v___x_3100_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__2, &l___private_Lean_Shell_0__Lean_shellMain___closed__2_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__2);
v___x_3101_ = l_Lean_Options_mergeBy(v___f_3084_, v_leanOpts_3063_, v___x_3100_);
v___x_3128_ = 1;
v___x_3472_ = l___private_Lean_Shell_0__Lean_maxMemory;
v_maxMemory_3473_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_3101_, v___x_3472_);
v___x_3474_ = lean_unsigned_to_nat(0u);
v___x_3475_ = lean_nat_dec_eq(v_maxMemory_3473_, v___x_3474_);
if (v___x_3475_ == 0)
{
size_t v___x_3476_; size_t v___x_3477_; size_t v___x_3478_; size_t v___x_3479_; lean_object* v___x_3480_; 
v___x_3476_ = lean_usize_of_nat(v_maxMemory_3473_);
lean_dec(v_maxMemory_3473_);
v___x_3477_ = ((size_t)10ULL);
v___x_3478_ = lean_usize_shift_left(v___x_3476_, v___x_3477_);
v___x_3479_ = lean_usize_shift_left(v___x_3478_, v___x_3477_);
v___x_3480_ = lean_internal_set_max_memory(v___x_3479_);
goto v___jp_3463_;
}
else
{
lean_dec(v_maxMemory_3473_);
goto v___jp_3463_;
}
v___jp_3085_:
{
lean_object* v___x_3087_; uint8_t v___x_3088_; 
v___x_3087_ = lean_display_cumulative_profiling_times();
v___x_3088_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__1, &l___private_Lean_Shell_0__Lean_shellMain___closed__1_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__1);
if (v___x_3088_ == 0)
{
if (lean_obj_tag(v___y_3086_) == 0)
{
if (v___x_3088_ == 0)
{
uint8_t v___x_3089_; lean_object* v___x_3090_; 
v___x_3089_ = 1;
v___x_3090_ = lean_io_exit(v___x_3089_);
return v___x_3090_;
}
else
{
goto v___jp_3038_;
}
}
else
{
lean_dec_ref_known(v___y_3086_, 1);
goto v___jp_3038_;
}
}
else
{
if (lean_obj_tag(v___y_3086_) == 0)
{
goto v___jp_3035_;
}
else
{
lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3098_; 
v_isSharedCheck_3098_ = !lean_is_exclusive(v___y_3086_);
if (v_isSharedCheck_3098_ == 0)
{
lean_object* v_unused_3099_; 
v_unused_3099_ = lean_ctor_get(v___y_3086_, 0);
lean_dec(v_unused_3099_);
v___x_3092_ = v___y_3086_;
v_isShared_3093_ = v_isSharedCheck_3098_;
goto v_resetjp_3091_;
}
else
{
lean_dec(v___y_3086_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3098_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
if (v___x_3088_ == 0)
{
lean_del_object(v___x_3092_);
goto v___jp_3035_;
}
else
{
lean_object* v___x_3094_; lean_object* v___x_3096_; 
v___x_3094_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3093_ == 0)
{
lean_ctor_set_tag(v___x_3092_, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3094_);
v___x_3096_ = v___x_3092_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3094_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
}
}
v___jp_3102_:
{
if (lean_obj_tag(v_bcFileName_x3f_3076_) == 1)
{
lean_object* v_val_3106_; lean_object* v___x_3107_; 
v_val_3106_ = lean_ctor_get(v_bcFileName_x3f_3076_, 0);
lean_inc(v_val_3106_);
lean_dec_ref_known(v_bcFileName_x3f_3076_, 1);
v___x_3107_ = lean_init_llvm();
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
lean_dec_ref_known(v___x_3107_, 1);
v___x_3108_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__3));
v___x_3109_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_emitLLVM___boxed), 4, 3);
lean_closure_set(v___x_3109_, 0, v___y_3105_);
lean_closure_set(v___x_3109_, 1, v___y_3103_);
lean_closure_set(v___x_3109_, 2, v_val_3106_);
v___x_3110_ = lean_box(0);
v___x_3111_ = l_Lean_profileitIOUnsafe___redArg(v___x_3108_, v___x_3101_, v___x_3109_, v___x_3110_);
lean_dec_ref(v___x_3101_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_dec_ref_known(v___x_3111_, 1);
v___y_3086_ = v___y_3104_;
goto v___jp_3085_;
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_dec(v___y_3104_);
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3111_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3111_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec(v_val_3106_);
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3104_);
lean_dec(v___y_3103_);
lean_dec_ref(v___x_3101_);
v_a_3120_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3107_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3107_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
else
{
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3103_);
lean_dec_ref(v___x_3101_);
lean_dec(v_bcFileName_x3f_3076_);
v___y_3086_ = v___y_3104_;
goto v___jp_3085_;
}
}
v___jp_3129_:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3136_ = lean_unsigned_to_nat(0u);
v___x_3137_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__4));
lean_inc(v_mainModuleName_3135_);
lean_inc_ref(v___x_3101_);
v___x_3138_ = l_Lean_Elab_runFrontend(v___y_3134_, v___x_3101_, v___y_3133_, v_mainModuleName_3135_, v_trustLevel_3070_, v_oleanFileName_x3f_3073_, v_ileanFileName_x3f_3074_, v_jsonOutput_3077_, v_errorOnKinds_3078_, v___x_3137_, v_printStats_3079_, v___y_3131_, v_incrSaveFileName_x3f_3081_, v_incrLoadFileName_x3f_3082_, v_incrHeaderSaveFileName_x3f_3083_);
lean_dec_ref(v_errorOnKinds_3078_);
lean_dec(v_ileanFileName_x3f_3074_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3206_; 
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3141_ = v___x_3138_;
v_isShared_3142_ = v_isSharedCheck_3206_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3138_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3206_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
if (lean_obj_tag(v_a_3139_) == 1)
{
if (v_run_3080_ == 0)
{
lean_del_object(v___x_3141_);
lean_dec(v___y_3132_);
if (lean_obj_tag(v_cFileName_x3f_3075_) == 1)
{
lean_object* v_val_3143_; lean_object* v_val_3144_; uint8_t v___x_3145_; lean_object* v___x_3146_; 
v_val_3143_ = lean_ctor_get(v_a_3139_, 0);
lean_inc(v_val_3143_);
v_val_3144_ = lean_ctor_get(v_cFileName_x3f_3075_, 0);
lean_inc(v_val_3144_);
lean_dec_ref_known(v_cFileName_x3f_3075_, 1);
v___x_3145_ = 1;
v___x_3146_ = lean_io_prim_handle_mk(v_val_3144_, v___x_3145_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___f_3167_; lean_object* v___x_3168_; 
lean_dec(v_val_3144_);
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_a_3147_);
lean_dec_ref_known(v___x_3146_, 1);
v___x_3148_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__5));
v___x_3149_ = l_Lean_instInhabitedFileMap_default;
v___x_3150_ = l_Lean_Options_empty;
v___x_3151_ = lean_box(0);
v___x_3152_ = lean_box(0);
v___x_3153_ = lean_box(0);
v___x_3154_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__6, &l___private_Lean_Shell_0__Lean_shellMain___closed__6_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__6);
v___x_3155_ = l_Lean_firstFrontendMacroScope;
v___x_3156_ = lean_box(0);
v___x_3157_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__7, &l___private_Lean_Shell_0__Lean_shellMain___closed__7_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__7);
v___x_3158_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__10));
v___x_3159_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__11));
v___x_3160_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__14, &l___private_Lean_Shell_0__Lean_shellMain___closed__14_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14);
v___x_3161_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__17, &l___private_Lean_Shell_0__Lean_shellMain___closed__17_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__17);
v___x_3162_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__18, &l___private_Lean_Shell_0__Lean_shellMain___closed__18_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__18);
v___x_3163_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__19, &l___private_Lean_Shell_0__Lean_shellMain___closed__19_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__19);
lean_inc(v_val_3143_);
v___x_3164_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3164_, 0, v_val_3143_);
lean_ctor_set(v___x_3164_, 1, v___x_3157_);
lean_ctor_set(v___x_3164_, 2, v___x_3158_);
lean_ctor_set(v___x_3164_, 3, v___x_3159_);
lean_ctor_set(v___x_3164_, 4, v___x_3160_);
lean_ctor_set(v___x_3164_, 5, v___x_3161_);
lean_ctor_set(v___x_3164_, 6, v___x_3162_);
lean_ctor_set(v___x_3164_, 7, v___x_3163_);
lean_ctor_set(v___x_3164_, 8, v___x_3137_);
v___x_3165_ = lean_box(v___x_3128_);
v___x_3166_ = lean_box(v_run_3080_);
lean_inc(v_mainModuleName_3135_);
v___f_3167_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed), 17, 16);
lean_closure_set(v___f_3167_, 0, v___x_3164_);
lean_closure_set(v___f_3167_, 1, v___x_3150_);
lean_closure_set(v___f_3167_, 2, v_mainModuleName_3135_);
lean_closure_set(v___f_3167_, 3, v_a_3147_);
lean_closure_set(v___f_3167_, 4, v___x_3165_);
lean_closure_set(v___f_3167_, 5, v___x_3161_);
lean_closure_set(v___f_3167_, 6, v___y_3130_);
lean_closure_set(v___f_3167_, 7, v___x_3149_);
lean_closure_set(v___f_3167_, 8, v___x_3136_);
lean_closure_set(v___f_3167_, 9, v___x_3151_);
lean_closure_set(v___f_3167_, 10, v___x_3152_);
lean_closure_set(v___f_3167_, 11, v___x_3153_);
lean_closure_set(v___f_3167_, 12, v___x_3154_);
lean_closure_set(v___f_3167_, 13, v___x_3155_);
lean_closure_set(v___f_3167_, 14, v___x_3156_);
lean_closure_set(v___f_3167_, 15, v___x_3166_);
v___x_3168_ = l_Lean_profileitIOUnsafe___redArg(v___x_3148_, v___x_3101_, v___f_3167_, v___x_3152_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_dec_ref_known(v___x_3168_, 1);
v___y_3103_ = v_mainModuleName_3135_;
v___y_3104_ = v_a_3139_;
v___y_3105_ = v_val_3143_;
goto v___jp_3102_;
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3176_; 
lean_dec(v_val_3143_);
lean_dec_ref_known(v_a_3139_, 1);
lean_dec(v_mainModuleName_3135_);
lean_dec_ref(v___x_3101_);
lean_dec(v_bcFileName_x3f_3076_);
v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3171_ = v___x_3168_;
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3168_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3174_; 
if (v_isShared_3172_ == 0)
{
v___x_3174_ = v___x_3171_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
}
else
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
lean_dec_ref_known(v___x_3146_, 1);
lean_dec(v_val_3143_);
lean_dec_ref_known(v_a_3139_, 1);
lean_dec(v_mainModuleName_3135_);
lean_dec_ref(v___y_3130_);
lean_dec_ref(v___x_3101_);
lean_dec(v_bcFileName_x3f_3076_);
v___x_3177_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__20));
v___x_3178_ = lean_string_append(v___x_3177_, v_val_3144_);
lean_dec(v_val_3144_);
v___x_3179_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__1));
v___x_3180_ = lean_string_append(v___x_3178_, v___x_3179_);
v___x_3181_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3180_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3189_; 
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3189_ == 0)
{
lean_object* v_unused_3190_; 
v_unused_3190_ = lean_ctor_get(v___x_3181_, 0);
lean_dec(v_unused_3190_);
v___x_3183_ = v___x_3181_;
v_isShared_3184_ = v_isSharedCheck_3189_;
goto v_resetjp_3182_;
}
else
{
lean_dec(v___x_3181_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3189_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3185_; lean_object* v___x_3187_; 
v___x_3185_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 0, v___x_3185_);
v___x_3187_ = v___x_3183_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
else
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3198_; 
v_a_3191_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3193_ = v___x_3181_;
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3181_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3196_; 
if (v_isShared_3194_ == 0)
{
v___x_3196_ = v___x_3193_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_a_3191_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
}
else
{
lean_object* v_val_3199_; 
lean_dec_ref(v___y_3130_);
lean_dec(v_cFileName_x3f_3075_);
v_val_3199_ = lean_ctor_get(v_a_3139_, 0);
lean_inc(v_val_3199_);
v___y_3103_ = v_mainModuleName_3135_;
v___y_3104_ = v_a_3139_;
v___y_3105_ = v_val_3199_;
goto v___jp_3102_;
}
}
else
{
lean_object* v_val_3200_; uint32_t v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3204_; 
lean_dec(v_mainModuleName_3135_);
lean_dec_ref(v___y_3130_);
lean_dec(v_bcFileName_x3f_3076_);
lean_dec(v_cFileName_x3f_3075_);
v_val_3200_ = lean_ctor_get(v_a_3139_, 0);
lean_inc(v_val_3200_);
lean_dec_ref_known(v_a_3139_, 1);
v___x_3201_ = lean_eval_main(v_val_3200_, v___x_3101_, v___y_3132_);
lean_dec(v___y_3132_);
lean_dec_ref(v___x_3101_);
lean_dec(v_val_3200_);
v___x_3202_ = lean_box_uint32(v___x_3201_);
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 0, v___x_3202_);
v___x_3204_ = v___x_3141_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3202_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
else
{
lean_del_object(v___x_3141_);
lean_dec(v_mainModuleName_3135_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3130_);
lean_dec_ref(v___x_3101_);
lean_dec(v_bcFileName_x3f_3076_);
lean_dec(v_cFileName_x3f_3075_);
v___y_3086_ = v_a_3139_;
goto v___jp_3085_;
}
}
}
else
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
lean_dec(v_mainModuleName_3135_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3130_);
lean_dec_ref(v___x_3101_);
lean_dec(v_bcFileName_x3f_3076_);
lean_dec(v_cFileName_x3f_3075_);
v_a_3207_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3209_ = v___x_3138_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3138_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3212_; 
if (v_isShared_3210_ == 0)
{
v___x_3212_ = v___x_3209_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3207_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
}
v___jp_3215_:
{
if (lean_obj_tag(v___y_3221_) == 0)
{
lean_object* v_a_3222_; 
v_a_3222_ = lean_ctor_get(v___y_3221_, 0);
lean_inc(v_a_3222_);
lean_dec_ref_known(v___y_3221_, 1);
v___y_3130_ = v___y_3216_;
v___y_3131_ = v___y_3217_;
v___y_3132_ = v___y_3218_;
v___y_3133_ = v___y_3219_;
v___y_3134_ = v___y_3220_;
v_mainModuleName_3135_ = v_a_3222_;
goto v___jp_3129_;
}
else
{
lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3230_; 
lean_dec_ref(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
lean_dec_ref(v___x_3101_);
lean_dec(v_incrHeaderSaveFileName_x3f_3083_);
lean_dec(v_incrLoadFileName_x3f_3082_);
lean_dec(v_incrSaveFileName_x3f_3081_);
lean_dec_ref(v_errorOnKinds_3078_);
lean_dec(v_bcFileName_x3f_3076_);
lean_dec(v_cFileName_x3f_3075_);
lean_dec(v_ileanFileName_x3f_3074_);
lean_dec(v_oleanFileName_x3f_3073_);
v_a_3223_ = lean_ctor_get(v___y_3221_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___y_3221_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3225_ = v___y_3221_;
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___y_3221_);
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
v___jp_3231_:
{
if (lean_obj_tag(v_setupFileName_x3f_3072_) == 0)
{
lean_object* v___x_3237_; 
v___x_3237_ = lean_box(0);
if (lean_obj_tag(v___y_3233_) == 1)
{
lean_object* v_val_3238_; lean_object* v___x_3239_; 
v_val_3238_ = lean_ctor_get(v___y_3233_, 0);
lean_inc(v_val_3238_);
lean_dec_ref_known(v___y_3233_, 1);
v___x_3239_ = l_Lean_moduleNameOfFileName(v_val_3238_, v_rootDir_x3f_3071_);
if (lean_obj_tag(v___x_3239_) == 0)
{
v___y_3216_ = v___y_3232_;
v___y_3217_ = v___x_3237_;
v___y_3218_ = v___y_3234_;
v___y_3219_ = v___y_3235_;
v___y_3220_ = v_contents_3236_;
v___y_3221_ = v___x_3239_;
goto v___jp_3215_;
}
else
{
if (lean_obj_tag(v_oleanFileName_x3f_3073_) == 0)
{
if (lean_obj_tag(v_cFileName_x3f_3075_) == 0)
{
lean_object* v___x_3240_; 
lean_dec_ref_known(v___x_3239_, 1);
v___x_3240_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__22));
v___y_3130_ = v___y_3232_;
v___y_3131_ = v___x_3237_;
v___y_3132_ = v___y_3234_;
v___y_3133_ = v___y_3235_;
v___y_3134_ = v_contents_3236_;
v_mainModuleName_3135_ = v___x_3240_;
goto v___jp_3129_;
}
else
{
v___y_3216_ = v___y_3232_;
v___y_3217_ = v___x_3237_;
v___y_3218_ = v___y_3234_;
v___y_3219_ = v___y_3235_;
v___y_3220_ = v_contents_3236_;
v___y_3221_ = v___x_3239_;
goto v___jp_3215_;
}
}
else
{
v___y_3216_ = v___y_3232_;
v___y_3217_ = v___x_3237_;
v___y_3218_ = v___y_3234_;
v___y_3219_ = v___y_3235_;
v___y_3220_ = v_contents_3236_;
v___y_3221_ = v___x_3239_;
goto v___jp_3215_;
}
}
}
else
{
lean_object* v___x_3241_; 
lean_dec(v___y_3233_);
lean_dec(v_rootDir_x3f_3071_);
v___x_3241_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__22));
v___y_3130_ = v___y_3232_;
v___y_3131_ = v___x_3237_;
v___y_3132_ = v___y_3234_;
v___y_3133_ = v___y_3235_;
v___y_3134_ = v_contents_3236_;
v_mainModuleName_3135_ = v___x_3241_;
goto v___jp_3129_;
}
}
else
{
lean_object* v_val_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3260_; 
lean_dec(v___y_3233_);
lean_dec(v_rootDir_x3f_3071_);
v_val_3242_ = lean_ctor_get(v_setupFileName_x3f_3072_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v_setupFileName_x3f_3072_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3244_ = v_setupFileName_x3f_3072_;
v_isShared_3245_ = v_isSharedCheck_3260_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_val_3242_);
lean_dec(v_setupFileName_x3f_3072_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3260_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3246_; 
v___x_3246_ = l_Lean_ModuleSetup_load(v_val_3242_);
lean_dec(v_val_3242_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; lean_object* v_name_3248_; lean_object* v___x_3250_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3247_);
lean_dec_ref_known(v___x_3246_, 1);
v_name_3248_ = lean_ctor_get(v_a_3247_, 0);
lean_inc(v_name_3248_);
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 0, v_a_3247_);
v___x_3250_ = v___x_3244_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3247_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
v___y_3130_ = v___y_3232_;
v___y_3131_ = v___x_3250_;
v___y_3132_ = v___y_3234_;
v___y_3133_ = v___y_3235_;
v___y_3134_ = v_contents_3236_;
v_mainModuleName_3135_ = v_name_3248_;
goto v___jp_3129_;
}
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_del_object(v___x_3244_);
lean_dec_ref(v_contents_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3232_);
lean_dec_ref(v___x_3101_);
lean_dec(v_incrHeaderSaveFileName_x3f_3083_);
lean_dec(v_incrLoadFileName_x3f_3082_);
lean_dec(v_incrSaveFileName_x3f_3081_);
lean_dec_ref(v_errorOnKinds_3078_);
lean_dec(v_bcFileName_x3f_3076_);
lean_dec(v_cFileName_x3f_3075_);
lean_dec(v_ileanFileName_x3f_3074_);
lean_dec(v_oleanFileName_x3f_3073_);
v_a_3252_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3246_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3246_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
}
}
v___jp_3261_:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; uint8_t v___x_3274_; 
v___x_3270_ = lean_nat_add(v_startInclusive_3267_, v___y_3269_);
lean_dec(v___y_3269_);
lean_inc(v___x_3270_);
lean_inc_ref(v_str_3266_);
v___x_3271_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3271_, 0, v_str_3266_);
lean_ctor_set(v___x_3271_, 1, v_startInclusive_3267_);
lean_ctor_set(v___x_3271_, 2, v___x_3270_);
v___x_3272_ = l_String_Slice_trimAscii(v___x_3271_);
v___x_3273_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__25, &l___private_Lean_Shell_0__Lean_shellMain___closed__25_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__25);
v___x_3274_ = l_String_Slice_beq(v___x_3272_, v___x_3273_);
if (v___x_3274_ == 0)
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
lean_dec(v___x_3270_);
lean_dec(v_endExclusive_3268_);
lean_dec_ref(v_str_3266_);
lean_dec_ref(v___y_3265_);
lean_dec(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec_ref(v___x_3101_);
lean_dec(v_incrHeaderSaveFileName_x3f_3083_);
lean_dec(v_incrLoadFileName_x3f_3082_);
lean_dec(v_incrSaveFileName_x3f_3081_);
lean_dec_ref(v_errorOnKinds_3078_);
lean_dec(v_bcFileName_x3f_3076_);
lean_dec(v_cFileName_x3f_3075_);
lean_dec(v_ileanFileName_x3f_3074_);
lean_dec(v_oleanFileName_x3f_3073_);
lean_dec(v_setupFileName_x3f_3072_);
lean_dec(v_rootDir_x3f_3071_);
v___x_3275_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__26));
v___x_3276_ = l_String_Slice_toString(v___x_3272_);
lean_dec_ref(v___x_3272_);
v___x_3277_ = lean_string_append(v___x_3275_, v___x_3276_);
lean_dec_ref(v___x_3276_);
v___x_3278_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
v___x_3279_ = lean_string_append(v___x_3277_, v___x_3278_);
v___x_3280_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3279_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3288_; 
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3288_ == 0)
{
lean_object* v_unused_3289_; 
v_unused_3289_ = lean_ctor_get(v___x_3280_, 0);
lean_dec(v_unused_3289_);
v___x_3282_ = v___x_3280_;
v_isShared_3283_ = v_isSharedCheck_3288_;
goto v_resetjp_3281_;
}
else
{
lean_dec(v___x_3280_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3288_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3284_; lean_object* v___x_3286_; 
v___x_3284_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3283_ == 0)
{
lean_ctor_set(v___x_3282_, 0, v___x_3284_);
v___x_3286_ = v___x_3282_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v___x_3284_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
else
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
v_a_3290_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3292_ = v___x_3280_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3280_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3290_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
}
else
{
lean_object* v___x_3298_; 
lean_dec_ref(v___x_3272_);
v___x_3298_ = lean_string_utf8_extract_fast(v_str_3266_, v___x_3270_, v_endExclusive_3268_);
lean_dec(v_endExclusive_3268_);
lean_dec(v___x_3270_);
lean_dec_ref(v_str_3266_);
v___y_3232_ = v___y_3262_;
v___y_3233_ = v___y_3263_;
v___y_3234_ = v___y_3264_;
v___y_3235_ = v___y_3265_;
v_contents_3236_ = v___x_3298_;
goto v___jp_3231_;
}
}
v___jp_3299_:
{
if (lean_obj_tag(v___y_3303_) == 0)
{
lean_object* v_a_3304_; lean_object* v___x_3305_; 
v_a_3304_ = lean_ctor_get(v___y_3303_, 0);
lean_inc(v_a_3304_);
lean_dec_ref_known(v___y_3303_, 1);
v___x_3305_ = lean_decode_lossy_utf8(v_a_3304_);
lean_dec(v_a_3304_);
if (v_onlyDeps_3067_ == 0)
{
if (v_onlySrcDeps_3068_ == 0)
{
lean_object* v___x_3306_; 
lean_inc_ref(v___x_3305_);
v___x_3306_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v___x_3305_);
if (lean_obj_tag(v___x_3306_) == 1)
{
lean_object* v_val_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
lean_dec_ref(v___x_3305_);
v_val_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_val_3307_);
lean_dec_ref_known(v___x_3306_, 1);
v___x_3308_ = lean_unsigned_to_nat(0u);
v___x_3309_ = lean_box(0);
v___x_3310_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3307_, v___x_3308_, v___x_3309_);
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_object* v_str_3311_; lean_object* v_startInclusive_3312_; lean_object* v_endExclusive_3313_; lean_object* v___x_3314_; 
v_str_3311_ = lean_ctor_get(v_val_3307_, 0);
lean_inc_ref(v_str_3311_);
v_startInclusive_3312_ = lean_ctor_get(v_val_3307_, 1);
lean_inc(v_startInclusive_3312_);
v_endExclusive_3313_ = lean_ctor_get(v_val_3307_, 2);
lean_inc(v_endExclusive_3313_);
lean_dec(v_val_3307_);
v___x_3314_ = lean_nat_sub(v_endExclusive_3313_, v_startInclusive_3312_);
lean_inc_ref(v___y_3302_);
v___y_3262_ = v___y_3302_;
v___y_3263_ = v___y_3300_;
v___y_3264_ = v___y_3301_;
v___y_3265_ = v___y_3302_;
v_str_3266_ = v_str_3311_;
v_startInclusive_3267_ = v_startInclusive_3312_;
v_endExclusive_3268_ = v_endExclusive_3313_;
v___y_3269_ = v___x_3314_;
goto v___jp_3261_;
}
else
{
lean_object* v_val_3315_; lean_object* v_str_3316_; lean_object* v_startInclusive_3317_; lean_object* v_endExclusive_3318_; 
v_val_3315_ = lean_ctor_get(v___x_3310_, 0);
lean_inc(v_val_3315_);
lean_dec_ref_known(v___x_3310_, 1);
v_str_3316_ = lean_ctor_get(v_val_3307_, 0);
lean_inc_ref(v_str_3316_);
v_startInclusive_3317_ = lean_ctor_get(v_val_3307_, 1);
lean_inc(v_startInclusive_3317_);
v_endExclusive_3318_ = lean_ctor_get(v_val_3307_, 2);
lean_inc(v_endExclusive_3318_);
lean_dec(v_val_3307_);
lean_inc_ref(v___y_3302_);
v___y_3262_ = v___y_3302_;
v___y_3263_ = v___y_3300_;
v___y_3264_ = v___y_3301_;
v___y_3265_ = v___y_3302_;
v_str_3266_ = v_str_3316_;
v_startInclusive_3267_ = v_startInclusive_3317_;
v_endExclusive_3268_ = v_endExclusive_3318_;
v___y_3269_ = v_val_3315_;
goto v___jp_3261_;
}
}
else
{
lean_dec(v___x_3306_);
lean_inc_ref(v___y_3302_);
v___y_3232_ = v___y_3302_;
v___y_3233_ = v___y_3300_;
v___y_3234_ = v___y_3301_;
v___y_3235_ = v___y_3302_;
v_contents_3236_ = v___x_3305_;
goto v___jp_3231_;
}
}
else
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
lean_dec(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___x_3101_);
lean_dec(v_incrHeaderSaveFileName_x3f_3083_);
lean_dec(v_incrLoadFileName_x3f_3082_);
lean_dec(v_incrSaveFileName_x3f_3081_);
lean_dec_ref(v_errorOnKinds_3078_);
lean_dec(v_bcFileName_x3f_3076_);
lean_dec(v_cFileName_x3f_3075_);
lean_dec(v_ileanFileName_x3f_3074_);
lean_dec(v_oleanFileName_x3f_3073_);
lean_dec(v_setupFileName_x3f_3072_);
lean_dec(v_rootDir_x3f_3071_);
v___x_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3319_, 0, v___y_3302_);
v___x_3320_ = l_Lean_Elab_printImportSrcs(v___x_3305_, v___x_3319_);
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3328_; 
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3328_ == 0)
{
lean_object* v_unused_3329_; 
v_unused_3329_ = lean_ctor_get(v___x_3320_, 0);
lean_dec(v_unused_3329_);
v___x_3322_ = v___x_3320_;
v_isShared_3323_ = v_isSharedCheck_3328_;
goto v_resetjp_3321_;
}
else
{
lean_dec(v___x_3320_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3328_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3324_; lean_object* v___x_3326_; 
v___x_3324_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 0, v___x_3324_);
v___x_3326_ = v___x_3322_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3324_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
else
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
v_a_3330_ = lean_ctor_get(v___x_3320_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3320_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3320_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3335_; 
if (v_isShared_3333_ == 0)
{
v___x_3335_ = v___x_3332_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_a_3330_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
}
}
else
{
lean_object* v___x_3338_; lean_object* v___x_3339_; 
lean_dec(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___x_3101_);
lean_dec(v_incrHeaderSaveFileName_x3f_3083_);
lean_dec(v_incrLoadFileName_x3f_3082_);
lean_dec(v_incrSaveFileName_x3f_3081_);
lean_dec_ref(v_errorOnKinds_3078_);
lean_dec(v_bcFileName_x3f_3076_);
lean_dec(v_cFileName_x3f_3075_);
lean_dec(v_ileanFileName_x3f_3074_);
lean_dec(v_oleanFileName_x3f_3073_);
lean_dec(v_setupFileName_x3f_3072_);
lean_dec(v_rootDir_x3f_3071_);
v___x_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3338_, 0, v___y_3302_);
v___x_3339_ = l_Lean_Elab_printImports(v___x_3305_, v___x_3338_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3347_; 
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3347_ == 0)
{
lean_object* v_unused_3348_; 
v_unused_3348_ = lean_ctor_get(v___x_3339_, 0);
lean_dec(v_unused_3348_);
v___x_3341_ = v___x_3339_;
v_isShared_3342_ = v_isSharedCheck_3347_;
goto v_resetjp_3340_;
}
else
{
lean_dec(v___x_3339_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3347_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3343_; lean_object* v___x_3345_; 
v___x_3343_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 0, v___x_3343_);
v___x_3345_ = v___x_3341_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3343_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
else
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
v_a_3349_ = lean_ctor_get(v___x_3339_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v___x_3339_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3339_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
}
else
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3364_; 
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___x_3101_);
lean_dec(v_incrHeaderSaveFileName_x3f_3083_);
lean_dec(v_incrLoadFileName_x3f_3082_);
lean_dec(v_incrSaveFileName_x3f_3081_);
lean_dec_ref(v_errorOnKinds_3078_);
lean_dec(v_bcFileName_x3f_3076_);
lean_dec(v_cFileName_x3f_3075_);
lean_dec(v_ileanFileName_x3f_3074_);
lean_dec(v_oleanFileName_x3f_3073_);
lean_dec(v_setupFileName_x3f_3072_);
lean_dec(v_rootDir_x3f_3071_);
v_a_3357_ = lean_ctor_get(v___y_3303_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___y_3303_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3359_ = v___y_3303_;
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___y_3303_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3362_; 
if (v_isShared_3360_ == 0)
{
v___x_3362_ = v___x_3359_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3357_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
v___jp_3365_:
{
if (v_useStdin_3066_ == 0)
{
lean_object* v___x_3369_; 
v___x_3369_ = l_IO_FS_readBinFile(v_fileName_3368_);
v___y_3300_ = v___y_3366_;
v___y_3301_ = v___y_3367_;
v___y_3302_ = v_fileName_3368_;
v___y_3303_ = v___x_3369_;
goto v___jp_3299_;
}
else
{
lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3370_ = lean_get_stdin();
v___x_3371_ = l_IO_FS_Stream_readBinToEnd(v___x_3370_);
v___y_3300_ = v___y_3366_;
v___y_3301_ = v___y_3367_;
v___y_3302_ = v_fileName_3368_;
v___y_3303_ = v___x_3371_;
goto v___jp_3299_;
}
}
v___jp_3372_:
{
if (lean_obj_tag(v___y_3373_) == 1)
{
lean_object* v_val_3375_; 
v_val_3375_ = lean_ctor_get(v___y_3373_, 0);
lean_inc(v_val_3375_);
v___y_3366_ = v___y_3373_;
v___y_3367_ = v___y_3374_;
v_fileName_3368_ = v_val_3375_;
goto v___jp_3365_;
}
else
{
if (v_useStdin_3066_ == 0)
{
lean_object* v___x_3376_; lean_object* v___x_3377_; 
lean_dec(v___y_3374_);
lean_dec(v___y_3373_);
lean_dec_ref(v___x_3101_);
lean_dec(v_incrHeaderSaveFileName_x3f_3083_);
lean_dec(v_incrLoadFileName_x3f_3082_);
lean_dec(v_incrSaveFileName_x3f_3081_);
lean_dec_ref(v_errorOnKinds_3078_);
lean_dec(v_bcFileName_x3f_3076_);
lean_dec(v_cFileName_x3f_3075_);
lean_dec(v_ileanFileName_x3f_3074_);
lean_dec(v_oleanFileName_x3f_3073_);
lean_dec(v_setupFileName_x3f_3072_);
lean_dec(v_rootDir_x3f_3071_);
v___x_3376_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__27));
v___x_3377_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3376_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v___x_3378_; 
lean_dec_ref_known(v___x_3377_, 1);
v___x_3378_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_3128_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3386_; 
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3386_ == 0)
{
lean_object* v_unused_3387_; 
v_unused_3387_ = lean_ctor_get(v___x_3378_, 0);
lean_dec(v_unused_3387_);
v___x_3380_ = v___x_3378_;
v_isShared_3381_ = v_isSharedCheck_3386_;
goto v_resetjp_3379_;
}
else
{
lean_dec(v___x_3378_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3386_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3382_; lean_object* v___x_3384_; 
v___x_3382_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 0, v___x_3382_);
v___x_3384_ = v___x_3380_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3382_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
else
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
v_a_3388_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v___x_3378_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3378_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3393_; 
if (v_isShared_3391_ == 0)
{
v___x_3393_ = v___x_3390_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3388_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
else
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
v_a_3396_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3377_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3377_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
else
{
lean_object* v___x_3404_; 
v___x_3404_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__28));
v___y_3366_ = v___y_3373_;
v___y_3367_ = v___y_3374_;
v_fileName_3368_ = v___x_3404_;
goto v___jp_3365_;
}
}
}
v___jp_3405_:
{
uint8_t v___x_3408_; 
v___x_3408_ = l_List_isEmpty___redArg(v___y_3407_);
if (v___x_3408_ == 0)
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
lean_dec(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___x_3101_);
lean_dec(v_incrHeaderSaveFileName_x3f_3083_);
lean_dec(v_incrLoadFileName_x3f_3082_);
lean_dec(v_incrSaveFileName_x3f_3081_);
lean_dec_ref(v_errorOnKinds_3078_);
lean_dec(v_bcFileName_x3f_3076_);
lean_dec(v_cFileName_x3f_3075_);
lean_dec(v_ileanFileName_x3f_3074_);
lean_dec(v_oleanFileName_x3f_3073_);
lean_dec(v_setupFileName_x3f_3072_);
lean_dec(v_rootDir_x3f_3071_);
v___x_3409_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__27));
v___x_3410_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3409_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v___x_3411_; 
lean_dec_ref_known(v___x_3410_, 1);
v___x_3411_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_3128_);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3419_; 
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3419_ == 0)
{
lean_object* v_unused_3420_; 
v_unused_3420_ = lean_ctor_get(v___x_3411_, 0);
lean_dec(v_unused_3420_);
v___x_3413_ = v___x_3411_;
v_isShared_3414_ = v_isSharedCheck_3419_;
goto v_resetjp_3412_;
}
else
{
lean_dec(v___x_3411_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3419_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3415_; lean_object* v___x_3417_; 
v___x_3415_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 0, v___x_3415_);
v___x_3417_ = v___x_3413_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v___x_3415_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
else
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3428_; 
v_a_3421_ = lean_ctor_get(v___x_3411_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3423_ = v___x_3411_;
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___x_3411_);
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
else
{
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3436_; 
v_a_3429_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3431_ = v___x_3410_;
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3410_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3434_; 
if (v_isShared_3432_ == 0)
{
v___x_3434_ = v___x_3431_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_a_3429_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
}
else
{
v___y_3373_ = v___y_3406_;
v___y_3374_ = v___y_3407_;
goto v___jp_3372_;
}
}
v___jp_3437_:
{
if (v_run_3080_ == 0)
{
v___y_3406_ = v_fst_3439_;
v___y_3407_ = v_snd_3440_;
goto v___jp_3405_;
}
else
{
if (v___y_3438_ == 0)
{
v___y_3373_ = v_fst_3439_;
v___y_3374_ = v_snd_3440_;
goto v___jp_3372_;
}
else
{
v___y_3406_ = v_fst_3439_;
v___y_3407_ = v_snd_3440_;
goto v___jp_3405_;
}
}
}
v___jp_3441_:
{
if (lean_obj_tag(v_args_3032_) == 0)
{
lean_object* v___x_3443_; 
v___x_3443_ = lean_box(0);
v___y_3438_ = v___y_3442_;
v_fst_3439_ = v___x_3443_;
v_snd_3440_ = v_args_3032_;
goto v___jp_3437_;
}
else
{
lean_object* v_head_3444_; lean_object* v_tail_3445_; lean_object* v___x_3446_; 
v_head_3444_ = lean_ctor_get(v_args_3032_, 0);
lean_inc(v_head_3444_);
v_tail_3445_ = lean_ctor_get(v_args_3032_, 1);
lean_inc(v_tail_3445_);
lean_dec_ref_known(v_args_3032_, 2);
v___x_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3446_, 0, v_head_3444_);
v___y_3438_ = v___y_3442_;
v_fst_3439_ = v___x_3446_;
v_snd_3440_ = v_tail_3445_;
goto v___jp_3437_;
}
}
v___jp_3447_:
{
switch(v_component_3065_)
{
case 0:
{
lean_dec_ref(v_forwardedArgs_3064_);
if (v_onlyDeps_3067_ == 0)
{
v___y_3442_ = v_onlyDeps_3067_;
goto v___jp_3441_;
}
else
{
if (v_depsJson_3069_ == 0)
{
v___y_3442_ = v_depsJson_3069_;
goto v___jp_3441_;
}
else
{
lean_dec_ref(v___x_3101_);
lean_dec(v_incrHeaderSaveFileName_x3f_3083_);
lean_dec(v_incrLoadFileName_x3f_3082_);
lean_dec(v_incrSaveFileName_x3f_3081_);
lean_dec_ref(v_errorOnKinds_3078_);
lean_dec(v_bcFileName_x3f_3076_);
lean_dec(v_cFileName_x3f_3075_);
lean_dec(v_ileanFileName_x3f_3074_);
lean_dec(v_oleanFileName_x3f_3073_);
lean_dec(v_setupFileName_x3f_3072_);
lean_dec(v_rootDir_x3f_3071_);
if (v_useStdin_3066_ == 0)
{
lean_object* v___x_3448_; 
v___x_3448_ = lean_array_mk(v_args_3032_);
v_fns_3042_ = v___x_3448_;
goto v___jp_3041_;
}
else
{
lean_object* v___x_3449_; lean_object* v___x_3450_; 
lean_dec(v_args_3032_);
v___x_3449_ = lean_get_stdin();
v___x_3450_ = l_IO_FS_Stream_lines(v___x_3449_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v_a_3451_; 
v_a_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_a_3451_);
lean_dec_ref_known(v___x_3450_, 1);
v_fns_3042_ = v_a_3451_;
goto v___jp_3041_;
}
else
{
lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3459_; 
v_a_3452_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3454_ = v___x_3450_;
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_3450_);
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
}
}
}
case 1:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; 
lean_dec_ref(v___x_3101_);
lean_dec(v_incrHeaderSaveFileName_x3f_3083_);
lean_dec(v_incrLoadFileName_x3f_3082_);
lean_dec(v_incrSaveFileName_x3f_3081_);
lean_dec_ref(v_errorOnKinds_3078_);
lean_dec(v_bcFileName_x3f_3076_);
lean_dec(v_cFileName_x3f_3075_);
lean_dec(v_ileanFileName_x3f_3074_);
lean_dec(v_oleanFileName_x3f_3073_);
lean_dec(v_setupFileName_x3f_3072_);
lean_dec(v_rootDir_x3f_3071_);
lean_dec(v_args_3032_);
v___x_3460_ = lean_array_to_list(v_forwardedArgs_3064_);
v___x_3461_ = l_Lean_Server_Watchdog_watchdogMain(v___x_3460_);
return v___x_3461_;
}
default: 
{
lean_object* v___x_3462_; 
lean_dec(v_incrHeaderSaveFileName_x3f_3083_);
lean_dec(v_incrLoadFileName_x3f_3082_);
lean_dec(v_incrSaveFileName_x3f_3081_);
lean_dec_ref(v_errorOnKinds_3078_);
lean_dec(v_bcFileName_x3f_3076_);
lean_dec(v_cFileName_x3f_3075_);
lean_dec(v_ileanFileName_x3f_3074_);
lean_dec(v_oleanFileName_x3f_3073_);
lean_dec(v_setupFileName_x3f_3072_);
lean_dec(v_rootDir_x3f_3071_);
lean_dec_ref(v_forwardedArgs_3064_);
lean_dec(v_args_3032_);
v___x_3462_ = l_Lean_Server_FileWorker_workerMain(v___x_3101_);
return v___x_3462_;
}
}
}
v___jp_3463_:
{
lean_object* v___x_3464_; lean_object* v_timeout_3465_; lean_object* v___x_3466_; uint8_t v___x_3467_; 
v___x_3464_ = l___private_Lean_Shell_0__Lean_timeout;
v_timeout_3465_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_3101_, v___x_3464_);
v___x_3466_ = lean_unsigned_to_nat(0u);
v___x_3467_ = lean_nat_dec_eq(v_timeout_3465_, v___x_3466_);
if (v___x_3467_ == 0)
{
size_t v___x_3468_; size_t v___x_3469_; size_t v___x_3470_; lean_object* v___x_3471_; 
v___x_3468_ = lean_usize_of_nat(v_timeout_3465_);
lean_dec(v_timeout_3465_);
v___x_3469_ = ((size_t)1000ULL);
v___x_3470_ = lean_usize_mul(v___x_3468_, v___x_3469_);
v___x_3471_ = lean_internal_set_max_heartbeat(v___x_3470_);
goto v___jp_3447_;
}
else
{
lean_dec(v_timeout_3465_);
goto v___jp_3447_;
}
}
}
else
{
lean_object* v___x_3481_; 
lean_dec_ref(v_opts_3033_);
lean_dec(v_args_3032_);
v___x_3481_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; lean_object* v___x_3483_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
lean_inc(v_a_3482_);
lean_dec_ref_known(v___x_3481_, 1);
v___x_3483_ = l_Lean_getLibDir(v_a_3482_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v_a_3484_; lean_object* v___x_3485_; 
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
lean_inc(v_a_3484_);
lean_dec_ref_known(v___x_3483_, 1);
v___x_3485_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3484_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3493_; 
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3493_ == 0)
{
lean_object* v_unused_3494_; 
v_unused_3494_ = lean_ctor_get(v___x_3485_, 0);
lean_dec(v_unused_3494_);
v___x_3487_ = v___x_3485_;
v_isShared_3488_ = v_isSharedCheck_3493_;
goto v_resetjp_3486_;
}
else
{
lean_dec(v___x_3485_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3493_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3489_; lean_object* v___x_3491_; 
v___x_3489_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 0, v___x_3489_);
v___x_3491_ = v___x_3487_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v___x_3489_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
else
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3502_; 
v_a_3495_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3497_ = v___x_3485_;
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3485_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3500_; 
if (v_isShared_3498_ == 0)
{
v___x_3500_ = v___x_3497_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3495_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
else
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3510_; 
v_a_3503_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3505_ = v___x_3483_;
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3483_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3508_; 
if (v_isShared_3506_ == 0)
{
v___x_3508_ = v___x_3505_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_a_3503_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
else
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3518_; 
v_a_3511_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3513_ = v___x_3481_;
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_3481_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3516_; 
if (v_isShared_3514_ == 0)
{
v___x_3516_ = v___x_3513_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_a_3511_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
}
else
{
lean_object* v___x_3519_; 
lean_dec_ref(v_opts_3033_);
lean_dec(v_args_3032_);
v___x_3519_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; lean_object* v___x_3521_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3520_);
lean_dec_ref_known(v___x_3519_, 1);
v___x_3521_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3520_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3529_; 
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3529_ == 0)
{
lean_object* v_unused_3530_; 
v_unused_3530_ = lean_ctor_get(v___x_3521_, 0);
lean_dec(v_unused_3530_);
v___x_3523_ = v___x_3521_;
v_isShared_3524_ = v_isSharedCheck_3529_;
goto v_resetjp_3522_;
}
else
{
lean_dec(v___x_3521_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3529_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3525_; lean_object* v___x_3527_; 
v___x_3525_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3525_);
v___x_3527_ = v___x_3523_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3525_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
else
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
v_a_3531_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v___x_3521_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3521_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3531_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
v_a_3539_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3519_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3519_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
v___jp_3035_:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3036_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_3037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
return v___x_3037_;
}
v___jp_3038_:
{
uint8_t v___x_3039_; lean_object* v___x_3040_; 
v___x_3039_ = 0;
v___x_3040_ = lean_io_exit(v___x_3039_);
return v___x_3040_;
}
v___jp_3041_:
{
lean_object* v___x_3043_; 
v___x_3043_ = l_Lean_printImportsJson(v_fns_3042_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3051_; 
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3051_ == 0)
{
lean_object* v_unused_3052_; 
v_unused_3052_ = lean_ctor_get(v___x_3043_, 0);
lean_dec(v_unused_3052_);
v___x_3045_ = v___x_3043_;
v_isShared_3046_ = v_isSharedCheck_3051_;
goto v_resetjp_3044_;
}
else
{
lean_dec(v___x_3043_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3051_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3047_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v___x_3047_);
v___x_3049_ = v___x_3045_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3047_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
v_a_3053_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_3043_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3043_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object* v_args_3547_, lean_object* v_opts_3548_, lean_object* v_a_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = lean_shell_main(v_args_3547_, v_opts_3548_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(lean_object* v_val_3551_, lean_object* v_inst_3552_, lean_object* v_R_3553_, lean_object* v_a_3554_, lean_object* v_b_3555_, lean_object* v_c_3556_){
_start:
{
lean_object* v___x_3557_; 
v___x_3557_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3551_, v_a_3554_, v_b_3555_);
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___boxed(lean_object* v_val_3558_, lean_object* v_inst_3559_, lean_object* v_R_3560_, lean_object* v_a_3561_, lean_object* v_b_3562_, lean_object* v_c_3563_){
_start:
{
lean_object* v_res_3564_; 
v_res_3564_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(v_val_3558_, v_inst_3559_, v_R_3560_, v_a_3561_, v_b_3562_, v_c_3563_);
lean_dec(v_b_3562_);
lean_dec_ref(v_val_3558_);
return v_res_3564_;
}
}
lean_object* runtime_initialize_Lean_Elab_Frontend(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ParseImportsFast(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Watchdog(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_FileWorker(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_EmitC(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
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
